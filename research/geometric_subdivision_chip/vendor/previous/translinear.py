"""P5 translinear current-mode netlist generator.

One-shot cube root in the reciprocal (Halley) coordinate:
    y0 = (3 I0 + Im) / 4                 seed, mirror ratios only
    y3 = y0^3 / I0^2                     6-junction up/down translinear loop
    IN = y3/2 + Im,  ID = y3 + Im/2      Kirchhoff current sums
    y1 = y0 * IN / ID                    4-junction loop  ->  cube root of Im/I0, times I0

Also: the AD state form (s -> m^-1/3, then 1/s), the direct 6-junction root loop (control)
and an optional closed-loop variant.  Mirrors are either ideal current-controlled sources
(level T1) or Wilson BJT mirrors (level T2).  Transistor models are generic assumptions for a
fast complementary bipolar process; they are not foundry data.
"""
from pathlib import Path
import shutil, subprocess, tempfile
import numpy as np

NG = shutil.which('ngspice') or '/opt/homebrew/bin/ngspice'
COUNT = 0
P = Path(__file__).parent

NPN = '.model QN NPN(Is=2e-17 Bf={bf} Br=2 Vaf={vaf} Var=5 Ikf={ikf} Rb={rb} Re={re} Rc=15 Tf={tf} Cje=15f Cjc=8f Vje=0.9 Vjc=0.7 Mje=0.4 Mjc=0.3 Xtb=1.4 Xti=3 Eg=1.1)'
PNP = '.model QP PNP(Is=2e-17 Bf={bfp} Br=2 Vaf={vafp} Var=5 Ikf=8m Rb=60 Re=2 Rc=25 Tf={tfp} Cje=20f Cjc=12f Vje=0.9 Vjc=0.7 Mje=0.4 Mjc=0.3 Xtb=1.4 Xti=3 Eg=1.1)'

class Net:
    """Accumulates netlist lines; current 'wires' are named nodes fed by sources."""
    def __init__(self, ideal_mirrors=True, mismatch=None, helper=False, bleed=20e-6):
        self.lines = []; self.n = 0; self.ideal = ideal_mirrors; self.helper = helper; self.bleed = bleed
        self.mismatch = mismatch or {}   # name -> relative Is deviation for named junctions
        self.junctions = []
    def uid(self, tag):
        self.n += 1; return f'{tag}{self.n}'
    def add(self, *ls):
        self.lines += ls
    def q(self, name, c, b, e, kind='QN', area=1.0):
        dev = self.mismatch.get(name, 0.0)
        # per-junction Is mismatch: emulate by an area factor (Is scales with area)
        self.junctions.append(name)
        self.add(f'Q{name} {c} {b} {e} {kind} area={area*(1+dev):.9g}')

    # ---- current copies -----------------------------------------------------------------
    # A "current" is represented by a 0 V sense source name; copies are made from its current.
    def sink_copy(self, src, node, ratio=1.0, tag='sk'):
        """Pull ratio*I(src) out of `node` towards VEE."""
        if self.ideal:
            self.add(f'F{self.uid(tag)} {node} vee {src} {ratio:.9g}')
        else:
            self.wilson_sink(src, node, ratio, tag)
    def source_copy(self, src, node, ratio=1.0, tag='sc'):
        """Push ratio*I(src) into `node` from VCC."""
        if self.ideal:
            self.add(f'F{self.uid(tag)} vcc {node} {src} {ratio:.9g}')
        else:
            self.wilson_source(src, node, ratio, tag)

    # ---- BJT Wilson mirrors (level T2) ---------------------------------------------------
    # The reference branch is a Wilson input fed by the current measured at `src`:
    # for a BJT-level chain, currents to be copied physically flow into the mirror inputs.
    # We keep the mirror inputs explicit: `src` is then the node name where the current arrives.
    def wilson_sink(self, src, node, ratio, tag):
        u = self.uid(tag)
        inp = self.mirror_input(src, 'sink')     # node that receives the current to be copied
        # Wilson NPN mirror: Q1 diode (out branch bottom), Q2 (input bottom), Q3 cascode on output
        self.q(f'{u}a', f'{inp}', f'{inp}', 'vee', 'QN')
        self.q(f'{u}b', f'{u}m', f'{inp}', 'vee', 'QN', area=ratio)
        self.q(f'{u}c', node, f'{u}m', 'vee', 'QN')  # placeholder; replaced below
        raise NotImplementedError
    def mirror_input(self, src, kind):
        raise NotImplementedError

    # ---- translinear loop ------------------------------------------------------------------
    def loop(self, name, ups, downs, vbias='vb', out_node=None):
        """Up/down (type B) loop: ups = list of injected currents (src names, ratio) for the
        diode-connected 'up' transistors; downs = list of forced currents for emitter followers,
        last 'down' is the loop output whose collector is `out_node`.
        len(ups) == len(downs); the last down has no forced current (it is the output).
        Returns the sense source name that carries the output current."""
        n = len(ups); assert len(downs) == n and downs[-1] is None
        prev_e = '0'
        for k in range(n):
            a = f'{name}_a{k+1}'
            # up transistor: emitter at prev_e, base=collector at a  (injection from top)
            if self.helper:
                # beta helper: the diode's base current and the follower base current are
                # supplied by an emitter follower, not taken from the injected loop current.
                ac = f'{name}_ac{k+1}'
                self.q(f'{name}_u{k+1}', ac, a, prev_e, 'QN')
                self.q(f'{name}_h{k+1}', 'vcc', ac, a, 'QN')
                if self.bleed:
                    self.add(f'Ibleed_{name}_h{k+1} {a} vee {self.bleed:.9g}')
                inj = ac
            else:
                self.q(f'{name}_u{k+1}', a, a, prev_e, 'QN')
                inj = a
            for src, ratio in ups[k]:
                self.source_copy(src, inj, ratio, tag=f'{name}i')
            if k < n - 1:
                b = f'{name}_b{k+1}'
                # down transistor k: base a, emitter b, collector at bias rail (matched Vce ~ Vbe)
                self.q(f'{name}_d{k+1}', vbias, a, b, 'QN')
                # sink at b: forced current of d_k plus the emitter current of u_{k+1}
                for src, ratio in downs[k]:
                    self.sink_copy(src, b, ratio, tag=f'{name}s')
                for src, ratio in ups[k + 1]:
                    self.sink_copy(src, b, ratio, tag=f'{name}s')
                prev_e = b
            else:
                sense = f'V{name}_out'
                cnode = out_node or f'{name}_c'
                self.q(f'{name}_d{k+1}', cnode, a, '0', 'QN')
                # output current measured through a 0 V source into a Vce-matching node
                self.add(f'{sense} {vbias} {cnode} 0')
        return sense

def header(temp=27, bf=400, vaf=100, tf=25e-12, re=1.5, rb=40, ikf=8e-3, bfp=100, vafp=60, tfp=60e-12, vcc=2.5, vee=-2.5, vb=0.85):
    return [
        f'.options reltol=1e-6 abstol=1e-13 vntol=1e-8 chgtol=1e-16 gmin=1e-15 method=gear',
        f'.temp {temp}',
        NPN.format(bf=bf, vaf=vaf, tf=tf, re=re, rb=rb, ikf=ikf), PNP.format(bfp=bfp, vafp=vafp, tfp=tfp),
        f'Vcc vcc 0 {vcc}', f'Vee vee 0 {vee}', 
        f'Vb vb 0 {vb}',   # collector rail of follower transistors: keeps Vce close to a diode drop
    ]

def build(kind='halley', I0=100e-6, m_source='dc', m=1.5, m2=2.0, tstep=0.0, ideal_mirrors=True,
          mismatch=None, helper=False, bleed=None, edge=1e-9, **hp):
    """kind: 'halley' (y form one-shot), 'ad' (s form one-shot + reciprocal), 'direct' (6-junction root)."""
    bleed = 0.2 * I0 if bleed is None else bleed   # helper bias scales with the unit current
    net = Net(ideal_mirrors, mismatch, helper, bleed)
    hp.setdefault('vb', 1.65 if helper else 0.85)   # follower collectors: Vce matched to the diode side
    net.add(f'* Pandrosion P5 translinear one-shot cube root, kind={kind}, helper={helper}', *header(**hp))
    # unit current I0 and input Im, both measured by 0 V sense sources (ideal references)
    net.add(f'Iunit vcc n_i0 {I0:.9g}', f'Vi0 n_i0 vee 0')
    if m_source == 'dc':
        net.add(f'Iin vcc n_im {I0*m:.9g}')
    else:  # step m -> m2 at tstep with 100 ps edges
        net.add(f'Iin vcc n_im PULSE({I0*m:.9g} {I0*m2:.9g} {tstep:.9g} {edge:.9g} {edge:.9g} 1 2)')
    net.add('Vim n_im vee 0')
    I0s, Ims = 'Vi0', 'Vim'
    if kind == 'halley':
        # seed y0 = (3 I0 + Im)/4 : realized by two copies into a sense branch
        net.add('Vseed n_seed vee 0')
        net.source_copy(I0s, 'n_seed', 0.75, tag='seed'); net.source_copy(Ims, 'n_seed', 0.25, tag='seed')
        y0 = 'Vseed'
        # cube loop: ups y0,y0,y0 ; downs I0, I0, out
        y3 = net.loop('cube', ups=[[(y0, 1)], [(y0, 1)], [(y0, 1)]], downs=[[(I0s, 1)], [(I0s, 1)], None])
        # numerator / denominator currents as sums (each needed twice: injection and sink)
        # update loop: ups y0, IN ; downs ID, out   (IN = y3/2 + Im, ID = y3 + Im/2)
        y1 = net.loop('upd', ups=[[(y0, 1)], [(y3, 0.5), (Ims, 1)]], downs=[[(y3, 1), (Ims, 0.5)], None])
        out = y1
    elif kind == 'ad':
        # AD state form: s0 = (5 I0 - Im)/4 is not mirror-friendly (needs subtraction);
        # use s0 = 1.25 I0 - 0.25 Im realized as source 1.25 I0 and sink 0.25 Im on the seed node.
        net.add('Vseed n_seed vee 0')
        net.source_copy(I0s, 'n_seed', 1.25, tag='seed'); net.sink_copy(Ims, 'n_seed', 0.25, tag='seed')
        s0 = 'Vseed'
        # t = m s^3 : ups s0,s0,s0,Im ; downs I0,I0,I0,out
        t = net.loop('tloop', ups=[[(s0, 1)], [(s0, 1)], [(s0, 1)], [(Ims, 1)]], downs=[[(I0s, 1)], [(I0s, 1)], [(I0s, 1)], None])
        # s1 = s0 (1 + t/2)/(1/2 + t): ups s0, N=(I0 + t/2) ; downs D=(I0/2 + t), out
        s1 = net.loop('upd', ups=[[(s0, 1)], [(I0s, 1), (t, 0.5)]], downs=[[(I0s, 0.5), (t, 1)], None])
        # y = I0^2 / s1 : ups I0, I0 ; downs s1, out
        out = net.loop('inv', ups=[[(I0s, 1)], [(I0s, 1)]], downs=[[(s1, 1)], None])
    elif kind == 'direct':
        # direct translinear root: ups Im, I0, I0 ; downs y, y, out=y  (feedback copies of the output)
        out = 'Vroot_out'
        net.loop('root', ups=[[(Ims, 1)], [(I0s, 1)], [(I0s, 1)]], downs=[[(out, 1)], [(out, 1)], None])
    else:
        raise ValueError(kind)
    return net, out

def control_block(out_sense, analysis, extra_vars=()):
    names = ' '.join(['i(%s)' % out_sense] + list(extra_vars))
    return ['.control', 'set noaskquit', 'set wr_singlescale', 'set wr_vecnames', 'set numdgt=15',
            analysis, f'wrdata waveform.txt {names}', 'quit', '.endc', '.end']

def execute(text, keep=None, timeout=120):
    global COUNT
    with tempfile.TemporaryDirectory(prefix='pandro_p5_') as t:
        d = Path(t); (d / 'test.cir').write_text(text)
        p = subprocess.run([NG, '-b', 'test.cir'], cwd=d, capture_output=True, text=True, timeout=timeout)
        ok = p.returncode == 0 and (d / 'waveform.txt').exists()
        if not ok:
            raise RuntimeError((p.stdout + p.stderr)[-4000:])
        a = np.loadtxt(d / 'waveform.txt', skiprows=1)
        if keep:
            (P / f'{keep}.cir').write_text(text); (P / f'{keep}.log').write_text(p.stdout + p.stderr)
        COUNT += 1
    assert np.isfinite(a).all()
    return a


# ======================================================================================
# Level T2: every current copy is a BJT mirror (helper + cascode), only the unit bias I0
# and the input Im are ideal current sources; rails vcc=4 V, vee=-2.5 V, cascode biases
# are ideal voltage sources.  Only the reciprocal (Halley) one-shot is built at this level.
# ======================================================================================
class NetT2(Net):
    def __init__(self, mismatch=None, helper=True, bleed=20e-6):
        super().__init__(ideal_mirrors=False, mismatch=mismatch, helper=helper, bleed=bleed)
    def npn_mirror(self, name, inp, outs):
        """Sink mirror: current arriving at node `inp` is copied (ratio) as currents pulled from nodes."""
        x = f'{name}_x'
        self.q(f'{name}_h', 'vcc', inp, x, 'QN')
        if self.bleed: self.add(f'Ibleed_{name} {x} vee {self.bleed:.9g}')
        self.q(f'{name}_d', inp, x, 'vee', 'QN')
        for k, (node, r) in enumerate(outs):
            e = f'{name}_e{k}'
            self.q(f'{name}_o{k}', e, x, 'vee', 'QN', area=r)
            self.q(f'{name}_c{k}', node, 'vcn', e, 'QN', area=r)
    def pnp_mirror(self, name, inp, outs):
        """Source mirror: current pulled out of node `inp` is copied as currents pushed into nodes."""
        x = f'{name}_x'
        self.q(f'{name}_h', 'vee', inp, x, 'QP')
        if self.bleed: self.add(f'Ibleed_{name} vcc {x} {self.bleed:.9g}')
        self.q(f'{name}_d', inp, x, 'vcc', 'QP')
        for k, (node, r) in enumerate(outs):
            e = f'{name}_e{k}'
            self.q(f'{name}_o{k}', e, x, 'vcc', 'QP', area=r)
            self.q(f'{name}_c{k}', node, 'vcp', e, 'QP', area=r)

def build_t2(I0=100e-6, m_source='dc', m=1.5, m2=2.0, tstep=0.0, mismatch=None, vcc=4.0, vee=-2.5, bleed=None, edge=1e-9, **hp):
    bleed = 0.2 * I0 if bleed is None else bleed
    net = NetT2(mismatch, helper=True, bleed=bleed)
    hp.setdefault('vb', 1.65)
    net.add('* Pandrosion P5 level T2: translinear one-shot cube root with BJT mirrors',
            *header(vcc=vcc, vee=vee, **hp), f'Vcn vcn 0 {vee + 2.4}', f'Vcp vcp 0 {vcc - 2.4}')
    # ideal bias and input
    if m_source == 'dc':
        net.add(f'Iin vcc n_im {I0*m:.9g}')
    else:
        net.add(f'Iin vcc n_im PULSE({I0*m:.9g} {I0*m2:.9g} {tstep:.9g} {edge:.9g} {edge:.9g} 1 2)')
    net.add(f'Iseed0 vcc n_seed {0.75*I0:.9g}', f'Ib1 cube_b1 vee {I0:.9g}', f'Ib2 cube_b2 vee {I0:.9g}')
    # input current copies: sinks 1.5 Im at upd_b1 and 1.25 Im into the PNP mirror input;
    # sources 0.25 Im (seed) and 1 Im (update numerator injection)
    net.npn_mirror('mim', 'n_im', [('upd_b1', 1.5), ('n_pim', 1.25)])
    net.pnp_mirror('mip', 'n_pim', [('n_seed', 0.2), ('upd_ac2', 0.8)])   # input carries 1.25 Im
    # seed y0 = 0.75 I0 + 0.25 Im arrives at n_seed: sinks for the cube loop and a 4x copy to the PNP side
    net.npn_mirror('my0', 'n_seed', [('cube_b1', 1.0), ('cube_b2', 1.0), ('n_py0', 4.0)])
    net.pnp_mirror('my0p', 'n_py0', [('cube_ac1', 0.25), ('cube_ac2', 0.25), ('cube_ac3', 0.25), ('upd_ac1', 0.25)])   # input carries 4 y0
    # cube loop (helper form): transistors only, currents come from the mirrors above
    for k, (prev, a) in enumerate([('0', 'cube_a1'), ('cube_b1', 'cube_a2'), ('cube_b2', 'cube_a3')]):
        net.q(f'cube_u{k+1}', f'cube_ac{k+1}', a, prev, 'QN'); net.q(f'cube_h{k+1}', 'vcc', f'cube_ac{k+1}', a, 'QN')
    net.q('cube_d1', 'vb', 'cube_a1', 'cube_b1', 'QN'); net.q('cube_d2', 'vb', 'cube_a2', 'cube_b2', 'QN')
    net.q('cube_d3', 'cube_c', 'cube_a3', '0', 'QN')
    # y3 is pulled from cube_c by the PNP mirror: 0.5 y3 into the update injection, 1.5 y3 to an NPN sink copy
    net.pnp_mirror('my3p', 'cube_c', [('upd_ac2', 0.5), ('n_ny3', 1.5)])
    net.npn_mirror('my3n', 'n_ny3', [('upd_b1', 1.0)])
    # update loop: ups y0 (ac1), IN = 0.5 y3 + Im (ac2); downs ID = y3 + 0.5 Im (sink 1.5 y3 + 1.5 Im at b1 minus IN), out
    net.q('upd_u1', 'upd_ac1', 'upd_a1', '0', 'QN'); net.q('upd_h1', 'vcc', 'upd_ac1', 'upd_a1', 'QN')
    net.q('upd_d1', 'vb', 'upd_a1', 'upd_b1', 'QN')
    net.q('upd_u2', 'upd_ac2', 'upd_a2', 'upd_b1', 'QN'); net.q('upd_h2', 'vcc', 'upd_ac2', 'upd_a2', 'QN')
    net.q('upd_d2', 'upd_c', 'upd_a2', '0', 'QN')
    net.add('Vupd_out vb upd_c 0')
    return net, 'Vupd_out'
