"""Level T2 for the centered chain: every current copy is a BJT mirror (helper-assisted, no cascode:
all mirror outputs see constant node voltages, so Early effects are fixed ratios absorbed by trims).
Ideal elements that remain: the unit bias I0 (bias generator), the two DAC input currents (Y, q0),
the constant trim bias currents, rails +2.5/-2.5 V.  Programmed weights are mirror area ratios.

Two-pass construction: the chain is first described as signals with copy demands, then each signal
receives one NPN mirror (Kirchhoff-sum nodes, DAC inputs) or one PNP mirror (loop outputs), plus a
secondary mirror of the other polarity when both sink and source copies are required.
"""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'pandrosion_analog_p5'))
import translinear as T                      # noqa: E402
from v30_bridge import schedule              # noqa: E402

class Sig:
    def __init__(self, name, kind, node):
        self.name, self.kind, self.node = name, kind, node; self.sinks = []; self.sources = []

class NetT2Chain(T.Net):
    def __init__(self, I0, mismatch=None, bleed=None, gains=None, clamps=True, cascodes=True, style='helper'):
        super().__init__(ideal_mirrors=False, mismatch=mismatch, helper=True, bleed=0.2 * I0 if bleed is None else bleed)
        self.clamps, self.cascodes, self.style = clamps, cascodes, style
        self.I0 = I0; self.signals = []; self.ideal_count = 0
        # measured copy gains per output type (npn plain / npn cascoded / pnp plain / pnp cascoded); ratios are
        # pre-compensated by 1/gain: the programmable-ratio trim of a real chip, fitted with test currents
        self.gains = gains or dict(npn=1.0, npnc=1.0, pnp=1.0, pnpc=1.0)
    # ---- symbolic pass -------------------------------------------------------------------------
    def ideal_sig(self, name):
        s = Sig(name, 'ideal', None); self.signals.append(s); return s
    def dac(self, name, current):
        s = Sig(name, 'npn', f'n_{name}'); self.add(f'I{name} vcc n_{name} {current}'); self.signals.append(s); return s
    def node(self, name, sources, sinks):
        s = Sig(name, 'npn', f'n_{name}')
        # 0 V senses on the summed source and sink branches of every Kirchhoff node
        self.add(f'V{name}_srcs n_{name}_s n_{name} 0', f'V{name}_snks n_{name} n_{name}_k 0')
        for src, r in sources: src.sources.append((f'n_{name}_s', r))
        for src, r in sinks: src.sinks.append((f'n_{name}_k', r))
        self.signals.append(s); return s
    def loop(self, name, ups, downs):
        n = len(ups); prev_e = '0'
        for k in range(n):
            a, ac = f'{name}_a{k+1}', f'{name}_ac{k+1}'
            self.q(f'{name}_u{k+1}', ac, a, prev_e, 'QN'); self.q(f'{name}_h{k+1}', 'vcc', ac, a, 'QN')
            self.add(f'Ibleed_{name}_h{k+1} {a} vee {self.bleed:.9g}', f'V{name}_inj{k+1} {ac}_in {ac} 0')   # 0 V sense on the injection
            for src, r in ups[k]: src.sources.append((f'{ac}_in', r))
            if k < n - 1:
                b = f'{name}_b{k+1}'; self.q(f'{name}_d{k+1}', f'{name}_dc{k+1}', a, b, 'QN'); self.add(f'V{name}_flw{k+1} vb {name}_dc{k+1} 0', f'V{name}_snk{k+1} {b} {b}_sk 0')
                for src, r in downs[k]: src.sinks.append((f'{b}_sk', r))
                for src, r in ups[k + 1]: src.sinks.append((f'{b}_sk', r))
                prev_e = b
            else:
                self.q(f'{name}_d{k+1}', f'{name}_cc', a, '0', 'QN'); self.add(f'V{name}_out {name}_c {name}_cc 0')   # sense on the loop output
        s = Sig(name, 'pnp', f'{name}_c'); self.signals.append(s); return s
    # ---- emission pass -------------------------------------------------------------------------
    # Mirror outputs whose collector node sits at the mirror-input level (two diode drops from the rail)
    # match the diode's Vce and need no cascode; every other output gets a cascode biased so that the
    # output transistor also sees two diode drops (Early effect then cancels as a fixed ratio).
    def npn_mirror(self, name, inp, outs):
        if self.style == 'plain':   # diode-connected input, simple outputs (beta and Early errors folded into the measured gain)
            self.add(f'V{name}_in {inp} {inp}_d 0'); self.q(f'{name}_d', f'{inp}_d', inp, 'vee', 'QN')
            for k, (node, r) in enumerate(outs): self.q(f'{name}_o{k}', node, inp, 'vee', 'QN', area=r / self.gains['npn'])
            return
        x = f'{name}_x'; self.q(f'{name}_h', f'{name}_hc', inp, x, 'QN'); self.add(f'V{name}_hc vcc {name}_hc 0', f'Ibleed_{name} {x} vee {self.bleed:.9g}')
        if self.clamps: self.add(f'Dcl_{name} clampn {inp} DCL')   # anti-saturation clamp: supplies any transient excess sink current
        self.add(f'V{name}_in {inp} {inp}_d 0'); self.q(f'{name}_d', f'{inp}_d', x, 'vee', 'QN')   # 0 V sense on the input branch
        for k, (node, r) in enumerate(outs):
            if node in self.npn_level or not self.cascodes: self.q(f'{name}_o{k}', node, x, 'vee', 'QN', area=r / self.gains['npn'])
            else: self.q(f'{name}_o{k}', f'{name}_e{k}', x, 'vee', 'QN', area=r / self.gains['npnc']); self.q(f'{name}_c{k}', node, 'vcn', f'{name}_e{k}', 'QN', area=r)
    def pnp_mirror(self, name, inp, outs):
        if self.style == 'plain':
            self.add(f'V{name}_in {inp}_d {inp} 0'); self.q(f'{name}_d', f'{inp}_d', inp, 'vcc', 'QP')
            for k, (node, r) in enumerate(outs): self.q(f'{name}_o{k}', node, inp, 'vcc', 'QP', area=r / self.gains['pnp'])
            return
        x = f'{name}_x'; self.q(f'{name}_h', f'{name}_hc', inp, x, 'QP'); self.add(f'V{name}_hc {name}_hc vee 0', f'Ibleed_{name} vcc {x} {self.bleed:.9g}')
        if self.clamps: self.add(f'Dcl_{name} {inp} clampp DCL')
        self.add(f'V{name}_in {inp}_d {inp} 0'); self.q(f'{name}_d', f'{inp}_d', x, 'vcc', 'QP')
        for k, (node, r) in enumerate(outs):
            if node in self.pnp_level or not self.cascodes: self.q(f'{name}_o{k}', node, x, 'vcc', 'QP', area=r / self.gains['pnp'])
            else: self.q(f'{name}_o{k}', f'{name}_e{k}', x, 'vcc', 'QP', area=r / self.gains['pnpc']); self.q(f'{name}_c{k}', node, 'vcp', f'{name}_e{k}', 'QP', area=r)
    def emit(self):
        self.npn_level = {s.node for s in self.signals if s.kind == 'npn'} | {f'{s.node}_k' for s in self.signals if s.kind == 'npn'} | {f'{s.node}_s' for s in self.signals if s.kind == 'npn'} | {f'{s.name}_nin' for s in self.signals if s.kind == 'pnp'} | {'n_meas'}
        self.pnp_level = {s.node for s in self.signals if s.kind == 'pnp'} | {f'{s.name}_pin' for s in self.signals if s.kind == 'npn'}
        for s in self.signals:
            if s.kind == 'ideal':
                for node, r in s.sources: self.ideal_count += 1; self.add(f'Iideal{self.ideal_count} vcc {node} {r*self.I0:.9g}')
                for node, r in s.sinks: self.ideal_count += 1; self.add(f'Iideal{self.ideal_count} {node} vee {r*self.I0:.9g}')
            elif s.kind == 'npn':
                outs = list(s.sinks)
                if s.sources:
                    tot = sum(r for _, r in s.sources); pin = f'{s.name}_pin'; outs.append((pin, tot))
                    self.pnp_mirror(f'mp_{s.name}', pin, [(n, r / tot) for n, r in s.sources])   # secondary mirror carries tot*I
                self.npn_mirror(f'mn_{s.name}', s.node, outs)   # an unused signal keeps its input diode as load
            elif s.kind == 'pnp':
                outs = list(s.sources)
                if s.sinks:
                    tot = sum(r for _, r in s.sinks); nin = f'{s.name}_nin'; outs.append((nin, tot))
                    self.npn_mirror(f'mn_{s.name}', nin, [(n, r / tot) for n, r in s.sinks])
                self.pnp_mirror(f'mp_{s.name}', s.node, outs)

def headers(vcc=4.0, vee=-2.5, ikfp=50e-3, **hp):
    hp.setdefault('vb', 1.65)
    hdr = [l.replace('Ikf=8m', f'Ikf={ikfp}') if l.startswith('.model QP') else l for l in T.header(vcc=vcc, vee=vee, **hp)]
    return hdr + [f'Vcn vcn 0 {vee + 2.4:.4g}', f'Vcp vcp 0 {vcc - 2.4:.4g}',   # cascode biases: ideal voltage sources
                  '.model DCL D(Is=1e-15 n=1 Cjo=5f)', f'Vclampn clampn 0 {vee + 1.7:.4g}', f'Vclampp clampp 0 {vcc - 1.7:.4g}']

def mirror_gains(I0=100e-6, level=0.5, vcc=4.0, vee=-2.5, **hp):
    """Measure the four copy types with a test current (level*I0): one mirror, one output each."""
    out = {}
    for kind in ['npn', 'npnc', 'pnp', 'pnpc']:
        net = NetT2Chain(I0); net.add('* mirror gain test', *headers(vcc=vcc, vee=vee, **hp)); I = level * I0
        if kind.startswith('npn'):
            net.add(f'Ix vcc n_x {I:.9g}'); net.npn_level = {'n_t'} if kind == 'npn' else set()
            net.npn_mirror('m', 'n_x', [('n_t', 1.0)]); net.add(f'Vtref tref 0 {(vee + 1.6 if kind == "npn" else 0.0):.4g}', 'Vmeas tref n_t 0')
        else:
            net.add(f'Ix c_in vee {I:.9g}'); net.pnp_level = {'n_t'} if kind == 'pnp' else set()
            net.pnp_mirror('m', 'c_in', [('n_t', 1.0)]); net.add(f'Vtref tref 0 {(vcc - 1.6 if kind == "pnp" else vee + 1.6):.4g}', 'Vmeas n_t tref 0')
        a = T.execute('\n'.join(net.lines + T.control_block('Vmeas', 'tran 20p 30n 0 20p uic')), timeout=120)
        out[kind] = float(a[-1, 1] / I)
    return out

def build_chain3(p, Y, q0=0.0, I0=100e-6, m_source='dc', Y2=None, q02=None, tstep=1e-9, edge=1e-9, mismatch=None, trims=None,
                 keep=0.1, vcc=4.0, vee=-2.5, ikfp=50e-3, gains=None, clamps=True, cascodes=True, style='helper', **hp):
    trims = trims or {}
    net = NetT2Chain(I0, mismatch, gains=gains, clamps=clamps, cascodes=cascodes, style=style); hp.setdefault('vb', 1.65)
    if style == 'plain': hp['vb'] = 0.85   # plain-mirror input nodes sit one diode drop from the rails
    net.add(f'* Pandrosion P6 translinear centered chain, level T2 (BJT mirrors), p={p}', *headers(vcc=vcc, vee=vee, ikfp=ikfp, **hp))
    I0s = net.ideal_sig('I0')
    def cur(v, v2):
        return f'{v*I0:.9g}' if m_source == 'dc' else f'PULSE({v*I0:.9g} {v2*I0:.9g} {tstep:.9g} {edge:.9g} {edge:.9g} 1 2)'
    Ys = net.dac('y', cur(Y, Y2 if Y2 is not None else Y)); vq = net.dac('vq', cur(1 + q0, 1 + (q02 if q02 is not None else q0)))
    def loop(name, ups, downs):
        raw = net.loop(name, ups, downs); tr = trims.get(name)
        if not tr: return raw
        b = tr['o'] / tr['k']
        return net.node(f'{name}t', [(raw, 1 / tr['k'])] + ([(I0s, -b)] if b < 0 else []), [(I0s, b)] if b >= 0 else [])
    eq = net.node('eq', [(I0s, 1)], [(vq, 1)]); eqk = net.node('eqk', [(I0s, 1 + keep)], [(vq, 1)])
    v = vq; ek = eqk
    for i, op in enumerate(schedule(p)):
        w = op['product_weight']
        if op['kind'] == 'square':
            sq = loop(f'sq{i}', [[(ek, 1)], [(ek, 1)]], [[(I0s, 1)], None])
            v = net.node(f'v{i}', [(v, 1), (sq, w), (I0s, w * keep ** 2)], [(ek, 2 * w * keep)])
        else:
            # v_{n+1} = n/(n+1) v_n + 1/(n+1) v_q + w' e_n e_q : same algebra as V30, written without a difference node
            cw = op['copy_weight']
            pr = loop(f'pr{i}', [[(ek, 1)], [(eqk, 1)]], [[(I0s, 1)], None])
            v = net.node(f'v{i}', [(v, 1 - cw), (vq, cw), (pr, w), (I0s, w * keep ** 2)], [(ek, w * keep), (eqk, w * keep)])
        ek = net.node(f'ek{i}', [(I0s, 1 + keep)], [(v, 1)])
    t = loop('res', [[(Ys, 1)], [(v, 1)]], [[(I0s, 1)], None])
    D = net.node('D', [(I0s, 1 - 1 / p), (t, 1 + 1 / p)], [])
    Pp = loop('P', [[(I0s, 1), (eq, 1)], [(t, 1)]], [[(I0s, 1)], None])
    Np = net.node('N', [(I0s, 3 - 1 / p)], [(eq, 1 + 1 / p), (Pp, 1 - 1 / p)])
    out = loop('upd', [[(Np, 1)], [(I0s, 1)]], [[(D, 1)], None])
    # measurement: one source copy of the output into a node held at the NPN-input level (-0.9 V)
    out.sources.append(('n_meas', 1.0)); net.add(f'Vmref mref 0 {(vee + 0.8) if style == "plain" else (vee + 1.6):.4g}', 'Vmeas n_meas mref 0')
    net.emit()
    return net, 'Vmeas'


def cell_t2(kind, x, y, I0=100e-6, gains=None, **hp):
    """Isolated T2 cell: DAC inputs through mirrors, one loop, PNP output copy into the measurement node."""
    net = NetT2Chain(I0, gains=gains); net.add('* T2 cell', *headers(**hp))
    I0s = net.ideal_sig('I0'); xs = net.dac('x', f'{x*I0:.9g}'); ys = net.dac('y', f'{y*I0:.9g}')
    if kind == 'sq': out = net.loop('L', [[(xs, 1)], [(xs, 1)]], [[(I0s, 1)], None]); ideal = x * x
    elif kind in ('pr', 'res', 'P'): out = net.loop('L', [[(xs, 1)], [(ys, 1)]], [[(I0s, 1)], None]); ideal = x * y
    elif kind == 'upd': out = net.loop('L', [[(xs, 1)], [(I0s, 1)]], [[(ys, 1)], None]); ideal = x / y
    out.sources.append(('n_meas', 1.0)); net.add(f'Vmref mref 0 {hp.get("vee", -2.5) + 1.6:.4g}', 'Vmeas n_meas mref 0'); net.emit()
    a = T.execute('\n'.join(net.lines + T.control_block('Vmeas', 'tran 20p 30n 0 20p uic')), timeout=120)
    return float(a[-1, 1] / I0), ideal
