"""R3 transistor netlists: same positive Padé algebra as transistor.py, new electrical primitives.

Changes against R2 (transistor.py is kept unchanged for R1/R2 reproduction):
  * every bias voltage (cascode bases, clamp references) is produced on chip by a replica
    stack of diode-connected BJTs fed by an I0-scaled bias current, so it tracks temperature
    and supply instead of being an ideal fixed voltage;
  * mirrors are cascoded on the input side as well as on every output, with one common bias:
    diode and outputs see the same Vce at every level (Early effect becomes level independent,
    and the cascode base currents cancel between input and outputs);
  * the four junctions of each translinear loop are cascoded with one common bias, which makes
    the Early factors of each up/down pair identical;
  * optional ratio trim kappa on the emitter-sharing sink (base current of the next up junction)
    and optional helper base-current compensation currents (trim sources).
Ideal elements: rails, input DAC currents, bias/bleed currents and trim currents.
"""
from pathlib import Path
import math, re, json, subprocess
import numpy as np
from transistor import mod, T, NG, ROOT

def headers(temp=25, vscale=1., vcc=4.0, vee=-2.5, ikf=.05, bf=None, vaf=None):
    vcc, vee = vcc * vscale, vee * vscale
    h = [l for l in T.header(temp=temp, vcc=vcc, vee=vee, ikf=ikf) if not l.startswith('Vb ')]
    h = [l.replace('Ikf=8m', f'Ikf={ikf}') if l.startswith('.model QP') else l for l in h]
    if bf: h = [re.sub(r' Bf=\S+', f' Bf={bf}', l) if l.startswith('.model Q') else l for l in h]
    if vaf: h = [re.sub(r' Vaf=\S+', f' Vaf={vaf}', l) if l.startswith('.model Q') else l for l in h]
    return h + ['.model DCL D(Is=1e-15 n=1 Rs=100 Cjo=5f)']

class NetR3(mod.NetT2Chain):
    def __init__(self, I0, gains=None, kappa=0., hcomp=None, bleed=.2, clamps=True, bias_ratio=2., bias_cap=10e-12, mismatch_fn=None, loop_area=1., darlington=False, bleed2=.02, loop_rc=100e3, por=None, base_r=0., loop_clamp=True):
        super().__init__(I0, gains=gains, clamps=clamps, bleed=bleed * I0)
        self.loop_area, self.darlington, self.bleed2, self.loop_rc = loop_area, darlington, bleed2 * I0, loop_rc
        self.comp = {}   # helper junction -> relative compensation weight (1 = full capacitor)
        self.por, self.base_r, self.loop_clamp = por, base_r, loop_clamp
        self.kappa = kappa; self.hcomp = hcomp or dict(npn=0., pnp=0., loop=0.)
        self.bias_ratio, self.bias_cap = bias_ratio, bias_cap
        if mismatch_fn: self.mismatch_fn = mismatch_fn
    def q(self, name, c, b, e, kind='QN', area=1.):
        if hasattr(self, 'mismatch_fn'): area = self.mismatch_fn(name, area)
        self.junctions.append(name); self.add(f'Q{name} {c} {b} {e} {kind} area={area:.17g}')
    def cb(self, name, bias, area=1.):
        """Cascode base node: isolated from the shared bias line by a series resistor scaled 1/area
        (equal drops at equal current density); a saturating cascode cannot collapse the shared line."""
        if not self.base_r: return bias
        self.add(f'Rb_{name} {bias} {name}_b {self.base_r / area:.17g}'); return f'{name}_b'
    def drive(self, name, kind, base, emitter, coll, darlington=None):
        """Beta helper driving `emitter`; Darlington option: a first stage with its own small bleed."""
        if darlington is None: darlington = self.darlington is True or self.darlington == ('pnp' if kind == 'QP' else 'npn')
        sink = (lambda node, i: f'Ibleed_{node} {node} vee {i:.17g}') if kind == 'QN' else (lambda node, i: f'Ibleed_{node} vcc {node} {i:.17g}')
        if not darlington:
            self.q(name, coll, base, emitter, kind); self.add(sink(emitter, self.bleed)); self.comp[name] = 1.; return
        y = f'{name}_y'; self.q(name, coll, base, y, kind); self.add(sink(y, self.bleed2))
        self.q(name + 'd', 'vcc' if kind == 'QN' else 'vee', y, emitter, kind); self.add(sink(emitter, self.bleed)); self.comp[name + 'd'] = 1.
    def bias(self):
        """Replica bias. Each reference is a stack of three diode-connected BJTs fed by an I0-scaled
        bias current, buffered by an emitter follower of the same polarity (so it can source/sink the
        cascode base currents): vcn = vee+2Vbe, vcp = vcc-2Vbe_p, vlc = 3Vbe above the loop ground
        (loop junctions keep one Vbe of margin against saturation), clamp references = identical replicas. Bias currents are ideal I0 multiples."""
        Ib = self.bias_ratio * self.I0
        # (node, polarity, reference, stack depth): follower output = (depth-1) Vbe from the reference
        for node, kind, ref, depth in [('vcn', 'QN', 'vee', 3), ('clampn', 'QN', 'vee', 3), ('vlc', 'QN', '0', 4),
                                       ('vcp', 'QP', 'vcc', 3), ('clampp', 'QP', 'vcc', 3)]:
            s = f'{node}_st'
            if kind == 'QN':
                self.add(f'Ibias_{node} vcc {s}{depth} {Ib:.17g}', f'Ifol_{node} {node} vee {Ib:.17g}')
                for k in range(depth, 0, -1): self.q(f'{node}_s{k}', f'{s}{k}', f'{s}{k}', f'{s}{k-1}' if k > 1 else ref, 'QN')
                self.q(f'{node}_f', 'vcc', f'{s}{depth}', node, 'QN')
            else:
                self.add(f'Ibias_{node} {s}{depth} vee {Ib:.17g}', f'Ifol_{node} vcc {node} {Ib:.17g}')
                for k in range(depth, 0, -1): self.q(f'{node}_s{k}', f'{s}{k}', f'{s}{k}', f'{s}{k-1}' if k > 1 else ref, 'QP')
                self.q(f'{node}_f', 'vee', f'{s}{depth}', node, 'QP')
            self.add(f'Cbyp_{node} {node} {ref} {self.bias_cap:.17g}')
        # Loop anti-latch reference must SINK the clamp current: PNP follower on a 2-diode NPN stack (3 Vbe).
        self.add(f'Ibias_clampl vcc clampl_st2 {Ib:.17g}', f'Ifol_clampl vcc clampl {Ib:.17g}', f'Cbyp_clampl clampl 0 {self.bias_cap:.17g}')
        self.q('clampl_s2', 'clampl_st2', 'clampl_st2', 'clampl_st1', 'QN'); self.q('clampl_s1', 'clampl_st1', 'clampl_st1', '0', 'QN')
        self.q('clampl_f', 'vee', 'clampl_st2', 'clampl', 'QP')
    def loop(self, name, ups, downs):
        n = len(ups); prev = '0'
        for k in range(n):
            a, ac, uc = f'{name}_a{k+1}', f'{name}_ac{k+1}', f'{name}_uc{k+1}'
            la = self.loop_area
            self.q(f'{name}_u{k+1}', uc, a, prev, 'QN', la); self.q(f'{name}_cu{k+1}', ac, self.cb(f'{name}_cu{k+1}', 'vlc', la), uc, 'QN', la)
            # Loop helper: single stage (NPN beta suffices) with a collector resistor. It bounds the drive
            # available to a saturated up junction, which removes the start-up latch (fb=0, out>>1).
            # A series diode shifts the injection node to 3 Vbe (cascode headroom) without adding current gain.
            hs = f'{name}_hs{k+1}'
            self.q(f'{name}_h{k+1}', f'{name}_hr{k+1}', ac, hs, 'QN'); self.q(f'{name}_hl{k+1}', hs, hs, a, 'QN'); self.comp[f'{name}_h{k+1}'] = 1.
            self.add(f'Ibleed_{a} {a} vee {self.bleed:.17g}', f'Rh_{name}_{k+1} vcc {name}_hr{k+1} {self.loop_rc:.17g}' if self.loop_rc else f'Vh_{name}_{k+1} vcc {name}_hr{k+1} 0')
            self.add(f'V{name}_inj{k+1} {ac}_in {ac} 0')
            if self.clamps and self.loop_clamp: self.add(f'Dcl_{name}_{k+1} {ac} clampl DCL')   # bounds the injection node in overload
            if self.por: self.q(f'{name}_rs{k+1}', ac, 'porb', '0', 'QN')   # power-on reset: holds the loop off
            if self.hcomp['loop']: self.add(f'Ihc_{name}_{k+1} vcc {ac} {self.hcomp["loop"]:.17g}')
            for src, r in ups[k]: src.sources.append((f'{ac}_in', r))
            if k < n - 1:
                b, dc = f'{name}_b{k+1}', f'{name}_dcc{k+1}'
                self.q(f'{name}_d{k+1}', dc, a, b, 'QN', la); self.q(f'{name}_cd{k+1}', f'{name}_dc{k+1}', self.cb(f'{name}_cd{k+1}', 'vlc', la), dc, 'QN', la)
                self.add(f'V{name}_flw{k+1} vcc {name}_dc{k+1} 0', f'V{name}_snk{k+1} {b} {b}_sk 0')
                for src, r in downs[k]: src.sinks.append((f'{b}_sk', r))
                for src, r in ups[k + 1]: src.sinks.append((f'{b}_sk', r * (1 + self.kappa)))
                prev = b
            else:
                dc = f'{name}_dcn'
                self.q(f'{name}_d{k+1}', dc, a, '0', 'QN', la); self.q(f'{name}_cd{k+1}', f'{name}_cc', self.cb(f'{name}_cd{k+1}', 'vlc', la), dc, 'QN', la)
                self.add(f'V{name}_out {name}_c {name}_cc 0')
        s = mod.Sig(name, 'pnp', f'{name}_c'); self.signals.append(s); return s
    @staticmethod
    def dest(node):
        """Destination voltage class of a mirror output (cascode Vce, hence Early-modulated alpha, differs)."""
        if node.endswith(('_in', '_pin')) or node.startswith('n_high'): return 'high'   # ~3 Vbe above loop ground
        if node.endswith(('_nin', '_s', '_k')) or node.startswith('n_low'): return 'low'  # NPN mirror input level
        return 'mid'                                                                        # loop sinks, output load
    def gain(self, kind, node):
        g = self.gains[kind]
        return g if not isinstance(g, dict) else g[self.dest(node)]
    def npn_mirror(self, name, inp, outs):
        x, ei = f'{name}_x', f'{name}_ei'
        self.drive(f'{name}_h', 'QN', inp, x, f'{name}_hc'); self.add(f'V{name}_hc vcc {name}_hc 0')
        if self.clamps: self.add(f'Dcl_{name} clampn {inp} DCL')
        if self.hcomp['npn']: self.add(f'Ihc_{name} vcc {inp} {self.hcomp["npn"]:.17g}')
        self.add(f'V{name}_in {inp} {inp}_d 0'); self.q(f'{name}_ci', f'{inp}_d', self.cb(f'{name}_ci', 'vcn'), ei, 'QN'); self.q(f'{name}_d', ei, x, 'vee', 'QN')
        for k, (node, r) in enumerate(outs):
            self.q(f'{name}_o{k}', f'{name}_e{k}', x, 'vee', 'QN', area=r / self.gain('npn', node)); self.q(f'{name}_c{k}', node, self.cb(f'{name}_c{k}', 'vcn', r), f'{name}_e{k}', 'QN', area=r)
    def pnp_mirror(self, name, inp, outs):
        x, ei = f'{name}_x', f'{name}_ei'
        self.drive(f'{name}_h', 'QP', inp, x, f'{name}_hc'); self.add(f'V{name}_hc {name}_hc vee 0')
        if self.clamps: self.add(f'Dcl_{name} {inp} clampp DCL')
        if self.hcomp['pnp']: self.add(f'Ihc_{name} {inp} vee {self.hcomp["pnp"]:.17g}')
        self.add(f'V{name}_in {inp}_d {inp} 0'); self.q(f'{name}_ci', f'{inp}_d', self.cb(f'{name}_ci', 'vcp'), ei, 'QP'); self.q(f'{name}_d', ei, x, 'vcc', 'QP')
        for k, (node, r) in enumerate(outs):
            self.q(f'{name}_o{k}', f'{name}_e{k}', x, 'vcc', 'QP', area=r / self.gain('pnp', node)); self.q(f'{name}_c{k}', node, self.cb(f'{name}_c{k}', 'vcp', r), f'{name}_e{k}', 'QP', area=r)
    def emit(self):
        self.bias(); self.npn_level = set(); self.pnp_level = set()
        if self.por:   # reset line from the controller: high until por seconds, then released (base pulled to vee)
            self.add(f'Vpor porc 0 PWL(0 1 {self.por:.17g} 1 {self.por + 20e-9:.17g} -2.5)', 'Rpor porc porb 100k')
        super().emit()

def build(kind='mean', A=1., B=2., A2=None, B2=None, p=3.7, X=2., n=6, I0=1e-5, temp=25, vscale=1., edge=10e-9,
          load=1e-12, load_R=1000., coeff_bits=24, mean_feedback=1., output_gain=1., readout_reference=None,
          weight_override=None, compensation=0., gains=None, kappa=0., hcomp=None, bleed=.2, clamps=True,
          mismatch=0., seed=1, startup=False, ramp=False, model=None, X2=None, bias_ratio=2., loop_area=1., darlington=False, bleed2=.02,
          soft_start=None, t_edge=100e-9, loop_rc=100e3, rail='b', nested='', por=None, base_r=0., loop_clamp=True):
    if not (math.isfinite(X) and X >= 1 and math.isfinite(p) and p >= 1 and isinstance(n, int) and n >= 0):
        raise ValueError('Require finite X>=1, p>=1 and integer n>=0')
    mfn = None
    if mismatch:
        import random; rng = random.Random(seed); cache = {}
        # iid synthetic area perturbations, NOT a foundry statistical mismatch model
        def mfn(name, area):
            if name not in cache: cache[name] = max(.5, 1 + rng.gauss(0, mismatch))
            return area * cache[name]
    net = NetR3(I0, gains=gains, kappa=kappa, hcomp=hcomp, bleed=bleed, clamps=clamps, bias_ratio=bias_ratio, mismatch_fn=mfn, loop_area=loop_area, darlington=darlington, bleed2=bleed2, loop_rc=loop_rc, por=por, base_r=base_r, loop_clamp=loop_clamp)
    net.add(f'* R3 {kind}', *headers(temp=temp, vscale=vscale, **(model or {})))
    def inp(name, a, b=None):
        # soft_start=(t0, tr): every DAC/reference input current ramps together from zero after the bias
        # network is up. The algebra is homogeneous of degree one, so a common ramp is a benign trajectory.
        pts = [(0., a)] if not soft_start else [(0., 0.), (soft_start[0], 0.), (soft_start[0] + soft_start[1], a)]
        if b is not None: pts += [(t_edge, a), (t_edge + edge, b)]
        if len(pts) == 1: return net.dac(name, f'{a*I0:.17g}')
        return net.dac(name, 'PWL(' + ' '.join(f'{t:.17g} {v*I0:.17g}' for t, v in pts) + ')')
    unit = inp('unit', 1.)
    def summ(name, items): return net.node(name, [(s, r) for s, r in items if r > 0], [])
    def loop(name, a, b, d): return net.loop(name, ups=[a, b], downs=[d, None])
    def mean(name, a, b, factor=1.):
        fb = mod.Sig('feedback', 'pnp', None)
        out = loop(name, [(a, factor)], [(b, 1.)], [(fb, mean_feedback)]); out.sinks.extend(fb.sinks); out.sources.extend(fb.sources)
        return out
    meta = {}
    if kind == 'mean':
        out = mean('gm', inp('a', A, A2), inp('b', B, B2)); scale = 1.
    elif kind == 'nested':
        # identity test: each input is either a DAC current or the output of mean(v, v) = v (a loop output)
        sa = mean('ina', inp('a1', A), inp('a2', A)) if 'a' in nested else inp('a', A, A2)
        sb = mean('inb', inp('b1', B), inp('b2', B)) if 'b' in nested else inp('b', B, B2)
        out = mean('gm', sa, sb); scale = 1.
    elif kind == 'product':
        out = loop('pr', [(inp('a', A, A2), 1)], [(inp('b', B, B2), 1)], [(unit, 1)]); scale = 1.
    elif kind == 'quotient':
        out = loop('qu', [(inp('a', A, A2), 1)], [(unit, 1)], [(inp('b', B, B2), 1)]); scale = 1.
    elif kind in ('root', 'rails'):
        mx, ex = math.frexp(X); mx *= 2; ex -= 1
        m2 = None if X2 is None else 2 * math.frexp(X2)[0]
        if X2 is not None and math.frexp(X2)[1] != math.frexp(X)[1]: raise ValueError('X2 must share the exponent of X')
        a = unit; b = inp('x', mx, m2); ea = 0; eb = ex; lo = 0.; hi = 1.
        for j in range(n):
            em = (ea + eb) // 2; factor = 2 ** (ea + eb - 2 * em); m = mean(f'gm{j}', a, b, factor)
            mid = (lo + hi) / 2
            if 1 / p <= mid: hi, b, eb = mid, m, em
            else: lo, a, ea = mid, m, em
        if kind == 'rails': out, scale = (b, 2. ** eb) if rail == 'b' else (a, 2. ** ea)
        else:
            weight = (1 / p - lo) / (hi - lo); weight = round(weight * 2 ** coeff_bits) / 2 ** coeff_bits
            if weight_override is not None: weight = weight_override
            b = summ('bscale', [(b, 2. ** (eb - ea))])
            if readout_reference is not None:
                ra, rb = readout_reference if isinstance(readout_reference, (tuple, list)) else (readout_reference, readout_reference)
                a = inp('cal_a', ra); b = inp('cal_b', rb)
            aa = loop('aa', [(a, 1)], [(a, 1)], [(unit, 1)]); ab = loop('ab', [(a, 1)], [(b, 1)], [(unit, 1)]); bb = loop('bb', [(b, 1)], [(b, 1)], [(unit, 1)])
            al = (weight + 1) * (weight + 2) / 12; be = (8 - 2 * weight ** 2) / 12; ga = (weight - 1) * (weight - 2) / 12
            num = summ('num', [(bb, al), (ab, be), (aa, ga)]); den = summ('den', [(bb, ga), (ab, be), (aa, al)])
            out = loop('pade', [(a, 1)], [(num, 1)], [(den, 1)]); scale = 2. ** ea; meta['weight'] = weight
    else: raise ValueError(kind)
    out.sources.append(('n_meas', output_gain)); net.add('Vmeas n_meas n_load 0', f'Rload n_load 0 {load_R:.17g}', f'Cload n_load 0 {load:.17g}'); net.emit()
    lines = net.lines
    if compensation:
        for name, wgt in net.comp.items():
            w = next(l for l in lines if l.startswith('Q' + name + ' ')).split(); lines.append(f'Ccomp_{name} {w[2]} {w[3]} {compensation * wgt:.17g}')
    if ramp:
        # line 0 is the SPICE title; rshunt (1e12 ohm to ground at every node, <0.3 ppm of I0) is a solver aid
        # needed for the all-zero initial point of a supply ramp; it is used only in this test mode.
        ramped = [lines[0], 'Venable enable 0 PWL(0 0 100n 0 1u 1)', '.options rshunt=1e12']
        for l in lines[1:]:
            w = l.split()
            if w and w[0].lower() in ('vcc', 'vee'): l = ' '.join(w[:3]) + f' PWL(0 0 100n 0 1u {w[3]})'
            elif w and w[0].startswith('I') and len(w) == 4 and not w[3].startswith(('PULSE', 'PWL')): l = 'B' + w[0] + ' ' + ' '.join(w[1:3]) + f' I=({w[3]})*v(enable)'
            ramped.append(l)
        lines = ramped
    return lines, 'Vmeas', dict(meta, scale=scale, I0=I0, transistors=len(net.junctions), kind=kind, p=p, X=X, X2=X2, n=n, A=A, B=B, A2=A2, B2=B2,
                                temp=temp, vscale=vscale, load=load, mean_feedback=mean_feedback, output_gain=output_gain, kappa=kappa, hcomp=hcomp,
                                gains=gains, bleed=bleed, compensation=compensation, readout_reference=readout_reference, weight_override=weight_override,
                                mismatch=mismatch, seed=seed, startup=startup, ramp=ramp, model=model, loop_area=loop_area, darlington=darlington, bleed2=bleed2, soft_start=soft_start, t_edge=t_edge, loop_rc=loop_rc, por=por, base_r=base_r, loop_clamp=loop_clamp)

REUSE = False

def execute(lines, sense, meta, out, duration=6e-6, dt=2e-9, window=.2, timeout=900, extra=''):
    out = Path(out); out.mkdir(parents=True, exist_ok=True)
    ctrl = ['.control', 'set noaskquit', 'set wr_singlescale', 'set wr_vecnames', 'set numdgt=17',
            f'tran {dt:.17g} {duration:.17g} 0 {dt:.17g}' + (' uic' if meta.get('startup') else ''),
            f'wrdata trace.txt i({sense}) i(vcc) i(vee) v(vcc) v(vee)', extra, 'quit', '.endc', '.end']
    text = '\n'.join(lines + ctrl) + '\n'
    # REUSE: a trace is reused only when the stored netlist is byte-identical to the one just generated.
    if REUSE and (out / 'circuit.cir').exists() and (out / 'circuit.cir').read_text() == text and (out / 'trace.txt').exists() and (out / 'trace.txt').stat().st_size > 1000: pass
    else:
        (out / 'circuit.cir').write_text(text)
        try: pr = subprocess.run([NG, '-b', 'circuit.cir'], cwd=out, capture_output=True, text=True, timeout=timeout)
        except subprocess.TimeoutExpired: return dict(meta, error=f'Solver timeout after {timeout} s')
        log = pr.stdout + pr.stderr; (out / 'ngspice.log').write_text(log)
        if pr.returncode or not (out / 'trace.txt').exists(): return dict(meta, error=log[-1500:])
    d = np.loadtxt(out / 'trace.txt', skiprows=1)
    if d.ndim != 2 or not np.isfinite(d).all(): return dict(meta, error='nonfinite trace')
    t = d[:, 0]; v = d[:, 1] / meta['I0'] * meta['scale']; tail = v[t > (1 - window) * duration]
    power = -(d[:, 2] * d[:, 4] + d[:, 3] * d[:, 5])
    return dict(meta, final=float(v[-1]), tail_min=float(tail.min()), tail_max=float(tail.max()), tail_pp=float(np.ptp(tail)),
                power_W=float(power[t > (1 - window) * duration].mean()), energy_J=float(np.trapezoid(power, t)), duration=duration, dt=dt,
                rail_accounting='vcc/vee rails; includes every ideal bias, bleed, trim and DAC current source returned through the rails')

def settle_time(trace, I0, scale, target, tol):
    """First time after which the output stays within tol of target (relative)."""
    d = np.loadtxt(trace, skiprows=1); t = d[:, 0]; v = d[:, 1] / I0 * scale
    bad = np.nonzero(np.abs(v / target - 1) > tol)[0]
    if len(bad) == 0: return float(t[0])
    if bad[-1] == len(t) - 1: return None
    return float(t[bad[-1] + 1])
