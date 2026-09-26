"""R3 frozen calibration procedure. Only known test currents and exact rational identities are used:
  1. mirror families: one NPN and one PNP mirror, input I0 and 2 I0, one output of area 1,
     fitted as out = g (I - offset); offsets become helper base-current trim sources, g the area trim;
     the gain is then measured again with the output held at the two other destination levels;
  2. mean cell: identities mean(u^2, v^2) = u v on five rational pairs; damped Gauss-Newton least squares
     sets the feedback ratio f, the emitter-sink ratio kappa and the loop helper trim;
  3. output mirror: as R2 (lambda=0 reference for p >= 2^n, A=B=1 reference otherwise).
No target root is evaluated here.
"""
import json, math, sys
from pathlib import Path
import numpy as np
import r3

HERE = Path(__file__).resolve().parent
BASE = dict(compensation=1e-11, startup=True, loop_area=4., darlington='pnp', loop_rc=0., base_r=20e3)
RUN = dict(duration=20e-6, dt=5e-9)

# Bench terminations at the three destination levels, derived from the on-chip replica references
# (clampl = 3 Vbe above loop ground, clampn = vee + 2 Vbe); offsets are the nominal helper Vbe differences.
LEVEL = dict(mid='0', high='clampl -0.16', low='clampn -0.055')

def mirror_bench(out_dir, kind, I, gains=None, hcomp=None, temp=25, vscale=1., model=None, n_out=1, dest='mid'):
    net = r3.NetR3(1e-5, gains=gains, hcomp=hcomp, darlington=BASE['darlington'], loop_area=BASE['loop_area'])
    net.add(f'* R3 {kind} mirror bench, destination {dest}', *r3.headers(temp=temp, vscale=vscale, **(model or {})))
    t = [f'n_{dest}{k}' for k in range(n_out)]
    if kind == 'npn':
        s = net.dac('x', f'{I*1e-5:.17g}')
        for node in t: s.sinks.append((node, 1.))
    else:
        s = r3.mod.Sig('x', 'pnp', 'n_x'); net.signals.append(s); net.add(f'Ix n_x vee {I*1e-5:.17g}')
        for node in t: s.sources.append((node, 1.))
    ref, off = (LEVEL[dest].split() + ['0'])[:2]
    net.add(f'Eterm tref 0 {ref} 0 1' if ref != '0' else 'Vterm tref 0 0', f'Vofs tlev tref {off}')
    for k, node in enumerate(t[1:], 1): net.add(f'Vt{k} {node} tlev 0')
    net.add(f'Vmeas {t[0]} tlev 0'); net.emit()
    lines = net.lines + [f'Ccomp_{j} {l.split()[2]} {l.split()[3]} {BASE["compensation"]:.17g}' for j, l in enumerate(net.lines) if l.startswith('Q') and l.split()[0][1:] in net.comp]
    r = r3.execute(lines, 'Vmeas', dict(I0=1e-5, scale=1., startup=True), out_dir, **RUN)
    if 'error' in r: raise RuntimeError(r['error'])
    return abs(r['final'])

def fit_mirrors(raw, **cond):
    """Offset and mid-level gain from I0 and 2 I0; then the gain at each other destination level."""
    gains, hcomp = {}, {}
    for kind in ['npn', 'pnp']:
        y1 = mirror_bench(raw / f'{kind}_1', kind, 1., **cond); y2 = mirror_bench(raw / f'{kind}_2', kind, 2., **cond)
        g = y2 - y1; off = 2 - y2 / g        # out = g (I - offset), I in units of I0
        hcomp[kind] = off * 1e-5; gains[kind] = dict(mid=g)
    for kind in ['npn', 'pnp']:
        for dest in ['high', 'low']:
            gains[kind][dest] = mirror_bench(raw / f'{kind}_{dest}', kind, 1., hcomp=dict(hcomp, loop=0.), **cond, dest=dest)
    return gains, hcomp

def mean(raw, A, B, cfg, **cond):
    r = r3.execute(*r3.build(kind='mean', A=A, B=B, **BASE, **cfg, **cond), raw, **RUN)
    if 'error' in r: raise RuntimeError(r['error'])
    if r['tail_pp'] > 1e-7: raise RuntimeError(f'mean cell not settled: {r["tail_pp"]}')
    return r['final']

# Exact rational identities mean(u^2, v^2) = u v. The set was chosen on the development pairs only
# (a 7-point set extended to 4 I0 was slightly worse there); ratios stay within the in-chain range.
IDENT = [(1., 1., 1.), (1., 2.25, 1.5), (2.25, 1., 1.5), (2.25, 2.25, 2.25), (.5625, .5625, .5625)]

def fit_mean(raw, cfg, iters=5, free_offsets=False, **cond):
    """Gauss-Newton least squares on log(out/uv). Unknowns: log f, kappa, loop helper trim and, optionally,
    corrections of the NPN/PNP helper trims (all in units of I0)."""
    k = 5 if free_offsets else 3
    x = np.zeros(k); x[1] = .005; x[2] = 5e-4
    def conf(x):
        h = dict(cfg['hcomp'], loop=x[2] * 1e-5)
        if free_offsets: h['npn'] = cfg['hcomp']['npn'] + x[3] * 1e-5; h['pnp'] = cfg['hcomp']['pnp'] + x[4] * 1e-5
        return dict(cfg, mean_feedback=math.exp(x[0]), kappa=x[1], hcomp=h)
    def resid(x, tag):
        c = conf(x)
        return np.array([math.log(mean(raw / f'{tag}_{j}', A, B, c, **cond) / t) for j, (A, B, t) in enumerate(IDENT)])
    rms = lambda r: float(np.sqrt((r ** 2).mean()))
    r0 = resid(x, 'it0'); hist = [dict(x=x.tolist(), residual_ppm=(r0 * 1e6).tolist(), rms=rms(r0))]
    for it in range(1, iters + 1):
        J = np.zeros((len(IDENT), k))
        for j in range(k):
            xp = x.copy(); xp[j] += 1e-4; J[:, j] = (resid(xp, f'it{it}_d{j}') - r0) / 1e-4
        step = np.linalg.lstsq(J, r0, rcond=None)[0]
        for half in range(6):   # damped step: accept only a settled, improving trial
            try:
                xt = x - step / 2 ** half; rt = resid(xt, f'it{it}_t{half}')
                if rms(rt) < rms(r0): break
            except RuntimeError: pass
        else: break
        improvement = rms(r0) - rms(rt); x, r0 = xt, rt
        hist.append(dict(x=x.tolist(), residual_ppm=(r0 * 1e6).tolist(), rms=rms(r0), damping=2 ** -half))
        if improvement < 1e-8: break
    c = conf(x)
    return dict(mean_feedback=c['mean_feedback'], kappa=float(c['kappa']), hcomp=c['hcomp'], history=hist)

def primitives(raw, **cond):
    gains, hcomp = fit_mirrors(raw / 'mirrors', **cond)
    cfg = dict(gains=gains, hcomp=dict(hcomp, loop=0.))
    m = fit_mean(raw / 'mean', cfg, **cond)
    cfg = dict(gains=gains, hcomp=m['hcomp'], kappa=m['kappa'], mean_feedback=m['mean_feedback'])
    return cfg, m['history']

def output_gain(raw, p, X, cfg, n=6, **cond):
    ref = dict(weight_override=0.) if p >= 2 ** n else dict(readout_reference=1.)
    g = 1.; hist = []
    for j in range(3):
        r = r3.execute(*r3.build(kind='root', p=p, X=X, n=n, output_gain=g, **BASE, **cfg, **ref, **cond), raw / f'cal{j}', **RUN)
        if 'error' in r: raise RuntimeError(r['error'])
        hist.append(r['final']); g *= r['scale'] / r['final']
    return g, hist

if __name__ == '__main__':
    raw = Path(sys.argv[1]) if len(sys.argv) > 1 else HERE / 'r3' / 'raw' / 'calibration'
    cfg, hist = primitives(raw)
    print(json.dumps(dict(config=cfg, history=hist), indent=1))
