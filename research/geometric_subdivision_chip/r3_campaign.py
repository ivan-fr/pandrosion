"""R3 campaign. Order is part of the protocol:
  1. frozen calibration (known currents and exact identities only), its hash written before any scoring;
  2. validation: 4 development pairs, the 24 R2 held-out pairs (partly seen during R3 design, flagged), and
     28 fresh pairs never simulated before this run; R2 is rerun on the fresh pairs with its own procedure;
  3. stress without recalibration, then with the full calibration procedure repeated in the stressed condition;
  4. input steps in both directions and a 4x finer time step.
Every R3 simulation starts from zero (uic, all rails and sources switched on at t=0).
Run from the repository root: python research/geometric_subdivision_chip/r3_campaign.py
"""
import json, math, hashlib, sys, time
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import numpy as np
import mpmath as mp
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import r3, r3_calibrate as C
import os
r3.REUSE = os.environ.get('R3_REUSE') == '1'   # byte-identical netlists only
import transistor as R2T

OUT = HERE / 'r3'; RAW = OUT / 'raw'; OUT.mkdir(exist_ok=True)
N = 6
DEV = [(3.7, 2.), (1e6, 5e5), (3., 2.), (37.5, 5e5)]
HOLD = [(p, X) for p in [1.2, math.sqrt(2), 2.7, 7.3, 22.25, 64.1, 1200.5, 999999.75] for X in [1.3, 17., 120000.]]
SEEN = {(1.2, 1.3), (7.3, 120000.), (2.7, 17.), (1200.5, 17.)}   # R2 held-out pairs looked at while designing R3
FRESH = [(p, X) for p in [1.07, 1.9, 5.5, 13.3, 90.2, 5000.5, 250000.25] for X in [1.05, 3.3, 777., 300000.]]
WORKERS = 8

def ref(p, X):
    mp.mp.dps = 80; return mp.power(mp.mpf(str(X)), 1 / mp.mpf(str(p)))

def settle(trace, meta, target, tols=(1e-4, 1e-5, 1e-6)):
    d = np.loadtxt(trace, skiprows=1); t = d[:, 0]; v = d[:, 1] / meta['I0'] * meta['scale']; out = {}
    for tol in tols:
        bad = np.nonzero(np.abs(v / target - 1) > tol)[0]
        out[f'{tol:g}'] = None if len(bad) and bad[-1] == len(t) - 1 else float(t[bad[-1] + 1] if len(bad) else t[0])
    return out

def score(r, p, X, trace=None):
    if 'error' in r: return r
    R = ref(p, X); r = dict(r, reference=mp.nstr(R, 30))
    r['window_error'] = float(max(abs(mp.mpf(v) / R - 1) for v in (r['tail_min'], r['tail_max'])))
    r['relative_error'] = float(abs(mp.mpf(r['final']) / R - 1))
    r['excess_error'] = float(abs((mp.mpf(r['final']) - R) / (R - 1))) if R != 1 else None
    if trace: r['settle_time_s'] = settle(trace, r, float(R))
    return r

def r3_job(label, p, X, cfg, cond=None, **kw):
    cond = cond or {}
    g, hist = C.output_gain(RAW / label, p, X, cfg, n=N, **cond)
    r = r3.execute(*r3.build(kind='root', p=p, X=X, n=N, output_gain=g, **C.BASE, **cfg, **cond, **kw), RAW / label / 'run', **C.RUN)
    return dict(output_gain=g, calibration_outputs=hist, result=score(r, p, X, RAW / label / 'run' / 'trace.txt'))

def r2_job(label, p, X, r2cfg):
    """R2 procedure unchanged: frozen primitives, then its per-job output calibration, DC start, 2 us."""
    sim = lambda tag, **kw: R2T.execute(*R2T.build(**kw), RAW / 'r2' / label / tag)
    ref_kw = dict(weight_override=0.) if p >= 2 ** N else dict(readout_reference=1.); g = 1.
    for j in range(3):
        c = sim(f'cal{j}', kind='root', p=p, X=X, output_gain=g, **r2cfg, **ref_kw)
        if 'error' in c: return dict(result=c)
        g *= c['scale'] / c['final']
    return dict(output_gain=g, result=score(sim('run', kind='root', p=p, X=X, output_gain=g, **r2cfg), p, X))

def pmap(fn, items):
    with ThreadPoolExecutor(WORKERS) as ex: return list(ex.map(fn, items))

def dump(name, obj): (OUT / name).write_text(json.dumps(obj, indent=1) + '\n')

def main():
    t0 = time.time(); stages = sys.argv[1:] or ['calibration', 'validation', 'stress', 'transitions']
    if 'calibration' not in stages:   # later stages reuse the frozen file, never refit
        cal = json.loads((OUT / 'calibration.json').read_text()); cfg = cal['config']; frozen = json.dumps(cfg, sort_keys=True)
        assert hashlib.sha256(frozen.encode()).hexdigest() == cal['sha256']
    else: cfg, hist = C.primitives(RAW / 'calibration')
    if 'calibration' in stages: _calibration(cfg, hist)
    if 'validation' in stages: _validation(cfg)
    if 'stress' in stages: _stress(cfg)
    if 'transitions' in stages: _transitions(cfg)
    print('done in', round(time.time() - t0), 's')

def _calibration(cfg, hist):
    frozen = json.dumps(cfg, sort_keys=True)
    dump('calibration.json', dict(config=cfg, sha256=hashlib.sha256(frozen.encode()).hexdigest(), mean_fit=hist,
                                  base=C.BASE, identities=C.IDENT, timing=dict(run=C.RUN), written_before_scoring=True))
    print('calibration', frozen, flush=True)

def _validation(cfg):
    frozen = json.dumps(cfg, sort_keys=True)
    jobs = [('development', p, X) for p, X in DEV] + [('r2_heldout', p, X) for p, X in HOLD] + [('fresh', p, X) for p, X in FRESH]
    def v(job):
        split, p, X = job; lab = f'val_{p:.12g}_{X:.12g}'
        row = dict(split=split, p=p, X=X, seen_during_design=(p, X) in SEEN, r3=r3_job(lab, p, X, cfg))
        print(split, p, X, row['r3']['result'].get('window_error'), flush=True); return row
    rows = pmap(v, jobs)
    r2 = json.loads((HERE / 'improvement/results.json').read_text())
    old = {(j['p'], j['X']): j for j in r2['jobs']}
    for row in rows:
        j = old.get((row['p'], row['X']))
        if j: row['r1_window_error'] = j['old'].get('window_error'); row['r2_window_error'] = j['r2'].get('window_error')
    fresh_r2 = pmap(lambda job: r2_job(f'{job[1]:.12g}_{job[2]:.12g}', job[1], job[2], r2['config']), [(s, p, X) for s, p, X in jobs if s == 'fresh'])
    for row, f in zip([r for r in rows if r['split'] == 'fresh'], fresh_r2):
        row['r2_window_error'] = f['result'].get('window_error'); row['r2_rerun'] = f
    dump('root_accuracy.json', dict(config_sha256=hashlib.sha256(frozen.encode()).hexdigest(), rows=rows))

def _stress(cfg):
    cases = [DEV[0], DEV[1], FRESH[5], FRESH[18]]
    variations = [dict(temp=-20), dict(temp=85), dict(vscale=.95), dict(vscale=1.05), dict(load=1e-10),
                  dict(mismatch=.001, seed=11), dict(mismatch=.001, seed=12), dict(mismatch=.001, seed=13)]
    def s(job):
        (p, X), var = job; lab = f'stress_{p:.12g}_{X:.12g}_' + '_'.join(f'{k}{v}' for k, v in var.items())
        frozen_run = r3_job(lab + '_frozen', p, X, cfg, cond=var)
        if 'mismatch' in var:   # family benches are separate circuits: they cannot measure per-copy mismatch
            print('stress', p, X, var, frozen_run['result'].get('window_error'), flush=True)
            return dict(p=p, X=X, variation=var, frozen=frozen_run, recalibrated=dict(result=dict(error='not applicable: family calibration cannot correct per-device mismatch'), applicable=False))
        try:
            cal_cond = {k: v for k, v in var.items() if k != 'load'}
            cfg_v, _ = C.primitives(RAW / (lab + '_cal'), **cal_cond)
            recal = r3_job(lab + '_recal', p, X, cfg_v, cond=var)
        except RuntimeError as e: recal = dict(result=dict(error=str(e)[:500]))
        print('stress', p, X, var, frozen_run['result'].get('window_error'), recal['result'].get('window_error'), flush=True)
        return dict(p=p, X=X, variation=var, frozen=frozen_run, recalibrated=recal)
    dump('stress.json', pmap(s, [(c, var) for c in cases for var in variations]))

def _transitions(cfg):
    steps = [(3.7, 1.3, 1.9), (3.7, 1.9, 1.3), (1e6, 3e5, 5e5), (1e6, 5e5, 3e5), (13.3, 777., 1000.), (13.3, 1000., 777.)]
    def st(job):
        p, X1, X2, dt = job; lab = f'step_{p:.12g}_{X1:.12g}_{X2:.12g}_{dt:g}'
        g, _ = C.output_gain(RAW / lab, p, X2, cfg, n=N)
        r = r3.execute(*r3.build(kind='root', p=p, X=X1, X2=X2, n=N, output_gain=g, t_edge=10e-6, **C.BASE, **cfg), RAW / lab / 'run', duration=20e-6, dt=dt)
        r = score(r, p, X2)
        if 'error' not in r:
            d = np.loadtxt(RAW / lab / 'run' / 'trace.txt', skiprows=1); t = d[:, 0]; y = d[:, 1] / r['I0'] * r['scale']
            m = t > 10e-6; R = float(ref(p, X2)); after = {}
            for tol in (1e-4, 1e-5, 1e-6):
                bad = np.nonzero(np.abs(y[m] / R - 1) > tol)[0]
                after[f'{tol:g}'] = None if len(bad) and bad[-1] == m.sum() - 1 else float((t[m][bad[-1] + 1] if len(bad) else t[m][0]) - 10e-6)
            r['settle_after_step_s'] = after
            pre = t < 10e-6; r['before_step_error'] = float(abs(y[pre][-1] / float(ref(p, X1)) - 1))
        print('step', p, X1, X2, dt, r.get('window_error'), r.get('settle_after_step_s'), flush=True)
        return dict(p=p, X1=X1, X2=X2, dt=dt, output_gain=g, result=r)
    dump('transitions.json', pmap(st, [(p, a, b, dt) for p, a, b in steps for dt in (5e-9, 1.25e-9)]))

if __name__ == '__main__': main()
