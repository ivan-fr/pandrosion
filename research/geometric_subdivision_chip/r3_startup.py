"""R3 start-up matrix with the frozen 25 C configuration (no recalibration): every run switches rails and all
sources on at t=0 from zero node voltages (uic). Settling is measured against the run's own final value,
so this file measures start-up, not accuracy. A separate supply-ramp mode is attempted and its solver
failures are kept as failures."""
import json, sys
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import numpy as np
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import r3, r3_calibrate as C

OUT = HERE / 'r3'

def job(args):
    (p, X), cond, cfg, g = args
    lab = f'startup_{p:g}_{X:g}_' + '_'.join(f'{k}{v}' for k, v in cond.items())
    kw = dict(C.BASE, **cond)
    r = r3.execute(*r3.build(kind='root', p=p, X=X, n=6, output_gain=g, **kw, **cfg), OUT / 'raw' / lab, **C.RUN)
    row = dict(p=p, X=X, condition=cond)
    if 'error' in r: return dict(row, error=r['error'][-300:], settled=False)
    d = np.loadtxt(OUT / 'raw' / lab / 'trace.txt', skiprows=1); t = d[:, 0]; v = d[:, 1] / r['I0'] * r['scale']; f = v[-1]
    st = {}
    for tol in (1e-4, 1e-5, 1e-6):
        bad = np.nonzero(np.abs(v / f - 1) > tol)[0]; st[f'{tol:g}'] = float(t[bad[-1] + 1]) if len(bad) and bad[-1] < len(t) - 1 else (None if len(bad) else 0.)
    return dict(row, final=r['final'], tail_pp=r['tail_pp'], settled=r['tail_pp'] < 1e-7, settle_to_own_final_s=st,
                peak_output=float(v.max()), peak_over_final=float(v.max() / f), power_W=r['power_W'])

if __name__ == '__main__':
    cfg = json.loads((OUT / 'calibration.json').read_text())['config']
    val = {(r['p'], r['X']): r for r in json.loads((OUT / 'root_accuracy.json').read_text())['rows']}
    cases = [(3.7, 2.), (1e6, 5e5), (13.3, 3.3), (5000.5, 777.)]
    conds = [dict(temp=t, vscale=s) for t in (-20, 25, 85) for s in (.95, 1., 1.05)] + [dict(ramp=True, temp=t) for t in (-20, 25, 85)]
    jobs = [((p, X), c, cfg, val[(p, X)]['r3']['output_gain']) for p, X in cases for c in conds]
    with ThreadPoolExecutor(8) as ex: rows = list(ex.map(job, jobs))
    for r in rows: print(r['p'], r['X'], r['condition'], r.get('settled'), r.get('settle_to_own_final_s'), r.get('error', '')[:80], flush=True)
    hard = [r for r in rows if not r['condition'].get('ramp')]; ramp = [r for r in rows if r['condition'].get('ramp')]
    summary = dict(hard_start_settled=sum(r['settled'] for r in hard), hard_start_total=len(hard),
                   ramp_settled=sum(r['settled'] for r in ramp), ramp_total=len(ramp),
                   worst_settle_1ppm_s=max((r['settle_to_own_final_s']['1e-06'] or 1e9) for r in hard if r['settled']))
    (OUT / 'startup.json').write_text(json.dumps(dict(summary=summary, rows=rows), indent=1) + '\n'); print(summary)
