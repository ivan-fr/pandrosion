"""Readout policies evaluated on stored trajectories (no new simulation).
single(T): one converted sample at time T after the job step.
avg16(T): mean of 16 samples spaced 10*tau ending at T (the noise knots are 10*tau apart)."""
import numpy as np, mpmath as mp
from v30_bridge import decode

def errors(row, case, kinds=('single', 'avg16')):
    mp.mp.dps = 60; ref = mp.exp(mp.log(mp.mpf(case['originalX'])) / case['p'])
    t = np.array(row['trajectory']['t']); q = np.array(row['trajectory']['q']); tau = row['tau_s']
    out = {}
    for kind in kinds:
        vals = []
        for i, T in enumerate(t):
            if kind == 'single':
                qq = q[i]
            else:
                idx = [np.argmin(np.abs(t - (T - k * 10 * tau))) for k in range(16)]
                if T - 15 * 10 * tau < 0: vals.append(None); continue
                qq = float(np.mean(q[idx]))
            vals.append(float(abs(mp.mpf(decode(case['c'], float(qq), case['p'])) / ref - 1)))
        out[kind] = vals
    return t.tolist(), out

def earliest(t, errs, target):
    """Earliest grid time T such that the error is <= target at T and at every later grid time."""
    ok = [e is not None and e <= target for e in errs]
    last_bad = max([i for i, v in enumerate(ok) if not v], default=-1)
    return None if last_bad + 1 >= len(t) else float(t[last_bad + 1])
