import numpy as np, mpmath as mp, time, sys, json
from multiprocessing import Pool
FAMS = ['real_gauss', 'complex_gauss', 'small_int', 'kac_pm1', 'wide_scale', 'integer_roots_mult', 'gaussian_roots_mult', 'real_cluster']
def load(name):
    P = [np.array(l.split(), float).view(complex) for l in open('fam_%s.txt' % name)]
    O = []
    for l in open('out_%s.txt' % name):
        v = l.split(); k = int(v[5]); r = np.array(v[6:], float).reshape(k, 5) if k else np.zeros((0, 5))
        O.append((int(v[0]), int(v[1]), int(v[2]), int(v[3]), int(v[4]), r))
    T = [None if l.strip() == '-' else np.array(l.split(), float).view(complex) for l in open('truth_%s.txt' % name)]
    return P, O, T
def strict(args):
    """high-precision reference: every disc must contain exactly mult*count reference roots, and all roots are covered."""
    c, r = args
    mp.mp.dps = 60
    cc = [mp.mpc(x.real, x.imag) for x in c]
    while cc and cc[0] == 0: cc = cc[1:]
    try: ref = mp.polyroots(cc, maxsteps=400, extraprec=600)
    except Exception: return 'noref'
    used = 0
    for z_re, z_im, rad, mu, cnt in r:
        z = mp.mpc(z_re, z_im); inside = sum(1 for q in ref if abs(q-z) <= mp.mpf(rad)*(1+mp.mpf(10)**-20)+mp.mpf(10)**-40*abs(z))
        if inside != int(mu)*int(cnt): return 'BAD'
        used += inside
    return 'ok' if used == len(ref) else 'BAD'
if __name__ == '__main__':
    rng = np.random.default_rng(1); summary = {}; total_bad = 0
    for name in FAMS:
        P, O, T = load(name); n = len(P); s = dict(n=n, incomplete=0, out_tol=0, degree_mismatch=0, overlap=0, truth_fail=0, numpy_mismatch=0)
        tp = np.array([o[2] for o in O])/1e3; deg = np.array([len(np.trim_zeros(p, 'f'))-1 for p in P])
        exact_used = sum(1 for o in O if o[4] > 0); esc = []; tn = []
        for i, (p, o) in enumerate(zip(P, O)):
            r = o[5]
            if not o[0]: s['incomplete'] += 1
            if not o[1]: s['out_tol'] += 1
            if int((r[:, 3]*r[:, 4]).sum()) != deg[i]: s['degree_mismatch'] += 1
            z = r[:, 0]+1j*r[:, 1]
            if len(z) > 1:
                D = np.abs(z[:, None]-z[None, :]); np.fill_diagonal(D, np.inf)
                if (D <= r[:, 2][:, None]+r[:, 2][None, :]).any(): s['overlap'] += 1
            if T[i] is not None:
                vals, cnts = np.unique(T[i], return_counts=True); ok = len(vals) == len(z)
                for v, m in zip(vals, cnts):
                    hit = np.where(np.abs(z-v) <= r[:, 2])[0]
                    ok = ok and len(hit) == 1 and int(r[hit[0], 3]) == m and int(r[hit[0], 4]) == 1
                if not ok: s['truth_fail'] += 1
            else:
                t0 = time.perf_counter(); q = np.roots(p); tn.append((time.perf_counter()-t0)*1e6)
                inside = [(np.abs(q-zz) <= rr+1e-6*abs(zz)+1e-300).sum() for zz, rr in zip(z, r[:, 2])]
                if not all(int(a) == int(b) for a, b in zip(inside, r[:, 3]*r[:, 4])): s['numpy_mismatch'] += 1; esc.append(i)
        s['median_us_pandroots'] = float(np.median(tp)); s['p99_us_pandroots'] = float(np.percentile(tp, 99)); s['max_ms_pandroots'] = float(tp.max()/1e3)
        s['beyond_double_sweeps'] = exact_used; s['median_radius_rel'] = float(np.median(np.concatenate([o[5][:, 2]/np.maximum(np.abs(o[5][:, 0]+1j*o[5][:, 1]), 1e-300) for o in O if len(o[5])])))
        if tn: s['median_us_numpy'] = float(np.median(tn))
        if T[0] is None:
            samp = sorted(set(rng.choice(n, 350, replace=False).tolist()) | set(esc[:400]))
            with Pool(2) as pool: res = pool.map(strict, [(P[i], O[i][5]) for i in samp], chunksize=8)
            s['strict_checked'] = len(samp); s['strict_ok'] = res.count('ok'); s['strict_BAD'] = res.count('BAD'); s['strict_noref'] = res.count('noref')
            s['escalated_from_numpy'] = len(esc); s['BAD_ids'] = [samp[k] for k, x in enumerate(res) if x == 'BAD'][:10]
        summary[name] = s; print(name, json.dumps(s), flush=True)
    json.dump(summary, open('summary.json', 'w'), indent=1)
