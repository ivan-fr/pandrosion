import numpy as np
from multiprocessing import Pool
from verify import load, strict
if __name__ == '__main__':
    for name in ['wide_scale', 'real_cluster', 'kac_pm1']:
        P, O, T = load(name); esc = []
        for i, (p, o) in enumerate(zip(P, O)):
            r = o[5]; z = r[:, 0]+1j*r[:, 1]; q = np.roots(p)
            inside = [(np.abs(q-zz) <= rr+1e-6*abs(zz)+1e-300).sum() for zz, rr in zip(z, r[:, 2])]
            if not all(int(a) == int(b) for a, b in zip(inside, r[:, 3]*r[:, 4])): esc.append(i)
        with Pool(2) as pool: res = pool.map(strict, [(P[i], O[i][5]) for i in esc], chunksize=8)
        print(name, 'numpy disagreements:', len(esc), 'strict ok:', res.count('ok'), 'BAD:', res.count('BAD'), 'no reference:', res.count('noref'), [esc[k] for k, x in enumerate(res) if x != 'ok'][:8], flush=True)
