"""Basins of attraction in the plane of the direct state u, for X = 1 (roots of unity)."""
import numpy as np
import matplotlib; matplotlib.use('Agg')
import matplotlib.pyplot as plt
from maps import Q, phi

def basin(name, p, N=700, L=2.0, nmax=40, tol=1e-9):
    xs = np.linspace(-L, L, N); ys = np.linspace(-L, L, N)
    u = (xs[None, :] + 1j*ys[:, None]).astype(complex)
    u[np.abs(u) < 1e-12] = 1e-12
    steps = np.full(u.shape, nmax)
    with np.errstate(all='ignore'):
        for n in range(nmax):
            t = 1/u**p
            done = (np.abs(t - 1) < tol) & (steps == nmax)
            steps[done] = n
            u = np.where(steps < nmax, u, u*phi(name, p, t))
    k = np.round(np.angle(u)*p/(2*np.pi)).astype(int) % p
    conv = (steps < nmax) & np.isfinite(u)
    return k, steps, conv

BASE = np.array([[0.13, 0.35, 0.62], [0.80, 0.42, 0.13], [0.24, 0.55, 0.36],
                 [0.58, 0.30, 0.55], [0.75, 0.65, 0.20]])
TITLE = {'AK': 'AK (Newton), order 2', 'AD': 'AD (Halley), order 3', 'proj': 'projective AD, order 4',
         'arc': 'decentered arc, order 5', 'nest': 'nested radicals, order 9',
         'tm': 'three means, order 9'}
names = ['AK', 'AD', 'proj', 'arc', 'nest', 'tm']
fig, axes = plt.subplots(2, 6, figsize=(18, 6.3))
stats = {}
for row, p in enumerate([3, 5]):
    for col, name in enumerate(names):
        k, steps, conv = basin(name, p)
        img = BASE[k % 5]
        shade = 1.0 - 0.55*np.clip(steps/14.0, 0, 1)
        img = 1 - (1 - img)*shade[..., None]
        img[~conv] = 0.0
        ax = axes[row, col]
        ax.imshow(img, extent=[-2, 2, -2, 2], origin='lower', interpolation='nearest')
        if name in ('AD', 'arc', 'nest', 'tm'):
            for j in range(p):
                for s in (-1, 1):
                    th = 2*np.pi*j/p + s*np.pi/(2*p)
                    ax.plot([0, 3*np.cos(th)], [0, 3*np.sin(th)], color='white', lw=0.7, ls=(0, (4, 3)))
        ax.plot(np.cos(2*np.pi*np.arange(p)/p), np.sin(2*np.pi*np.arange(p)/p), 'o', ms=3.2, mfc='white', mec='black', mew=0.6)
        ax.set_xlim(-2, 2); ax.set_ylim(-2, 2); ax.set_xticks([]); ax.set_yticks([])
        ax.set_title(TITLE[name] if row == 0 else '', fontsize=10.5)
        if col == 0: ax.set_ylabel(f'p = {p}', fontsize=11)
        # fraction of each open sector |arg(u/r_k)| < pi/p that reaches its own root
        xs = np.linspace(-2, 2, k.shape[0]); U = xs[None, :] + 1j*xs[:, None]
        own = np.round(np.angle(U)*p/(2*np.pi)).astype(int) % p
        stats[(name, p)] = (100*np.mean(conv), 100*np.mean(conv & (k == own)))
fig.tight_layout(pad=0.6)
fig.savefig('paper/basins.png', dpi=150)
for key, v in stats.items(): print(key, f'converged {v[0]:.2f}%  to the root of its own sector {v[1]:.2f}%')
