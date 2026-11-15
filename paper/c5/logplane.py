"""Basins in the logarithmic state plane for the irrational degree p = pi, X = 1."""
import numpy as np
import matplotlib; matplotlib.use('Agg')
import matplotlib.pyplot as plt
from maps import phi
p = np.pi
BASE = np.array([[0.13, 0.35, 0.62], [0.80, 0.42, 0.13], [0.24, 0.55, 0.36], [0.58, 0.30, 0.55], [0.75, 0.65, 0.20]])
TITLE = {'AD': 'AD (Halley)', 'arc': 'decentered arc', 'nest': 'nested radicals'}
fig, axes = plt.subplots(1, 3, figsize=(9.2, 5.6))
N = 700; xs = np.linspace(-1.6, 1.6, N); ys = np.linspace(-np.pi, np.pi, int(N*1.96))
for ax, name in zip(axes, ['AD', 'arc', 'nest']):
    l = (xs[None, :] + 1j*ys[:, None]).astype(complex)
    start_im = l.imag.copy()
    steps = np.full(l.shape, 40)
    with np.errstate(all='ignore'):
        for n in range(40):
            t = np.exp(-p*l)
            done = (np.abs(t - 1) < 1e-9) & (steps == 40)
            steps[done] = n
            l = np.where(steps < 40, l, l + np.log(phi(name, p, t)))
    k = np.round(l.imag*p/(2*np.pi))
    conv = (steps < 40) & np.isfinite(l)
    k = np.where(conv, k, 0).astype(int)
    img = BASE[k % 5]
    shade = 1.0 - 0.55*np.clip(steps/14.0, 0, 1)
    img = 1 - (1 - img)*shade[..., None]
    img[~conv] = 0.0
    ax.imshow(img, extent=[-1.6, 1.6, -np.pi, np.pi], origin='lower', interpolation='nearest', aspect='equal')
    for kk in (-1, 0, 1):
        ax.plot(0, 2*kk, 'o', ms=3.5, mfc='white', mec='black', mew=0.6)
        for s in (-1, 1):
            ax.axhline(2*kk + s*0.5, color='white', lw=0.7, ls=(0, (4, 3)))
    own = np.round(start_im*p/(2*np.pi)).astype(int)
    inside = np.abs(start_im - 2*own) < 0.5
    print(name, 'converged %.2f%%' % (100*conv.mean()), '| nearest determination %.2f%%' % (100*np.mean(conv & (k == own))),
          '| inside the strips: %.4f%%' % (100*np.mean((conv & (k == own))[inside])))
    ax.set_title(TITLE[name], fontsize=10); ax.set_xlabel(r'Re $\ell$ = ln|u|', fontsize=9)
    ax.set_xticks([-1, 0, 1]); ax.set_yticks([-2, 0, 2]); ax.tick_params(labelsize=8)
axes[0].set_ylabel(r'Im $\ell$ = arg u (not reduced)', fontsize=9)
fig.tight_layout(pad=0.6)
fig.savefig('paper/logplane.png', dpi=150)
