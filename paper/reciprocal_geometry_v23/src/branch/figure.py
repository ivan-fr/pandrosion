"""Figure: contraction ratio on the whole branch and the endpoint margin."""
import numpy as np, matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from pathlib import Path
fig, ax = plt.subplots(1, 2, figsize=(9.2, 3.4))
for n, c in [(3, '#176B9B'), (5, '#C0392B'), (17, '#2E8B57')]:
    r = np.sqrt(12*(n*n-1.0)); vp = (n*n+2+r)/(n*n-4); vm = 1/vp
    vv = np.linspace(vm*(1+1e-9), vp*(1-1e-9), 4000)
    A=(n+1)*(n+2); B=n*n-4; C=(n-1)*(n-2)
    t = (C*vv**2-2*B*vv+A)/(A*vv**2-2*B*vv+C)
    e = np.log(t)/n; ep = e+np.log(vv)
    ax[0].plot(t, np.abs(ep)/np.abs(e), color=c, lw=1.4, label=f'$p={n}$')
ax[0].set_xscale('log'); ax[0].set_ylim(0, 1.02)
ax[0].axhline(1, color='k', lw=.6, ls='--')
ax[0].set_xlabel(r'residual $t=Xs^p$ (whole real branch $\tau_-<t<\tau_+$)')
ax[0].set_ylabel(r'$|e^+|\,/\,|e|$'); ax[0].legend(frameon=False); ax[0].set_title('Contraction ratio on the branch', fontsize=10)
ps = np.arange(3, 401)
r = np.sqrt(12*(ps**2-1.0)); vp = (ps**2+2+r)/(ps**2-4)
tp = (7*ps**2-4+4*ps*np.sqrt(3*(ps**2-1.0)))/(ps**2-4)
m = 2*np.log(tp) - ps*np.log(vp)
ax[1].plot(ps, m, color='#176B9B', lw=1.4)
ax[1].axhline(2*np.log(7+4*np.sqrt(3))-2*np.sqrt(3), color='k', lw=.6, ls='--', label=r'limit $2\log(7+4\sqrt{3})-2\sqrt{3}\approx1.80$')
ax[1].set_xscale('log'); ax[1].set_ylim(0, 2.3)
ax[1].set_xlabel('degree $p$'); ax[1].set_ylabel(r'$2\log\tau_+-p\log v_+$')
ax[1].set_title('Endpoint margin (must be positive)', fontsize=10); ax[1].legend(frameon=False, fontsize=8)
for a in ax: a.spines['top'].set_visible(False); a.spines['right'].set_visible(False)
fig.tight_layout()
out = Path(__file__).resolve().parents[2]/'figures'/'branch_contraction.pdf'
fig.savefig(out); fig.savefig(out.with_suffix('.png'), dpi=160)
print('wrote', out)
