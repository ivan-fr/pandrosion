"""Figure: the product and square-root constructions, drawn from the traced curves."""
import cmath, math
import matplotlib; matplotlib.use('Agg')
import matplotlib.pyplot as plt
from geometry import Plane

def draw(ax, pl, n_setup, lim, labels, title):
    for k, it in enumerate(pl.items):
        setup = k < n_setup
        col = '0.72' if setup else ('#1f4e9a' if it[0] != 'par' else '#b5541c')
        lw = 0.6 if setup else 0.9
        if it[0] == 'circle':
            ax.add_patch(plt.Circle((it[1].real, it[1].imag), it[2], fill=False, color=col, lw=lw))
        else:
            P, Q = it[1], it[2]; d = (Q - P)/abs(Q - P)
            A, B = P - 20*d, P + 20*d
            ax.plot([A.real, B.real], [A.imag, B.imag], color=col, lw=lw, ls='--' if it[0] == 'par' else '-')
    ax.axhline(0, color='0.72', lw=0.6)
    for name, P, off in labels:
        ax.plot(P.real, P.imag, 'o', ms=3.2, color='black')
        ax.annotate(name, (P.real, P.imag), textcoords='offset points', xytext=off, fontsize=9)
    ax.set_xlim(lim[0], lim[1]); ax.set_ylim(lim[2], lim[3]); ax.set_aspect('equal')
    ax.set_xticks([]); ax.set_yticks([]); ax.set_title(title, fontsize=10)

fig, axes = plt.subplots(1, 2, figsize=(11, 5.2))
Z = cmath.rect(1.45, math.radians(38)); W = cmath.rect(1.7, math.radians(62))
pl = Plane(); n0 = len(pl.items); P = pl.prod(Z, W)
Z1, W1 = Z/abs(Z), W/abs(W); U = Z1*W1; Z3 = abs(Z)*U
draw(axes[0], pl, n0, (-2.3, 2.6, -1.3, 2.9),
     [('O', 0j, (-10, -11)), ('E', 1+0j, (4, -11)), ('Z', Z, (5, -3)), ('W', W, (5, 2)), (r'$Z_1$', Z1, (5, -9)),
      (r'$W_1$', W1, (-17, 3)), ('U', U, (-11, 5)), (r'$Z_3$', Z3, (-17, 2)), (r'$P=ZW$', P, (6, 0))],
     r'product: 6 j + 5 c')
Z = cmath.rect(2.6, math.radians(112))
pl = Plane(); n0 = len(pl.items); R = pl.sqrt(Z)
Z1 = Z/abs(Z); Z4 = -abs(Z) + 0j; M = (Z4 + 1)/2; H = 1j*math.sqrt(abs(Z))
draw(axes[1], pl, n0, (-3.1, 2.3, -1.6, 3.0),
     [('O', 0j, (4, -11)), ('E', 1+0j, (4, -11)), ('Z', Z, (5, 2)), (r'$Z_1$', Z1, (-16, 2)), (r'$Z_4$', Z4, (-6, -12)),
      ('M', M, (-4, -12)), ('H', H, (5, 3)), (r'$P=\sqrt{Z}$', R, (6, -2))],
     r'principal square root: 3 j + 7 c')
fig.tight_layout(pad=0.8)
fig.savefig('paper/constructions.png', dpi=170)
print('ok')
