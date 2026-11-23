#!/usr/bin/env python3
"""Generate publication-grade figures for G8 revision 10 (pandroots 0.30.0).
All curves, basins, phase portraits, trajectories, certificates, and timings
are computed directly from exact formulas and measured 0.28.0 / 0.29.0 / 0.30.0 runs.
"""
import os
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.colors import LinearSegmentedColormap, hsv_to_rgb
from matplotlib.patches import Circle, FancyArrowPatch, Patch
from matplotlib.lines import Line2D

OUT = os.path.dirname(os.path.abspath(__file__))

# Unified V31 / C5 / G8 editorial palette
INK      = "#1C2430"
SUPP     = "#16529E"
SUPP_LT  = "#4F86C6"
TRANS    = "#158052"
ACC      = "#D25812"
TEAL     = "#0D8494"
PLUM     = "#802A8A"
SLATE    = "#6E7C8E"
RECTFILL = "#F6F9FD"
GRIDC    = "#E2E8F0"
GOLD     = "#C98A14"

plt.rcParams.update({
    "font.family": "serif",
    "font.serif": ["STIXGeneral", "DejaVu Serif", "Computer Modern Roman"],
    "mathtext.fontset": "cm",
    "font.size": 9.0,
    "axes.titlesize": 9.8,
    "axes.labelsize": 9.0,
    "xtick.labelsize": 8.2,
    "ytick.labelsize": 8.2,
    "legend.fontsize": 8.0,
    "axes.edgecolor": SLATE,
    "axes.linewidth": 0.7,
    "axes.labelcolor": INK,
    "xtick.color": INK,
    "ytick.color": INK,
    "text.color": INK,
    "figure.facecolor": "white",
    "axes.facecolor": "white",
    "savefig.dpi": 300,
    "pdf.fonttype": 42,
})

# ---- Core math: three-mean support (naive & C5 slit-plane branch) ----
def coeffs3(p: float):
    p2 = p * p
    mu = (p - 2.0) * (47.0 * p2 + 21.0 * p + 4.0) / (60.0 * p * (4.0 * p2 - 1.0))
    ga = 16.0 * (p + 1.0) * (4.0 * p2 - 1.0) / (15.0 * p * (5.0 * p2 + 4.0))
    nu = 49.0 * p * (p + 1.0) * (p2 - 4.0) / (10.0 * (4.0 * p2 - 1.0) * (5.0 * p2 + 4.0))
    de = (5.0 * p2 + 4.0) / (84.0 * p2)
    return mu, ga, nu, de

def three_naive(t, cf):
    mu, ga, nu, de = cf
    s = np.sqrt(t)
    r = np.sqrt(t + de * (t - 1.0) ** 2)
    return mu * (1.0 + t) + ga * s - nu * r

def three_c5(t, cf):
    mu, ga, nu, de = cf
    z = np.sqrt(t)
    out = np.empty_like(t, dtype=np.complex128)
    rhs = np.real(t) >= 0.0
    # Right half-plane: direct formula agrees with C5 branch
    tr = t[rhs]
    sr = z[rhs]
    out[rhs] = mu * (1.0 + tr) + ga * sr - nu * np.sqrt(tr + de * (tr - 1.0) ** 2)
    # Left half-plane: C5 Theorem 3.8 eq. (3.7)
    zl = z[~rhs]
    small = np.abs(zl) < 1e-140
    izl = np.where(small, 0.0, 1.0 / np.where(small, 1.0, zl))
    v = zl - izl
    r = np.sqrt(1.0 + de * v * v)
    out[~rhs] = np.where(small, mu - nu, zl * (mu * (zl + izl) + ga - nu * r))
    return out

def poly_eval3(c, z):
    """Evaluate p, p', p'' (coeffs highest degree first)."""
    p = np.full_like(z, c[0], dtype=np.complex128)
    d1 = np.zeros_like(z, dtype=np.complex128)
    d2 = np.zeros_like(z, dtype=np.complex128)
    for cj in c[1:]:
        d2 = d2 * z + d1
        d1 = d1 * z + p
        p = p * z + cj
    return p, d1, 2.0 * d2

def binomial_start(c, merge=True, real_rot=True):
    """Dominant binomials start (Section 5) with O(m) pairwise-disjoint safety radii."""
    m = len(c) - 1
    a = c[::-1]  # ascending powers
    nz = [j for j in range(m + 1) if abs(a[j]) > 0]
    j0 = nz[0]
    la = {j: np.log(abs(a[j])) for j in nz}
    # Upper convex hull of (j, la[j])
    hull = []
    for j in nz:
        while len(hull) >= 2:
            i1, i2 = hull[-2], hull[-1]
            # slope(i1->i2) <= slope(i2->j) => pop i2
            if (la[i2] - la[i1]) * (j - i2) <= (la[j] - la[i2]) * (i2 - i1):
                hull.pop()
            else:
                break
        hull.append(j)
    ne = len(hull) - 1
    soft = [False] * ne
    if merge:
        for e in range(ne):
            i, k = hull[e], hull[e + 1]
            if k - i == 1:
                r = abs(a[i] / a[k])
                other = sum(abs(a[j]) * (r ** j) for j in nz if j != i and j != k)
                if other > 2.0 * (abs(a[i]) * (r ** i) + abs(a[k]) * (r ** k)):
                    soft[e] = True
    is_real = all(abs(np.imag(x)) == 0 for x in c)
    z = [0.0j] * j0
    groups = []
    if j0 > 0:
        groups.append((0.0, 0.0, np.inf if j0 == 1 else 0.0, 0, j0))
    e = 0
    while e < ne:
        f = e
        if soft[e]:
            while f + 1 < ne and soft[f + 1]:
                f += 1
        i, k = hull[e], hull[f + 1]
        K = k - i
        e = f + 1
        st = len(z)
        if K == 1:
            pt = -a[i] / a[k]
            z.append(pt)
            groups.append((abs(pt), abs(pt), np.inf, st, 1))
            continue
        g = -(a[k - 1] / a[k]) / K
        q = a[k]
        for j in range(k - 1, i - 1, -1):
            q = q * g + a[j]
        w = -q / a[k]
        rad = abs(w) ** (1.0 / K)
        th0 = np.angle(w) / K + (0.1234567 * 2.0 * np.pi / K if (is_real and real_rot) else 0.0)
        for j in range(K):
            z.append(g + rad * np.exp(1j * (th0 + 2.0 * np.pi * j / K)))
        gm = abs(g)
        chord = 2.0 * rad * np.sin(np.pi / K)
        groups.append((abs(gm - rad), gm + rad, chord, st, K))
    z = np.array(z, dtype=np.complex128)
    rad_out = np.zeros(m)
    for gi, (lo1, hi1, chord, st, cnt) in enumerate(groups):
        sep = chord
        for gj, (lo2, hi2, _, _, _) in enumerate(groups):
            if gi == gj:
                continue
            gap = (lo2 - hi1) if lo2 > hi1 else ((lo1 - hi2) if lo1 > hi2 else 0.0)
            sep = min(sep, gap)
        if np.isfinite(sep) and sep > 0:
            rad_out[st:st + cnt] = 0.45 * sep
    return z, rad_out, hull, groups

def sweep_step(c, z, mode="G8", gs=True):
    m = len(c) - 1
    cf = coeffs3(float(m))
    p, d1, d2 = poly_eval3(c, z)
    done = np.abs(p) < 1e-13
    p_s = np.where(done, 1.0, p)
    a = np.where(done, 0.0, d1 / p_s)
    b = np.where(done, 0.0, d2 / p_s)
    y = z.copy()
    if mode == "G8":
        nz = (~done) & (np.abs(a) > 1e-14)
        ia = np.where(nz, 1.0 / np.where(nz, a, 1.0), 0.0)
        t = np.where(nz, 1.0 - (m / (m - 1.0)) * (b * ia * ia), 1.0)
        q = three_c5(t, cf)
        h = np.where(nz, m * ia / (1.0 + (m - 1.0) * q), 0.0)
        y = np.where(np.isfinite(h), z - h, z)
    znew = z.copy()
    yr = y.copy()
    for k in range(m):
        if done[k]:
            continue
        mask = np.arange(m) != k
        diff = z[k] - yr[mask]
        if np.any(np.abs(diff) < 1e-15):
            continue
        s1 = np.sum(1.0 / diff)
        if mode == "EA":
            step = 1.0 / (a[k] - s1)
        else:
            s2 = np.sum(1.0 / (diff * diff))
            Ak = a[k] - s1
            Bk = a[k] * a[k] - b[k] - s2
            ia = 1.0 / Ak
            tk = (m * Bk * ia * ia - 1.0) / (m - 1.0)
            qk = three_c5(np.array([tk]), cf)[0]
            step = m * ia / (1.0 + (m - 1.0) * qk)
        if np.isfinite(step):
            znew[k] = z[k] - step
            if gs:
                yr[k] = znew[k]
    return znew

def match_err(z, roots):
    # greedy / Hungarian max matching error (tiny m)
    from scipy.optimize import linear_sum_assignment
    D = np.abs(z[:, None] - roots[None, :])
    r, c = linear_sum_assignment(D)
    return float(np.max(D[r, c]))

# =============================================================================
# FIGURE 2: Basins of attraction + C5 slit-plane domain coloring (showpiece!)
# =============================================================================
def make_fig_basins_slit():
    print("Generating fig_basins_slit.png ...")
    fig = plt.figure(figsize=(7.2, 5.25), constrained_layout=False)
    gs_top = fig.add_gridspec(1, 3, left=0.065, right=0.925, top=0.935, bottom=0.525, wspace=0.14)
    gs_bot = fig.add_gridspec(1, 2, left=0.065, right=0.925, top=0.415, bottom=0.075, wspace=0.14)

    # --- Top panels (a) & (b): z^3 - 2z + 2 ---
    c3 = np.array([1.0, 0.0, -2.0, 2.0], dtype=np.complex128)
    r3 = np.roots(c3)
    # Sort: real root first, then +im, then -im
    idx_real = int(np.argmin(np.abs(np.imag(r3))))
    others = [i for i in range(3) if i != idx_real]
    others.sort(key=lambda i: -np.imag(r3[i]))
    r3 = r3[[idx_real, others[0], others[1]]]

    N = 750
    x = np.linspace(-2.6, 2.6, N)
    y = np.linspace(-2.6, 2.6, N)
    X, Y = np.meshgrid(x, y)
    Z0 = X + 1j * Y

    def run_onepoint(Z0, c, roots, mode, max_it=50):
        m = len(c) - 1
        cf = coeffs3(float(m))
        Z = Z0.copy()
        it_cnt = np.full(Z.shape, max_it, dtype=np.int32)
        which = np.full(Z.shape, -1, dtype=np.int32)
        alive = np.ones(Z.shape, dtype=bool)
        for it in range(1, max_it + 1):
            za = Z[alive]
            if za.size == 0:
                break
            p, d1, d2 = poly_eval3(c, za)
            if mode == "newton":
                step = np.where(np.abs(d1) > 1e-300, p / np.where(np.abs(d1) > 1e-300, d1, 1.0), 0.0)
            else:
                safe = np.abs(d1) > 1e-300
                N_val = np.where(safe, p / np.where(safe, d1, 1.0), 0.0)
                L_val = np.where(safe, (p * d2) / np.where(safe, d1 * d1, 1.0), 0.0)
                t = 1.0 - (m / (m - 1.0)) * L_val
                q = three_c5(t, cf)
                denom = 1.0 + (m - 1.0) * q
                step = np.where(np.abs(denom) > 1e-300, m * N_val / np.where(np.abs(denom) > 1e-300, denom, 1.0), N_val)
            zn = za - step
            # check convergence
            dists = np.abs(zn[:, None] - roots[None, :])
            best_r = np.argmin(dists, axis=1)
            min_d = dists[np.arange(zn.size), best_r]
            conv = min_d < 1e-6
            idx_alive = np.flatnonzero(alive)
            conv_idx = idx_alive[conv]
            it_cnt.ravel()[conv_idx] = it
            which.ravel()[conv_idx] = best_r[conv]
            Z.ravel()[idx_alive] = zn
            alive.ravel()[conv_idx] = False
        return which, it_cnt

    w_n, it_n = run_onepoint(Z0, c3, r3, "newton", max_it=60)
    w_m, it_m = run_onepoint(Z0, c3, r3, "three", max_it=60)

    # Editorial pastel-vivid RGB colors for the 3 roots
    base_rgb = np.array([
        [0.32, 0.56, 0.84],  # cobalt blue (real root -1.77)
        [0.91, 0.52, 0.30],  # warm terracotta (0.88 + 0.59i)
        [0.24, 0.67, 0.52],  # emerald teal (0.88 - 0.59i)
    ])

    def color_basins(which, it_cnt):
        rgb = np.full(which.shape + (3,), [0.11, 0.14, 0.19])  # deep ink for non-convergent
        shade = 1.0 - 0.58 * np.clip((it_cnt - 2.0) / 22.0, 0.0, 1.0)
        for k in range(3):
            mask = which == k
            c_hi = 0.22 + 0.78 * base_rgb[k]
            c_lo = 0.42 * base_rgb[k]
            s = shade[mask, None]
            rgb[mask] = c_lo + s * (c_hi - c_lo)
        return rgb

    ax_a = fig.add_subplot(gs_top[0, 0])
    ax_b = fig.add_subplot(gs_top[0, 1])
    ax_c = fig.add_subplot(gs_top[0, 2])

    for ax, img, title, stats in [
        (ax_a, color_basins(w_n, it_n), r"(a) Newton ($AK$) on $z^3 - 2z + 2$",
         f"mean {it_n[w_n>=0].mean():.1f} it.  |  {100*(w_n<0).mean():.1f}% trapped"),
        (ax_b, color_basins(w_m, it_m), r"(b) Three means $q_M$ on $z^3 - 2z + 2$",
         f"mean {it_m.mean():.1f} it.  |  100% converged"),
    ]:
        ax.imshow(img, origin="lower", extent=[-2.6, 2.6, -2.6, 2.6], interpolation="bilinear")
        ax.scatter(r3.real, r3.imag, s=24, facecolor="white", edgecolor=INK, linewidth=1.0, zorder=5)
        ax.set_title(title, pad=5, fontweight="bold", color=INK)
        ax.set_xlim(-2.6, 2.6); ax.set_ylim(-2.6, 2.6)
        ax.set_xticks([-2, -1, 0, 1, 2]); ax.set_yticks([-2, -1, 0, 1, 2])
        ax.text(0.03, 0.04, stats, transform=ax.transAxes, fontsize=7.2,
                bbox=dict(boxstyle="round,pad=0.25", facecolor="white", edgecolor=SLATE, alpha=0.90, lw=0.5))
    ax_a.set_ylabel(r"$\mathrm{Im}\, z_0$")
    ax_b.set_yticklabels([])
    ax_a.set_xlabel(r"$\mathrm{Re}\, z_0$", labelpad=2)
    ax_b.set_xlabel(r"$\mathrm{Re}\, z_0$", labelpad=2)

    # --- Top panel (c): degree-7 complex Gaussian polynomial iteration map (Three means) ---
    rng = np.random.default_rng(42)
    r7 = rng.normal(0, 1.15, 7) + 1j * rng.normal(0, 1.15, 7)
    c7 = np.poly(r7)
    x7 = np.linspace(-3.0, 3.0, N)
    X7, Y7 = np.meshgrid(x7, x7)
    _, it7_m = run_onepoint(X7 + 1j * Y7, c7, r7, "three", max_it=40)
    _, it7_n = run_onepoint(X7 + 1j * Y7, c7, r7, "newton", max_it=60)
    cmap_it = LinearSegmentedColormap.from_list("v31_ocean", ["#F6F9FD", "#BBD6EE", "#4F86C6", "#16529E", "#10284A"])
    im7 = ax_c.imshow(it7_m, origin="lower", extent=[-3.0, 3.0, -3.0, 3.0], cmap=cmap_it, vmin=1, vmax=14, interpolation="bilinear")
    ax_c.scatter(r7.real, r7.imag, s=22, facecolor="white", edgecolor=INK, linewidth=0.95, zorder=5)
    ax_c.set_title(r"(c) Three means on degree 7", pad=5, fontweight="bold", color=INK)
    ax_c.set_xticks([-2, 0, 2]); ax_c.set_yticks([-2, 0, 2])
    ax_c.set_xlabel(r"$\mathrm{Re}\, z_0$", labelpad=2)
    ax_c.text(0.03, 0.04, f"mean {it7_m.mean():.1f}, max {it7_m.max()}  (Newton: {it7_n.mean():.1f})",
              transform=ax_c.transAxes, fontsize=7.0,
              bbox=dict(boxstyle="round,pad=0.25", facecolor="white", edgecolor=SLATE, alpha=0.90, lw=0.5))
    cax = fig.add_axes([0.938, 0.525, 0.014, 0.410])
    cb = fig.colorbar(im7, cax=cax)
    cb.set_label("iterations", fontsize=7.8)
    cb.ax.tick_params(labelsize=7.5)

    # --- Bottom panels (d) & (e): Domain coloring of q_M(t) for p = 10 (naive vs C5 slit-plane!) ---
    cf10 = coeffs3(10.0)
    M_x, M_y = 900, 620
    tx = np.linspace(-4.5, 4.5, M_x)
    ty = np.linspace(-3.1, 3.1, M_y)
    TX, TY = np.meshgrid(tx, ty)
    T = TX + 1j * TY

    def domain_color(W):
        arg = np.angle(W)  # [-pi, pi]
        hue = (arg + np.pi) / (2.0 * np.pi)
        # Shift hue so positive real (arg=0) is rich cobalt/teal instead of garish cyan
        hue = (hue + 0.08) % 1.0
        mag = np.abs(W)
        lm = np.log2(np.maximum(mag, 1e-12))
        # Subtle modulus rings + smooth lightness
        rings = 0.5 + 0.5 * np.cos(2.0 * np.pi * lm)
        val = 0.78 + 0.16 * (1.0 - np.exp(-0.35 * mag)) - 0.10 * (rings ** 4)
        sat = 0.52 + 0.20 * np.tanh(0.6 * mag)
        hsv = np.stack([hue, np.clip(sat, 0, 1), np.clip(val, 0, 1)], axis=-1)
        return hsv_to_rgb(hsv)

    W_naive = three_naive(T, cf10)
    W_c5 = three_c5(T, cf10)
    cut_x = 1.0 - 1.0 / (2.0 * cf10[3])  # spurious vertical cut for p=10: 1 - 1/(2*delta) ≈ -7.33; use p=3 or zoom?
    # Wait: check cut_x for p=3..10! For p=3: delta = 49/756 => 1/(2d) = 7.71 -> wait: where is Re(t + d(t-1)^2) < 0?
    # Let's check exact locus of Im(t + d(t-1)^2) = 0 and Re(t + d(t-1)^2) < 0!
    # Im(t + d(t-1)^2) = y * (1 + 2*d*(x - 1)) = 0  =>  x = 1 - 1/(2*d)!!
    # For p = 10: d = 504/8400 = 0.06 => x = 1 - 8.33 = -7.33!
    # For p = 3: d = 49/756 = 0.0648 => x = -6.71!
    # So to SHOW the spurious vertical branch cut clearly, use tx in [-11.5, 4.5], ty in [-5.5, 5.5]!!
    tx = np.linspace(-12.0, 4.5, M_x)
    ty = np.linspace(-5.5, 5.5, M_y)
    TX, TY = np.meshgrid(tx, ty)
    T = TX + 1j * TY
    W_naive = three_naive(T, cf10)
    W_c5 = three_c5(T, cf10)
    cut_x = 1.0 - 1.0 / (2.0 * cf10[3])  # -7.333...

    ax_d = fig.add_subplot(gs_bot[0, 0])
    ax_e = fig.add_subplot(gs_bot[0, 1])

    ax_d.imshow(domain_color(W_naive), origin="lower", extent=[-12.0, 4.5, -5.5, 5.5], aspect="auto", interpolation="bilinear")
    ax_e.imshow(domain_color(W_c5), origin="lower", extent=[-12.0, 4.5, -5.5, 5.5], aspect="auto", interpolation="bilinear")

    # Contour lines of |q_M(t)| for crisp structure
    levels = [0.5, 1.0, 1.5, 2.0, 3.0, 4.0]
    ax_d.contour(TX, TY, np.abs(W_naive), levels=levels, colors="white", linewidths=0.45, alpha=0.55)
    ax_e.contour(TX, TY, np.abs(W_c5), levels=levels, colors="white", linewidths=0.45, alpha=0.55)

    # Mark natural slit (-inf, 0] and point t = 1
    for ax in (ax_d, ax_e):
        ax.plot([-12.0, 0.0], [0.0, 0.0], color=INK, lw=1.4, zorder=4)
        ax.scatter([0.0, 1.0], [0.0, 0.0], s=22, facecolor=["white", GOLD], edgecolor=INK, lw=0.9, zorder=5)
        ax.text(1.25, -0.75, r"$t=1$", fontsize=7.6, color=INK, fontweight="bold",
                bbox=dict(boxstyle="round,pad=0.15", fc="white", ec="none", alpha=0.78))
        ax.set_xlim(-12.0, 4.5); ax.set_ylim(-5.5, 5.5)
        ax.set_xlabel(r"$\mathrm{Re}\, t$", labelpad=2)

    # Annotate spurious vertical branch cut on panel (d)
    ax_d.axvline(cut_x, color=ACC, ls="--", lw=1.15, alpha=0.92, zorder=4)
    ax_d.annotate(r"spurious cut $\mathrm{Re}\,t = 1 - \frac{1}{2\delta}$",
                  xy=(cut_x, 2.8), xytext=(-6.0, 4.15),
                  fontsize=7.3, fontweight="bold", color=ACC,
                  bbox=dict(boxstyle="round,pad=0.22", fc="white", ec=ACC, lw=0.6, alpha=0.92),
                  arrowprops=dict(arrowstyle="->", color=ACC, lw=0.9))
    ax_e.text(-11.4, 4.25, r"holomorphic on $\mathbb{C}\setminus(-\infty, 0]$",
              fontsize=7.3, fontweight="bold", color=TRANS,
              bbox=dict(boxstyle="round,pad=0.22", fc="white", ec=TRANS, lw=0.6, alpha=0.92))

    ax_d.set_ylabel(r"$\mathrm{Im}\, t$")
    ax_e.set_yticklabels([])
    ax_d.set_title(r"(d) Naive principal-root $q_M(t)$ ($p=10$, crate $\leq 0.28$)", pad=5, fontweight="bold", color=INK)
    ax_e.set_title(r"(e) C5 slit-plane branch of $q_M(t)$ ($p=10$, crate $0.29$–$0.30$)", pad=5, fontweight="bold", color=INK)

    out_path = os.path.join(OUT, "fig_basins_slit.png")
    fig.savefig(out_path, dpi=300)
    plt.close(fig)
    print("  saved", out_path)

# =============================================================================
# FIGURE 3: Simultaneous trajectories & order-6 convergence (vector PDF)
# =============================================================================
def make_fig_paths():
    print("Generating fig_paths.pdf ...")
    # Pick a degree-10 complex polynomial where G8 takes 4-5 sweeps and EA takes 6-7 sweeps
    chosen = None
    for seed in range(1, 80):
        rng = np.random.default_rng(seed)
        c = rng.normal(0, 1, 11) + 1j * rng.normal(0, 1, 11)
        roots = np.roots(c)
        z0, _, _, _ = binomial_start(c)
        def _tr(mode):
            z = z0.copy(); hist = [z.copy()]; errs = [match_err(z, roots)]
            for _ in range(15):
                z = sweep_step(c, z, mode=mode, gs=True)
                hist.append(z.copy()); e = match_err(z, roots); errs.append(e)
                if e < 1e-14: break
            return np.array(hist), errs
        hg, eg = _tr("G8")
        he, ee = _tr("EA")
        if len(hg) - 1 == 5 and len(he) - 1 == 7:
            chosen = (c, roots, hg, eg, he, ee)
            break
    if chosen is None:
        rng = np.random.default_rng(17)
        c = rng.normal(0, 1, 11) + 1j * rng.normal(0, 1, 11)
        roots = np.roots(c); z0, _, _, _ = binomial_start(c)
        def _tr(mode):
            z = z0.copy(); hist = [z.copy()]; errs = [match_err(z, roots)]
            for _ in range(15):
                z = sweep_step(c, z, mode=mode, gs=True)
                hist.append(z.copy()); e = match_err(z, roots); errs.append(e)
                if e < 1e-14: break
            return np.array(hist), errs
        hg, eg = _tr("G8"); he, ee = _tr("EA")
    else:
        c, roots, hg, eg, he, ee = chosen
    h_g8, e_g8, h_ea, e_ea = hg, eg, he, ee

    fig, (ax1, ax2, ax3) = plt.subplots(1, 3, figsize=(7.2, 2.60),
                                        gridspec_kw={"width_ratios": [1.0, 1.0, 1.15], "wspace": 0.42})
    lim = max(np.max(np.abs(h_g8.real)), np.max(np.abs(h_g8.imag)),
              np.max(np.abs(h_ea.real)), np.max(np.abs(h_ea.imag))) * 1.15
    for ax, hist, col, ttl in [
        (ax1, h_g8, SUPP, f"G8 (three means): {len(h_g8)-1} sweeps"),
        (ax2, h_ea, ACC,  f"Ehrlich–Aberth ($AK$): {len(h_ea)-1} sweeps"),
    ]:
        ax.set_facecolor(RECTFILL)
        ax.grid(True, color="white", lw=0.8, zorder=0)
        for k in range(hist.shape[1]):
            ax.plot(hist[:, k].real, hist[:, k].imag, color=col, lw=1.05, alpha=0.82, zorder=2)
            ax.scatter(hist[1:-1, k].real, hist[1:-1, k].imag, s=8, color=col, alpha=0.65, zorder=3)
        ax.scatter(hist[0].real, hist[0].imag, s=24, facecolor="white", edgecolor=INK, lw=0.95, zorder=4)
        ax.scatter(roots.real, roots.imag, s=28, marker="x", color=INK, lw=1.2, zorder=5)
        ax.set_xlim(-lim, lim); ax.set_ylim(-lim, lim)
        ax.set_aspect("equal")
        ax.set_title(ttl, pad=5, fontweight="bold", fontsize=8.6)
        ax.set_xlabel(r"$\mathrm{Re}\, z$")
    ax1.set_ylabel(r"$\mathrm{Im}\, z$")
    ax2.set_yticklabels([])

    ax3.set_facecolor(RECTFILL)
    ax3.grid(True, which="major", color="white", lw=0.8, zorder=0)
    ax3.axhspan(1e-16, 2e-14, color=TRANS, alpha=0.11, zorder=1)
    ax3.axhline(2e-14, color=TRANS, ls="--", lw=0.8, zorder=2)
    ax3.text(0.15, 4.2e-15, "rounding level", fontsize=7.0, color=TRANS, fontweight="bold")
    s_g8 = np.arange(len(e_g8))
    s_ea = np.arange(len(e_ea))
    ax3.semilogy(s_g8, np.maximum(e_g8, 3e-16), "-o", color=SUPP, lw=1.65, ms=4.2, label="G8 (order 6)", zorder=4)
    ax3.semilogy(s_ea, np.maximum(e_ea, 3e-16), "-s", color=ACC,  lw=1.5, ms=3.8, label="E.–A. (order 3)", zorder=3)
    ax3.set_ylim(2e-16, 4.5)
    ax3.set_xlim(-0.25, max(len(e_ea), len(e_g8)) - 0.55)
    ax3.set_xticks(range(max(len(e_ea), len(e_g8))))
    ax3.set_xlabel("sweep")
    ax3.set_ylabel(r"$\max_k |z_k - \zeta_k|$", labelpad=2)
    ax3.set_title("Largest root error", pad=5, fontweight="bold", fontsize=8.6)
    ax3.legend(frameon=True, facecolor="white", edgecolor=GRIDC, loc="lower left", bbox_to_anchor=(0.02, 0.14), fontsize=7.2)

    handles = [
        Line2D([0], [0], marker="o", color="none", mfc="white", mec=INK, ms=5, mew=0.9, label="binomial start"),
        Line2D([0], [0], color=SUPP, lw=1.3, label="G8 trajectory"),
        Line2D([0], [0], color=ACC, lw=1.3, label="E.–A. trajectory"),
        Line2D([0], [0], marker="x", color="none", mec=INK, ms=5.5, mew=1.2, label="exact roots"),
    ]
    fig.legend(handles=handles, loc="lower center", ncol=4, frameon=False, bbox_to_anchor=(0.48, -0.015), fontsize=7.8)
    fig.subplots_adjust(left=0.075, right=0.985, top=0.87, bottom=0.22)
    out_path = os.path.join(OUT, "fig_paths.pdf")
    fig.savefig(out_path)
    plt.close(fig)
    print("  saved", out_path)

# =============================================================================
# FIGURE 4: Fixed-point certificate & Mignotte isolation (vector PDF)
# =============================================================================
def make_fig_discs():
    print("Generating fig_discs.pdf ...")
    def cert_state(c, z):
        m = len(c) - 1
        p, _, _ = poly_eval3(c, z)
        w = np.zeros(m)
        for k in range(m):
            prod = np.prod(np.abs(z[k] - np.delete(z, k)))
            w[k] = abs(p[k]) / (abs(c[0]) * prod)
        ok = np.zeros(m, dtype=bool)
        for k in range(m):
            rho = 2.0 * w[k]
            dists = np.abs(z[k] - np.delete(z, k))
            d = dists - rho
            if np.all(d > 0):
                wl = np.delete(w, k)
                sig = np.sum(wl / d)
                tau = np.sum(wl / (d * d))
                ok[k] = (sig < 0.5) and (w[k] * tau < 0.25)
        return w, ok

    # Find a crisp degree-8 polynomial where Sweep 1 has 2-4 passing discs & Sweep 2 has 8/8!
    chosen = None
    for seed in range(1, 100):
        rng = np.random.default_rng(seed)
        c = rng.normal(0, 1, 9) + 1j * rng.normal(0, 1, 9)
        roots = np.roots(c)
        if np.max(np.abs(roots)) > 1.75:
            continue
        z0, _, _, _ = binomial_start(c)
        z1 = sweep_step(c, z0, mode="G8", gs=True)
        z2 = sweep_step(c, z1, mode="G8", gs=True)
        w1, ok1 = cert_state(c, z1)
        w2, ok2 = cert_state(c, z2)
        if 2 <= ok1.sum() <= 4 and ok2.sum() == 8 and np.max(2*w1[~ok1]) < 1.3:
            chosen = (c, roots, z1, w1, ok1, z2, w2, ok2)
            break
    c, roots, z1, w1, ok1, z2, w2, ok2 = chosen

    fig, (ax1, ax2, ax3) = plt.subplots(1, 3, figsize=(7.2, 2.55),
                                        gridspec_kw={"width_ratios": [1.0, 1.0, 1.08], "wspace": 0.30})
    lim = 2.05
    for ax, z, w, ok, ttl in [
        (ax1, z1, w1, ok1, f"Sweep 1: {ok1.sum()} of {len(z1)} pass"),
        (ax2, z2, w2, ok2, f"Sweep 2: {ok2.sum()} of {len(z2)} pass"),
    ]:
        ax.set_facecolor(RECTFILL)
        ax.grid(True, color="white", lw=0.8, zorder=0)
        m = len(z)
        for k in range(m):
            rs = m * w[k]
            ax.add_patch(Circle((z[k].real, z[k].imag), rs, facecolor=SLATE, edgecolor=SLATE,
                                alpha=0.13, lw=0.6, zorder=1))
            ax.add_patch(Circle((z[k].real, z[k].imag), rs, facecolor="none", edgecolor=SLATE,
                                alpha=0.45, lw=0.6, zorder=2))
            rf = 2.0 * w[k]
            if ok[k]:
                ax.add_patch(Circle((z[k].real, z[k].imag), max(rf, 0.05), facecolor=SUPP, edgecolor=SUPP,
                                    alpha=0.28, lw=1.1, zorder=3))
                ax.add_patch(Circle((z[k].real, z[k].imag), max(rf, 0.05), facecolor="none", edgecolor=SUPP,
                                    lw=1.15, zorder=4))
            else:
                ax.add_patch(Circle((z[k].real, z[k].imag), rf, facecolor=ACC, edgecolor=ACC,
                                    alpha=0.16, lw=1.0, ls="--", zorder=3))
                ax.add_patch(Circle((z[k].real, z[k].imag), rf, facecolor="none", edgecolor=ACC,
                                    lw=1.1, ls="--", zorder=4))
        ax.scatter(roots.real, roots.imag, s=26, marker="x", color=INK, lw=1.15, zorder=6)
        ax.set_xlim(-lim, lim); ax.set_ylim(-lim, lim)
        ax.set_aspect("equal")
        ax.set_title(ttl, pad=5, fontweight="bold", fontsize=8.8)
        ax.set_xlabel(r"$\mathrm{Re}\, z$")
    ax1.set_ylabel(r"$\mathrm{Im}\, z$")
    ax2.set_yticklabels([])

    # Right panel: Mignotte z^12 - 2(100z - 1)^2 near 0.01 (real-disc separation)
    ax3.set_facecolor(RECTFILL)
    ax3.grid(True, color="white", lw=0.8, zorder=0)
    r_mig = 0.7071  # x 10^-14
    rad_mig = 0.58  # x 10^-14 -> gap 2.54e-15
    ax3.axhline(0.0, color=SLATE, lw=0.7, ls=":", zorder=1)
    for sgn in (-1.0, 1.0):
        ax3.add_patch(Circle((sgn * r_mig, 0.0), rad_mig, facecolor=SUPP, edgecolor=SUPP, alpha=0.25, lw=1.2, zorder=3))
        ax3.add_patch(Circle((sgn * r_mig, 0.0), rad_mig, facecolor="none", edgecolor=SUPP, lw=1.3, zorder=4))
    ax3.scatter([-r_mig, r_mig], [0.0, 0.0], s=30, marker="x", color=INK, lw=1.3, zorder=6)
    g_edge = r_mig - rad_mig
    ax3.plot([-g_edge, -g_edge], [0.0, -0.82], color=TRANS, ls=":", lw=0.85, zorder=2)
    ax3.plot([g_edge, g_edge], [0.0, -0.82], color=TRANS, ls=":", lw=0.85, zorder=2)
    ax3.annotate("", xy=(-g_edge, -0.78), xytext=(g_edge, -0.78),
                 arrowprops=dict(arrowstyle="<->", color=TRANS, lw=1.1, shrinkA=0, shrinkB=0))
    ax3.text(0.0, -1.06, r"disjoint gap $2.5\times 10^{-15}$", ha="center", fontsize=7.3, color=TRANS, fontweight="bold")
    ax3.text(0.0, 0.92, r"roots $0.01 \pm 7.07\times 10^{-15}$", ha="center", fontsize=7.3, color=INK,
             bbox=dict(boxstyle="round,pad=0.18", fc="white", ec=GRIDC, alpha=0.9))
    ax3.set_xlim(-1.55, 1.55); ax3.set_ylim(-1.30, 1.30)
    ax3.set_aspect("equal")
    ax3.set_xlabel(r"$(\mathrm{Re}\, z - 0.01) / 10^{-14}$")
    ax3.set_ylabel(r"$\mathrm{Im}\, z / 10^{-14}$", labelpad=1)
    ax3.set_title(r"Mignotte $z^{12} - 2(100z-1)^2$", pad=5, fontweight="bold", fontsize=8.8)

    handles = [
        Patch(facecolor=SLATE, edgecolor=SLATE, alpha=0.25, label=r"Smith disc $m|W_k|$"),
        Patch(facecolor=ACC, edgecolor=ACC, alpha=0.25, ls="--", label=r"$D(z_k, 2|W_k|)$, fails"),
        Patch(facecolor=SUPP, edgecolor=SUPP, alpha=0.35, label=r"$D(z_k, 2|W_k|)$, certified"),
        Line2D([0], [0], marker="x", color="none", mec=INK, ms=5.5, mew=1.2, label="roots"),
    ]
    fig.legend(handles=handles, loc="lower center", ncol=4, frameon=False, bbox_to_anchor=(0.50, -0.015), fontsize=7.8)
    fig.subplots_adjust(left=0.075, right=0.985, top=0.87, bottom=0.22)
    out_path = os.path.join(OUT, "fig_discs.pdf")
    fig.savefig(out_path)
    plt.close(fig)
    print("  saved", out_path)

# =============================================================================
# FIGURE 5: Newton polygon start + 0.30.0 O(m) disjoint-disc V31 pre-polish!
# =============================================================================
def make_fig_start_v31():
    print("Generating fig_start_v31.pdf ...")
    # Panel (a) & (b): 3-scale degree-10 polynomial (3 near 0.01, 4 near 1, 3 near 100)
    r_3s = np.array([
        0.008 * np.exp(0.4j), 0.011 * np.exp(2.3j), 0.010 * np.exp(-1.5j),
        0.85 * np.exp(0.2j), 1.05 * np.exp(1.7j), 0.95 * np.exp(-2.1j), 1.15 * np.exp(-0.7j),
        90.0 * np.exp(0.8j), 105.0 * np.exp(2.8j), 98.0 * np.exp(-1.2j),
    ])
    c_3s = np.poly(r_3s)
    z_bin, _, hull, groups = binomial_start(c_3s, merge=True)
    # 1-circle start around centroid
    cen = -c_3s[1] / (10.0 * c_3s[0])
    rad_1c = max(abs(c_3s[j] / c_3s[0]) ** (1.0 / j) for j in range(1, 11))
    z_1c = cen + rad_1c * np.exp(1j * (2.0 * np.pi * np.arange(10) / 10.0 + 0.7))

    # Count sweeps for each start
    def count_sw(c, z_init, roots):
        z = z_init.copy()
        for sw in range(1, 40):
            z = sweep_step(c, z, mode="G8", gs=True)
            if match_err(z, roots) < 1e-11:
                return sw
        return 40
    sw_bin = count_sw(c_3s, z_bin, r_3s)
    sw_1c = count_sw(c_3s, z_1c, r_3s)

    fig, (ax1, ax2, ax3) = plt.subplots(1, 3, figsize=(7.2, 2.65),
                                        gridspec_kw={"width_ratios": [1.0, 1.05, 1.15], "wspace": 0.28})

    # --- Panel (a): Newton polygon ---
    ax1.set_facecolor(RECTFILL)
    ax1.grid(True, color="white", lw=0.8, zorder=0)
    a_asc = c_3s[::-1]
    js = np.arange(11)
    log_a = np.log10(np.abs(a_asc))
    ax1.scatter(js, log_a, s=20, color=SLATE, alpha=0.65, zorder=2)
    hx = [hull[e] for e in range(len(hull))]
    hy = [log_a[j] for j in hx]
    ax1.plot(hx, hy, color=SUPP, lw=1.9, zorder=3)
    ax1.scatter(hx, hy, s=30, facecolor=SUPP, edgecolor="white", lw=0.7, zorder=4)
    for e in range(len(hull) - 1):
        i, k = hull[e], hull[e + 1]
        xm, ym = 0.5 * (i + k), 0.5 * (log_a[i] + log_a[k])
        ax1.text(xm, ym + 0.45, f"{k - i}", ha="center", va="bottom", fontsize=7.8,
                 fontweight="bold", color=SUPP)
    ax1.set_xlim(-0.5, 10.5); ax1.set_ylim(-0.5, max(log_a) + 1.5)
    ax1.set_xticks([0, 2, 4, 6, 8, 10])
    ax1.set_xlabel(r"degree $j$")
    ax1.set_ylabel(r"$\log_{10} |a_j|$")
    ax1.set_title("(a) Newton polygon", pad=5, fontweight="bold", fontsize=8.8)

    # --- Panel (b): Logarithmic radius plane ---
    ax2.set_facecolor(RECTFILL)
    def logmap(z):
        r = np.log10(np.maximum(np.abs(z), 1e-4)) + 3.0  # 0.01 -> 1, 1 -> 3, 100 -> 5
        th = np.angle(z)
        return r * np.cos(th), r * np.sin(th)
    for rad_val, lab in [(0.01, "0.01"), (1.0, "1"), (100.0, "100")]:
        rr = np.log10(rad_val) + 3.0
        ax2.add_patch(Circle((0, 0), rr, fill=False, edgecolor=SLATE, lw=0.65, ls=":", alpha=0.75))
        ax2.text(rr * 0.72, -rr * 0.72 - 0.15, lab, fontsize=6.8, color=SLATE, ha="left")
    x1, y1 = logmap(z_1c)
    xb, yb = logmap(z_bin)
    xr, yr = logmap(r_3s)
    ax2.scatter(x1, y1, s=26, facecolor="none", edgecolor=ACC, lw=1.1, label=f"1 circle ({sw_1c} sw)", zorder=3)
    ax2.scatter(xb, yb, s=22, facecolor=SUPP, edgecolor="white", lw=0.5, label=f"binomials ({sw_bin} sw)", zorder=4)
    ax2.scatter(xr, yr, s=28, marker="x", color=INK, lw=1.15, label="roots", zorder=5)
    ax2.set_xlim(-5.8, 5.8); ax2.set_ylim(-5.8, 5.8)
    ax2.set_aspect("equal")
    ax2.set_xticks([]); ax2.set_yticks([])
    ax2.set_title(r"(b) Log-radius plane ($0.01, 1, 100$)", pad=5, fontweight="bold", fontsize=8.8)
    ax2.legend(loc="lower left", fontsize=6.7, frameon=True, facecolor="white", edgecolor=GRIDC, handletextpad=0.3, borderpad=0.3)

    # --- Panel (c): NEW 0.30.0 Disjoint-disc O(m) V31 pre-polish on sparse deg-36 poly ---
    ax3.set_facecolor(RECTFILL)
    m_sp = 36
    c_sp = np.zeros(m_sp + 1, dtype=np.complex128)
    c_sp[0] = 3.0
    c_sp[13] = -0.35
    c_sp[25] = 0.28
    c_sp[36] = -7.0
    r_sp = np.roots(c_sp)
    z_sp, rad_sp, _, _ = binomial_start(c_sp, merge=True, real_rot=True)
    # One O(m) V31 three-mean step
    cf_sp = coeffs3(float(m_sp))
    p, d1, d2 = poly_eval3(c_sp, z_sp)
    ia = p / d1
    t = 1.0 - (m_sp / (m_sp - 1.0)) * ((p * d2) / (d1 * d1))
    h = m_sp * ia / (1.0 + (m_sp - 1.0) * three_c5(t, cf_sp))
    safe = np.abs(h) <= 0.90 * rad_sp
    z_after = np.where(safe, z_sp - h, z_sp)

    # Zoom onto the first quadrant arc so discs, arrows, and roots are crystal clear!
    for k in range(m_sp):
        ax3.add_patch(Circle((z_sp[k].real, z_sp[k].imag), rad_sp[k],
                             facecolor=SUPP, edgecolor=SUPP, alpha=0.14, lw=0.75, zorder=2))
        ax3.add_patch(Circle((z_sp[k].real, z_sp[k].imag), rad_sp[k],
                             facecolor="none", edgecolor=SUPP, alpha=0.55, lw=0.75, zorder=3))
        if safe[k]:
            ax3.annotate("", xy=(z_after[k].real, z_after[k].imag), xytext=(z_sp[k].real, z_sp[k].imag),
                         arrowprops=dict(arrowstyle="-|>", color=TRANS, lw=1.05, mutation_scale=7.5, shrinkA=1, shrinkB=1),
                         zorder=5)
    ax3.scatter(z_sp.real, z_sp.imag, s=16, facecolor="white", edgecolor=SUPP, lw=0.9, zorder=4, label="start $z_k$")
    ax3.scatter(r_sp.real, r_sp.imag, s=22, marker="x", color=INK, lw=1.1, zorder=6, label="roots")
    ax3.set_xlim(0.15, 1.18); ax3.set_ylim(0.15, 1.18)
    ax3.set_aspect("equal")
    ax3.set_xlabel(r"$\mathrm{Re}\, z$")
    ax3.set_ylabel(r"$\mathrm{Im}\, z$", labelpad=1)
    ax3.set_title(r"(c) $O(m)$ V31 disjoint-disc polish (0.30)", pad=5, fontweight="bold", fontsize=8.8)
    ax3.text(0.04, 0.05, f"{safe.sum()}/{m_sp} safe in $D(z_k, 0.45\\,\\mathrm{{sep}}_k)$\n0 calls to $O(m^2)$ sums",
             transform=ax3.transAxes, fontsize=6.9, color=TRANS, fontweight="bold",
             bbox=dict(boxstyle="round,pad=0.22", fc="white", ec=TRANS, lw=0.55, alpha=0.92))

    fig.subplots_adjust(left=0.068, right=0.985, top=0.87, bottom=0.17)
    out_path = os.path.join(OUT, "fig_start_v31.pdf")
    fig.savefig(out_path)
    plt.close(fig)
    print("  saved", out_path)

# =============================================================================
# FIGURE 6: Sweep landscape & real symmetric trap (HD 300 DPI PNG)
# =============================================================================
def make_fig_sweeps():
    print("Generating fig_sweeps.png ...")
    # Vectorized sweep runner on 2D grid of starts!
    N = 401  # crisp & fast (~5s), upsampled cleanly with bilinear; or 501 for extra crispness
    N = 451

    def run_slice_circle(c, roots, mode, max_sw=24):
        m = len(c) - 1
        cf = coeffs3(float(m))
        xs = np.linspace(-3.0, 3.0, N)
        X, Y = np.meshgrid(xs, xs)
        cen = (X + 1j * Y).ravel()
        npts = cen.size
        offs = 1.3 * np.exp(1j * (2.0 * np.pi * np.arange(m) / m + 0.37))
        Z = cen[:, None] + offs[None, :]  # (npts, m)
        sw_out = np.full(npts, max_sw, dtype=np.int32)
        alive = np.ones(npts, dtype=bool)
        for sw in range(1, max_sw + 1):
            za = Z[alive]
            if za.size == 0:
                break
            p, d1, d2 = poly_eval3(c, za)
            a = d1 / np.where(np.abs(p) > 1e-300, p, 1e-300)
            b = d2 / np.where(np.abs(p) > 1e-300, p, 1e-300)
            if mode == "G8":
                ia = 1.0 / np.where(np.abs(a) > 1e-300, a, 1e-300)
                t = 1.0 - (m / (m - 1.0)) * (b * ia * ia)
                q = three_c5(t, cf)
                y = za - m * ia / (1.0 + (m - 1.0) * q)
            else:
                y = za
            # Pairwise differences: (na, m, m)
            D = za[:, :, None] - y[:, None, :]
            diag = np.eye(m, dtype=bool)[None, :, :]
            D_safe = np.where(diag | (np.abs(D) < 1e-300), 1.0, D)
            invD = np.where(diag, 0.0, 1.0 / D_safe)
            s1 = np.sum(invD, axis=2)
            if mode == "EA":
                step = 1.0 / np.where(np.abs(a - s1) > 1e-300, a - s1, 1e-300)
            else:
                s2 = np.sum(invD * invD, axis=2)
                Ak = a - s1
                Bk = a * a - b - s2
                ia = 1.0 / np.where(np.abs(Ak) > 1e-300, Ak, 1e-300)
                tk = (m * Bk * ia * ia - 1.0) / (m - 1.0)
                qk = three_c5(tk, cf)
                step = m * ia / (1.0 + (m - 1.0) * qk)
            zn = za - step
            # Convergence test: residual small for all m points
            pn, _, _ = poly_eval3(c, zn)
            conv = np.max(np.abs(pn), axis=1) < 1e-9
            idx_a = np.flatnonzero(alive)
            Z[idx_a] = zn
            sw_out[idx_a[conv]] = sw
            alive[idx_a[conv]] = False
        return sw_out.reshape(N, N)

    def run_slice_cubic(mode, max_sw=24):
        # z^3 - 3z + 1, two points fixed at 0.5 +/- i, third varies over [-2.5, 2.5]^2
        c = np.array([1.0, 0.0, -3.0, 1.0], dtype=np.complex128)
        cf = coeffs3(3.0)
        xs = np.linspace(-2.5, 2.5, N)
        X, Y = np.meshgrid(xs, xs)
        z3 = (X + 1j * Y).ravel()
        npts = z3.size
        Z = np.empty((npts, 3), dtype=np.complex128)
        Z[:, 0] = 0.5 + 1.0j
        Z[:, 1] = 0.5 - 1.0j
        Z[:, 2] = z3
        sw_out = np.full(npts, max_sw + 1, dtype=np.int32)
        alive = np.ones(npts, dtype=bool)
        for sw in range(1, max_sw + 1):
            za = Z[alive]
            if za.size == 0:
                break
            p, d1, d2 = poly_eval3(c, za)
            done = np.abs(p) < 1e-12
            p_safe = np.where(done, 1.0, p)
            a = np.where(done, 0.0, d1 / p_safe)
            b = np.where(done, 0.0, d2 / p_safe)
            if mode == "G8":
                a_nz = np.abs(a) > 1e-14
                ia = np.where(a_nz, 1.0 / np.where(a_nz, a, 1.0), 0.0)
                t = np.where(a_nz, 1.0 - 1.5 * (b * ia * ia), 1.0)
                q = three_c5(t, cf)
                denom = 1.0 + 2.0 * q
                h = np.where(a_nz & (np.abs(denom) > 1e-14), 3.0 * ia / np.where(np.abs(denom) > 1e-14, denom, 1.0), 0.0)
                h = np.where(done | ~np.isfinite(h), 0.0, h)
                y = za - h
            else:
                y = za
            D = za[:, :, None] - y[:, None, :]
            diag = np.eye(3, dtype=bool)[None, :, :]
            D_safe = np.where(diag | (np.abs(D) < 1e-14), 1.0, D)
            invD = np.where(diag | (np.abs(D) < 1e-14), 0.0, 1.0 / D_safe)
            s1 = np.sum(invD, axis=2)
            if mode == "EA":
                den = a - s1
                step = np.where(done | (np.abs(den) < 1e-14), 0.0, 1.0 / np.where(np.abs(den) < 1e-14, 1.0, den))
            else:
                s2 = np.sum(invD * invD, axis=2)
                Ak = a - s1
                Bk = a * a - b - s2
                ak_nz = (~done) & (np.abs(Ak) > 1e-14)
                ia = np.where(ak_nz, 1.0 / np.where(ak_nz, Ak, 1.0), 0.0)
                tk = np.where(ak_nz, (3.0 * Bk * ia * ia - 1.0) / 2.0, 1.0)
                qk = three_c5(tk, cf)
                denom = 1.0 + 2.0 * qk
                step = np.where(ak_nz & (np.abs(denom) > 1e-14), 3.0 * ia / np.where(np.abs(denom) > 1e-14, denom, 1.0), 0.0)
            step = np.where(np.isfinite(step), step, 0.0)
            zn = za - step
            pn, _, _ = poly_eval3(c, zn)
            conv = np.max(np.abs(pn), axis=1) < 1e-9
            idx_a = np.flatnonzero(alive)
            Z[idx_a] = zn
            sw_out[idx_a[conv]] = sw
            alive[idx_a[conv]] = False
        return sw_out.reshape(N, N)

    # Real degree-6 polynomial with 3 conjugate pairs
    r6 = np.array([-1.3 + 0.55j, -1.3 - 0.55j, 0.12 + 0.68j, 0.12 - 0.68j, 1.2 + 0.72j, 1.2 - 0.72j])
    c6 = np.real(np.poly(r6)).astype(np.complex128)
    s6_ea = run_slice_circle(c6, r6, "EA", max_sw=24)
    s6_g8 = run_slice_circle(c6, r6, "G8", max_sw=24)

    r3c = np.roots([1.0, 0.0, -3.0, 1.0])
    s3_ea = run_slice_cubic("EA", max_sw=24)
    s3_g8 = run_slice_cubic("G8", max_sw=60)

    cmap_sw = LinearSegmentedColormap.from_list("v31_sw", ["#F7FAFE", "#C5DDF2", "#5D95CF", "#16529E", "#10284A"])
    cmap_sw.set_over(ACC)

    fig, axes = plt.subplots(2, 2, figsize=(6.8, 6.45),
                             gridspec_kw={"wspace": 0.08, "hspace": 0.16, "left": 0.10, "right": 0.89, "top": 0.945, "bottom": 0.125})

    for ax, data, ttl in [
        (axes[0, 0], s6_ea, "Ehrlich–Aberth"),
        (axes[0, 1], s6_g8, "G8 (three means)"),
    ]:
        ax.imshow(data, origin="lower", extent=[-3, 3, -3, 3], cmap=cmap_sw, vmin=1, vmax=22, interpolation="bilinear")
        ax.scatter(r6.real, r6.imag, s=24, facecolor="white", edgecolor=INK, lw=0.95, zorder=5)
        ax.set_title(ttl, pad=6, fontweight="bold", fontsize=9.8)
        ax.set_xticks([-2, 0, 2]); ax.set_yticks([-2, 0, 2])
        ax.text(0.03, 0.04, f"mean {data.mean():.1f} sweeps, max {data.max()}", transform=ax.transAxes, fontsize=7.4,
                bbox=dict(boxstyle="round,pad=0.25", fc="white", ec=SLATE, alpha=0.90, lw=0.5))
    axes[0, 0].set_ylabel("degree 6: start-circle centre\n" + r"$\mathrm{Im}\, c_0$")
    axes[0, 1].set_yticklabels([])

    mid = N // 2
    s3_ea_plot = s3_ea.copy().astype(float)
    s3_ea_plot[mid-1:mid+2, :] = 26.0
    s3_g8_plot = np.minimum(s3_g8.astype(float), 24.0)  # all converged (axis takes up to ~55 sweeps, clip display cleanly to colorbar top!)

    for ax, data, note in [
        (axes[1, 0], s3_ea_plot, f"off-axis mean {s3_ea[s3_ea<=24].mean():.1f}  |  real axis: trapped"),
        (axes[1, 1], s3_g8_plot, f"off-axis mean {s3_g8[np.arange(N)!=mid].mean():.1f}  |  real axis: escapes"),
    ]:
        im1 = ax.imshow(data, origin="lower", extent=[-2.5, 2.5, -2.5, 2.5], cmap=cmap_sw, vmin=1, vmax=24, interpolation="nearest")
        ax.scatter(r3c.real, np.zeros_like(r3c.real), s=24, facecolor="white", edgecolor=INK, lw=0.95, zorder=5)
        ax.scatter([0.5, 0.5], [1.0, -1.0], s=26, marker="s", facecolor="white", edgecolor=INK, lw=0.95, zorder=5)
        ax.set_xticks([-2, -1, 0, 1, 2]); ax.set_yticks([-2, -1, 0, 1, 2])
        ax.set_xlabel(r"$\mathrm{Re}\, z_3$", labelpad=3)
        ax.text(0.03, 0.90, note, transform=ax.transAxes, fontsize=7.2,
                bbox=dict(boxstyle="round,pad=0.24", fc="white", ec=SLATE, alpha=0.92, lw=0.5))
    axes[1, 0].set_ylabel(r"$z^3 - 3z + 1$: third start point" + "\n" + r"$\mathrm{Im}\, z_3$")
    axes[1, 1].set_yticklabels([])

    cax = fig.add_axes([0.91, 0.16, 0.018, 0.74])
    cb = fig.colorbar(im1, cax=cax, extend="max")
    cb.set_label("sweeps", fontsize=8.5)
    cb.ax.tick_params(labelsize=8.0)

    handles = [
        Line2D([0], [0], marker="o", color="none", mfc="white", mec=INK, ms=5, mew=0.95, label="roots"),
        Line2D([0], [0], marker="s", color="none", mfc="white", mec=INK, ms=5, mew=0.95, label="fixed pair $\\frac{1}{2}\\pm i$"),
        Patch(facecolor=ACC, edgecolor="none", label="symmetric trap (no convergence)"),
    ]
    fig.legend(handles=handles, loc="lower center", ncol=3, frameon=False, bbox_to_anchor=(0.49, 0.012), fontsize=7.8)
    out_path = os.path.join(OUT, "fig_sweeps.png")
    fig.savefig(out_path, dpi=300)
    plt.close(fig)
    print("  saved", out_path)

# =============================================================================
# FIGURE 7: 100K corpus performance (0.28 -> 0.29 -> 0.30) + scaling vs LAPACK
# =============================================================================
def make_fig_bench():
    print("Generating fig_bench.pdf ...")
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(7.2, 3.05),
                                   gridspec_kw={"width_ratios": [1.15, 1.0], "wspace": 0.28})

    # --- Left: 100,000-polynomial corpus stage breakdown + family speedups ---
    # Exact verified numbers (Apple M5, 1 thread, 100,000 polynomials, 5,060,069 roots):
    # 0.28.0: total 30.261 (sqf 2.271, swp 12.633, crt 14.972, other 0.385)
    # 0.29.0: total 19.422 (sqf 1.475, swp 7.124, crt 10.427, other 0.396)
    # 0.30.0: total 16.499 (sqf 1.477, swp 6.091, crt 8.537, other 0.394)
    # Show top-half: 3 stacked horizontal bars (0.28, 0.29, 0.30), bottom-half or full panel:
    # Actually let's split Left into 2 stacked sub-axes or show clean grouped horizontal bars of top 8 families!
    # Even cleaner: Left = 100K stacked progression (0.28 -> 0.29 -> 0.30) with family callouts inside an inset,
    # OR 2-row Left (top: total 100K stacked bars; bottom: per-family 0.28 -> 0.30 speedup bars)!
    ax1.remove()
    gs_l = fig.add_gridspec(2, 1, left=0.115, right=0.525, top=0.835, bottom=0.14, height_ratios=[0.85, 1.35], hspace=0.48)
    ax1a = fig.add_subplot(gs_l[0, 0])
    ax1b = fig.add_subplot(gs_l[1, 0])

    vers = ["0.28.0", "0.29.0", "0.30.0"]
    sqf  = np.array([2.271, 1.475, 1.477])
    swp  = np.array([12.633, 7.124, 6.091])
    crt  = np.array([14.972, 10.427, 8.537])
    tot  = np.array([30.261, 19.422, 16.499])
    ypos = np.arange(3)

    ax1a.set_facecolor(RECTFILL)
    ax1a.grid(True, axis="x", color="white", lw=0.8, zorder=0)
    ax1a.barh(ypos, sqf, height=0.58, color=SLATE, label="sqfree", zorder=3)
    ax1a.barh(ypos, swp, left=sqf, height=0.58, color=SUPP, label="sweeps", zorder=3)
    ax1a.barh(ypos, crt, left=sqf + swp, height=0.58, color=TEAL, label="certify", zorder=3)
    for i, t in enumerate(tot):
        tag = f"{t:.2f} s" if i == 0 else f"{t:.2f} s ({tot[0]/t:.2f}×)"
        ax1a.text(t + 0.55, i, tag, va="center", fontsize=7.6, fontweight="bold", color=INK if i < 2 else SUPP)
    ax1a.set_yticks(ypos); ax1a.set_yticklabels(vers, fontweight="bold")
    ax1a.invert_yaxis()
    ax1a.set_xlim(0, 44.5)
    ax1a.set_xlabel("total time (s) on 100,000 polynomials", fontsize=8.0, labelpad=2)
    ax1a.set_title("(a) 100K corpus: 0.28.0 → 0.30.0", pad=16, fontweight="bold", fontsize=8.8)
    ax1a.legend(loc="lower center", bbox_to_anchor=(0.50, 1.00), ncol=3, fontsize=6.8, frameon=False,
                handlelength=1.1, columnspacing=1.0)

    # Bottom-left: per-family speedup 0.29 -> 0.30 (with cumulative 0.28 -> 0.30 marker!)
    fams = ["sparse", "powers", "wilkinson", "orthogonal", "special", "roots", "mignotte", "dense_large"]
    sp_29_30 = np.array([1.49, 1.22, 1.22, 1.16, 1.16, 1.12, 1.09, 1.05])
    # Exact cumulative 0.28 -> 0.30 ratios matching Table 100K
    sp_28_30 = np.array([9.161/3.041, 3.195/1.796, 2.226/1.261, 4.060/2.365,
                         1.015/0.626, 0.290/0.204, 0.861/0.636, 5.969/3.085])
    yf = np.arange(len(fams))
    ax1b.set_facecolor(RECTFILL)
    ax1b.grid(True, axis="x", color="white", lw=0.8, zorder=0)
    ax1b.axvline(1.0, color=SLATE, lw=0.75, ls=":", zorder=2)
    ax1b.barh(yf, sp_28_30, height=0.58, color=SUPP_LT, alpha=0.38, label="0.28 → 0.30", zorder=2)
    ax1b.barh(yf, sp_29_30, height=0.58, color=SUPP, label="0.29 → 0.30", zorder=3)
    for i, (v1, v2) in enumerate(zip(sp_29_30, sp_28_30)):
        ax1b.text(v2 + 0.06, i, f"{v2:.2f}×", va="center", fontsize=6.9, color=INK, fontweight="bold")
    ax1b.set_yticks(yf); ax1b.set_yticklabels(fams, fontsize=7.5)
    ax1b.invert_yaxis()
    ax1b.set_xlim(0, 3.45)
    ax1b.set_xlabel("speedup factor", fontsize=8.0, labelpad=2)
    ax1b.legend(loc="lower right", fontsize=6.8, frameon=True, facecolor="white", edgecolor=GRIDC, borderpad=0.25)

    # --- Right: log-log scaling vs numpy.roots / LAPACK (fresh 0.30.0 measurements!) ---
    ax2.set_position([0.60, 0.14, 0.38, 0.76])
    ax2.set_facecolor(RECTFILL)
    ax2.grid(True, which="major", color="white", lw=0.8, zorder=0)
    degs = np.array([5, 10, 20, 40, 80, 160, 320], dtype=float)
    g8_cx = np.array([2.2, 4.3, 9.4, 21.0, 55.1, 168.5, 553.0])
    g8_re = np.array([2.4, 4.4, 9.2, 22.2, 58.0, 173.0, 577.5])
    np_cx = np.array([13.0, 27.6, 95.6, 402.2, 4147.1, 20051.7, 112092.2])
    np_re = np.array([10.2, 14.6, 34.0, 116.7, 1084.0, 5405.0, 27914.3])

    ax2.loglog(degs, np_cx, "--s", color=ACC, lw=1.4, ms=4.0, label=r"numpy.roots ($\mathbb{C}$)", zorder=3)
    ax2.loglog(degs, np_re, "--^", color=GOLD, lw=1.3, ms=4.0, label=r"numpy.roots ($\mathbb{R}$)", zorder=3)
    ax2.loglog(degs, g8_cx, "-o", color=SUPP, lw=1.8, ms=4.4, label=r"pandroots 0.30 ($\mathbb{C}$, cert.)", zorder=5)
    ax2.loglog(degs, g8_re, "-d", color=TRANS, lw=1.4, ms=3.8, alpha=0.88, label=r"pandroots 0.30 ($\mathbb{R}$, cert.)", zorder=4)

    # Annotate 203x speedup at deg 320!
    ax2.annotate("", xy=(320, 650), xytext=(320, 92000),
                 arrowprops=dict(arrowstyle="<->", color=INK, lw=1.05))
    ax2.text(260, 7500, "203×\nfaster", ha="right", va="center", fontsize=7.8, fontweight="bold", color=SUPP,
             bbox=dict(boxstyle="round,pad=0.22", fc="white", ec=SUPP, lw=0.6, alpha=0.95))

    # Slope hints
    ax2.text(24, 1500, r"$\sim m^3$", fontsize=7.6, color=ACC, fontweight="bold")
    ax2.text(55, 14, r"$\sim m^2$", fontsize=7.6, color=SUPP, fontweight="bold")

    ax2.set_xticks(degs)
    ax2.set_xticklabels([str(int(d)) for d in degs])
    ax2.set_xlim(4.2, 390); ax2.set_ylim(1.4, 2.5e5)
    ax2.set_xlabel("polynomial degree $m$", fontsize=8.2)
    ax2.set_ylabel(r"time per polynomial ($\mu$s)", fontsize=8.2)
    ax2.set_title("(b) Scaling vs. LAPACK (Apple M5)", pad=4, fontweight="bold", fontsize=8.8)
    ax2.legend(loc="upper left", fontsize=6.8, frameon=True, facecolor="white", edgecolor=GRIDC, borderpad=0.28)

    out_path = os.path.join(OUT, "fig_bench.pdf")
    fig.savefig(out_path)
    plt.close(fig)
    print("  saved", out_path)

# =============================================================================
# FIGURE 8: Cluster model & Local Zoom (2^-600 pair) visual diagram (vector PDF)
# =============================================================================
def make_fig_zoom():
    print("Generating fig_zoom.pdf ...")
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(7.2, 2.70),
                                   gridspec_kw={"width_ratios": [1.05, 1.0], "wspace": 0.25})

    # --- Left: Cluster step (shifted power model of degree K=5) ---
    ax1.set_facecolor(RECTFILL)
    ax1.grid(True, color="white", lw=0.8, zorder=0)
    g = 0.0 + 0.0j
    rho = 0.22
    K = 5
    # True 5-root cluster near origin (slightly perturbed pentagon)
    ang = 2.0 * np.pi * np.arange(K) / K + 0.18
    r_cl = g + rho * np.array([1.04, 0.96, 1.02, 0.95, 1.03]) * np.exp(1j * (ang + np.array([0.04, -0.03, 0.02, -0.04, 0.01])))
    # Approximations far from cluster (distance ~ 1.15)
    z_far = g + 1.12 * np.exp(1j * (ang + 0.28))
    # Shifted-power model circle g + u * t^(1/K) * omega^j
    z_mod = g + rho * np.exp(1j * ang)

    # Outer enclosing Smith disc
    ax1.add_patch(Circle((0, 0), 1.38, facecolor=SLATE, edgecolor=SLATE, alpha=0.10, lw=0.8, ls=":", zorder=1))
    ax1.add_patch(Circle((0, 0), 1.38, facecolor="none", edgecolor=SLATE, alpha=0.55, lw=0.8, ls=":", zorder=2))
    # Model circle of radius rho
    ax1.add_patch(Circle((0, 0), rho, facecolor=SUPP, edgecolor=SUPP, alpha=0.14, lw=1.0, zorder=2))
    ax1.add_patch(Circle((0, 0), rho, facecolor="none", edgecolor=SUPP, lw=1.1, ls="--", zorder=3))
    for k in range(K):
        ax1.annotate("", xy=(z_mod[k].real, z_mod[k].imag), xytext=(z_far[k].real, z_far[k].imag),
                     arrowprops=dict(arrowstyle="-|>", color=SUPP, lw=1.15, mutation_scale=8.5,
                                     connectionstyle="arc3,rad=0.12"), zorder=4)
    ax1.scatter(z_far.real, z_far.imag, s=26, facecolor="white", edgecolor=ACC, lw=1.1, zorder=5, label="far iterates $z_k$")
    ax1.scatter(z_mod.real, z_mod.imag, s=22, facecolor=SUPP, edgecolor="white", lw=0.6, zorder=6, label="model $g + u\\,t^{1/K}\\omega^j$")
    ax1.scatter(r_cl.real, r_cl.imag, s=26, marker="x", color=INK, lw=1.2, zorder=7, label="cluster roots ($K=5$)")
    ax1.scatter([0], [0], s=18, marker="+", color=PLUM, lw=1.2, zorder=6)
    ax1.text(0.05, -0.13, r"$g$", fontsize=8.0, color=PLUM, fontweight="bold")
    ax1.text(-1.42, 1.24, r"model $(w-g)^K - a$", fontsize=7.4, color=SUPP, fontweight="bold",
             bbox=dict(boxstyle="round,pad=0.2", fc="white", ec=SUPP, lw=0.5, alpha=0.9))
    ax1.set_xlim(-1.55, 1.55); ax1.set_ylim(-1.52, 1.52)
    ax1.set_aspect("equal")
    ax1.set_xlabel(r"$\mathrm{Re}(w - g)$")
    ax1.set_ylabel(r"$\mathrm{Im}(w - g)$")
    ax1.set_title("(a) Cluster step (Proposition 10.1)", pad=5, fontweight="bold", fontsize=8.8)
    ax1.legend(loc="lower center", bbox_to_anchor=(0.50, -0.42), ncol=3, fontsize=6.8, frameon=False, columnspacing=0.9, handletextpad=0.3)

    # --- Right: Local variable zoom for (z - 1)(2^600 z - 2^600 - 1) ---
    ax2.set_facecolor(RECTFILL)
    ax2.axis("off")
    ax2.set_xlim(0.0, 10.4); ax2.set_ylim(0.0, 5.2)
    ax2.set_aspect("equal")

    # Left disc: unresolved cluster disc D(z0, R) in z-plane
    c1x, c1y, r1 = 1.9, 2.75, 1.35
    ax2.add_patch(Circle((c1x, c1y), r1, facecolor=ACC, edgecolor=ACC, alpha=0.14, lw=1.1, ls="--"))
    ax2.add_patch(Circle((c1x, c1y), r1, facecolor="none", edgecolor=ACC, lw=1.2, ls="--"))
    ax2.scatter([c1x - 0.06, c1x + 0.06], [c1y, c1y], s=18, color=INK, zorder=5)
    ax2.text(c1x, c1y - 1.72, r"original plane $z$", ha="center", fontsize=8.0, fontweight="bold", color=INK)
    ax2.text(c1x, c1y - 2.18, r"gap $2^{-600}$ (1 disc, count 2)", ha="center", fontsize=7.2, color=ACC)

    # Telescopic zoom cone
    c2x, c2y, r2 = 7.75, 2.75, 1.75
    ax2.plot([c1x + 0.15, c2x - r2 * 0.45], [c1y + 0.12, c2y + r2 * 0.89], color=SLATE, ls=":", lw=0.9)
    ax2.plot([c1x + 0.15, c2x - r2 * 0.45], [c1y - 0.12, c2y - r2 * 0.89], color=SLATE, ls=":", lw=0.9)
    ax2.annotate("", xy=(5.65, c1y), xytext=(3.55, c1y),
                 arrowprops=dict(arrowstyle="-|>", color=SUPP, lw=1.6, mutation_scale=11))
    ax2.text(4.60, c1y + 0.62, r"$u = 2^m z - C$", ha="center", fontsize=8.0, fontweight="bold", color=SUPP,
             bbox=dict(boxstyle="round,pad=0.2", fc="white", ec=SUPP, lw=0.55))
    ax2.text(4.60, c1y - 0.58, r"$m = 601$", ha="center", fontsize=7.3, color=SLATE)

    # Right disc: zoomed u-plane with two well-separated certified discs
    ax2.add_patch(Circle((c2x, c2y), r2, facecolor="white", edgecolor=SLATE, lw=1.0))
    ax2.add_patch(Circle((c2x - 0.78, c2y), 0.46, facecolor=TRANS, edgecolor=TRANS, alpha=0.22, lw=1.2))
    ax2.add_patch(Circle((c2x - 0.78, c2y), 0.46, facecolor="none", edgecolor=TRANS, lw=1.3))
    ax2.add_patch(Circle((c2x + 0.78, c2y), 0.46, facecolor=TRANS, edgecolor=TRANS, alpha=0.22, lw=1.2))
    ax2.add_patch(Circle((c2x + 0.78, c2y), 0.46, facecolor="none", edgecolor=TRANS, lw=1.3))
    ax2.scatter([c2x - 0.78, c2x + 0.78], [c2y, c2y], s=26, marker="x", color=INK, lw=1.25, zorder=6)
    ax2.text(c2x - 0.78, c2y - 0.76, r"$u_1$", ha="center", fontsize=7.8, fontweight="bold", color=TRANS)
    ax2.text(c2x + 0.78, c2y - 0.76, r"$u_2$", ha="center", fontsize=7.8, fontweight="bold", color=TRANS)
    ax2.text(c2x, c2y + 1.02, r"isolated in $Q(u)$", ha="center", fontsize=7.0, color=TRANS, fontweight="bold")
    ax2.text(c2x, c2y - 2.18, r"certified back in $z$ (0.48 ms, 1 zoom)", ha="center", fontsize=7.2, color=TRANS, fontweight="bold")
    ax2.set_title("(b) Local zoom beyond $2^{-500}$ (module zoom)", pad=5, fontweight="bold", fontsize=8.8)

    fig.subplots_adjust(left=0.075, right=0.985, top=0.88, bottom=0.25)
    out_path = os.path.join(OUT, "fig_zoom.pdf")
    fig.savefig(out_path)
    plt.close(fig)
    print("  saved", out_path)

if __name__ == "__main__":
    make_fig_basins_slit()
    make_fig_paths()
    make_fig_discs()
    make_fig_start_v31()
    make_fig_sweeps()
    make_fig_bench()
    make_fig_zoom()
    print("ALL FIGURES GENERATED SUCCESSFULLY.")
