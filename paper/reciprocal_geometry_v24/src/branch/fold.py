"""Reproduce the V20 fold, with both positive inverse roots explicitly marked."""
from pathlib import Path
import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

OUT = Path(__file__).resolve().parents[2] / "figures"
blue, orange, gray = "#176B9B", "#BD5A20", "#A9B4BC"
plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 11, "pdf.fonttype": 42})
p = 3
A, B, C = (p + 1) * (p + 2), p * p - 4, (p - 1) * (p - 2)


def model(v):
    return (C * v * v - 2 * B * v + A) / (A * v * v - 2 * B * v + C)


vm = (p * p + 2 - np.sqrt(12 * (p * p - 1))) / (p * p - 4)
vp = 1 / vm
t = .05
roots = np.sort(np.roots([C - t * A, -2 * B * (1 - t), A - t * C]))
assert np.all(roots > 0) and vm < roots[0] < vp < roots[1]
assert np.allclose(model(roots), t, rtol=1e-12)
assert np.isclose(model(1), 1)
fig, ax = plt.subplots(figsize=(8.7, 2.75), layout="constrained")
for lo, hi in [(.055, vm), (vp, 20)]:
    v = np.geomspace(lo, hi, 500)
    ax.plot(np.log(v), np.log(model(v)), color=gray, lw=1.6)
v = np.geomspace(vm, vp, 800)
ax.plot(np.log(v), np.log(model(v)), color=blue, lw=2.3)
ax.axhline(np.log(t), color=orange, lw=1, ls="--")
ax.scatter(np.log([vm, vp]), np.log(model(np.array([vm, vp]))), s=36,
           facecolors="white", edgecolors=blue, zorder=4)
ax.scatter([0], [0], color=blue, s=24, zorder=5)
ax.annotate("v = t = 1", (0, 0), xytext=(11, 10), textcoords="offset points")
ax.scatter(np.log(roots), np.log([t, t]), s=30, color=[blue, orange], zorder=5)
for root, label, offset, color in [
    (roots[0], "Selected: 3.1183", (-180, 14), blue),
    (roots[1], "Rejected: 6.3817", (12, 26), orange),
]:
    ax.annotate(label, (np.log(root), np.log(t)), xytext=offset,
                textcoords="offset points", color=color, fontsize=10,
                arrowprops={"arrowstyle": "-", "color": color, "lw": .7})
ax.text(-2.65, np.log(t) + .18, "t = 0.05", color=orange, fontsize=10)
ax.text(-2.7, 1.9, "Other branch", color="#65727A", fontsize=10)
ax.text(-.15, 1.55, "Descending branch", color=blue, fontsize=10)
ax.set(xlim=(-2.9, 3.1), ylim=(-3.6, 3.6), xlabel="log v", ylabel="log R(v)")
ax.grid(alpha=.14)
for suffix in ["pdf", "png"]:
    fig.savefig(OUT / f"branch_fold.{suffix}", dpi=180)
plt.close(fig)
print("PASS: fold figure selects the descending root and rejects the other positive root")
