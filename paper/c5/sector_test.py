"""High-precision test of the sector theorem (natural branch, beta = 5 pi/6, p >= 3)."""
import random
from mpmath import mp, mpf, mpc, sqrt, log, exp, pi, fabs, tanh, im, re, arg
mp.dps = 300
random.seed(21)
BETA = 5*pi/6
def coeffs(p):
    h = 1/mpf(p)
    return (1-2*h)/12, (1+h)*(3+h)/30, (121-185*h-67*h**2-h**3)/(840*(3+h))
def mfun(name, p, w):
    a, b, c = coeffs(p)
    if name == 'arc': return sqrt(1+a*w)
    return sqrt(1+a*w/sqrt(1+b*w/(1+c*w)))
def Lam(name, p, x):
    z = exp(x/2); w = exp(x) + exp(-x) - 2
    M = (p-1)*mfun(name, p, w)
    return x - p*(log(z + M) - log(1/z + M))
zeta = lambda x: tanh(3*x/10)
for name, m in [('arc', 5), ('nest', 9)]:
    worst = mpf(100); inside = True; maxim = mpf(0)
    for p in [3, mpf('3.5'), 4, 5, 7, 12, 40, 1000]:
        for _ in range(700):
            x = mpc(random.uniform(-8, 8), random.uniform(-1, 1)*float(BETA)*0.9999)
            y = Lam(name, p, x)
            inside = inside and fabs(im(y)) < BETA
            maxim = max(maxim, fabs(im(y))/BETA)
            worst = min(worst, log(fabs(zeta(y)))/log(fabs(zeta(x))))
    print(f"{name}: image inside the strip: {inside} (max |Im Lam|/beta = {float(maxim):.4f}); min log|zeta+|/log|zeta| = {float(worst):.4f} (claim >= {m})")
