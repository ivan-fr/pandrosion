"""Interval-arithmetic certificate for the boundary inequality (U) of the half-plane theorem.

On the boundary t = i*y of the right half-plane put nu = y - 1/y, w = -2 + i*nu, h = 1/p.
For a reciprocal support q = sqrt(t)*m(w) the inequality  arg(phi(i y)) <= pi/p  follows from
    G(h, nu) = pi*(1-h)*|m|^2 - (1 - pi*h)*R - h/(1-h) >= 0,   R = Re sqrt(m^2 * (w+4)),
(see the paper, proof of the half-plane theorem).  By the symmetry y -> 1/y only nu >= 0 is needed.
This script proves G > 0 on  0 <= h <= 1/pi, nu >= 0  by adaptive subdivision with outward-rounded
interval arithmetic (mpmath.iv), in two charts: nu in [0, V] and s = 1/nu in [0, 1/V] (scaled by s).
The range 1/pi <= h <= 1/2 is covered by the analytic bound stated in the paper.
"""
import sys
from mpmath import iv, mp
iv.prec = 60
PI = iv.pi
ZERO = iv.mpf(0)

def psqrt(x):                 # sqrt of an interval known to represent a nonnegative quantity
    if x.a >= 0: return iv.sqrt(x)
    if x.b <= 0: return ZERO
    return iv.sqrt(iv.mpf([0, x.b]))

class C:                      # complex interval as a pair of real intervals
    __slots__ = ('re', 'im')
    def __init__(s, re, im=ZERO): s.re, s.im = iv.mpf(re), iv.mpf(im)
    def __add__(s, o): o = cc(o); return C(s.re + o.re, s.im + o.im)
    __radd__ = __add__
    def __mul__(s, o): o = cc(o); return C(s.re*o.re - s.im*o.im, s.re*o.im + s.im*o.re)
    __rmul__ = __mul__
    def __truediv__(s, o):
        o = cc(o); d = o.re*o.re + o.im*o.im
        return C((s.re*o.re + s.im*o.im)/d, (s.im*o.re - s.re*o.im)/d)
    def abs(s): return psqrt(s.re**2 + s.im**2)
def cc(x): return x if isinstance(x, C) else C(x)
def csqrt_rhp(z):             # principal square root, requires Re z > 0
    assert z.re.a > 0
    r = iv.sqrt((z.abs() + z.re)/2)
    return C(r, z.im/(2*r))
def re_sqrt(z):               # real part of the principal square root, any z
    return psqrt((z.abs() + z.re)/2)

def coeffs(h, support):
    a = (1 - 2*h)/12
    if support == 'arc': return a, None, None
    b = (1 + h)*(3 + h)/30
    c = (121 - 185*h - 67*h*h - h*h*h)/(840*(3 + h))
    return a, b, c

def G_chart1(h, nu, support):
    a, b, c = coeffs(h, support)
    w = C(-2, nu)
    if support == 'arc':
        m2 = w*a + 1
    else:
        rho = csqrt_rhp((w*b)/(w*c + 1) + 1)
        m2 = (w*a)/rho + 1
    R = re_sqrt(m2*C(2, nu))
    return PI*(1 - h)*m2.abs() - (1 - PI*h)*R - h/(1 - h)

def G_chart2(h, s, support):   # s = 1/nu, returns s*G
    a, b, c = coeffs(h, support)
    sw = C(-2*s, 1)
    if support == 'arc':
        sm2 = sw*a + s
    else:
        rho = csqrt_rhp((sw*b)/(sw*c + s) + 1)
        sm2 = (sw*a)/rho + s
    sR = re_sqrt(sm2*C(2*s, 1))
    return PI*(1 - h)*sm2.abs() - (1 - PI*h)*sR - s*h/(1 - h)

def certify(fun, box, support, maxdepth=40):
    stack = [(box, 0)]; n = 0; worst = None
    while stack:
        (h0, h1, x0, x1), d = stack.pop()
        val = fun(iv.mpf([h0, h1]), iv.mpf([x0, x1]), support)
        n += 1
        if val.a > 0:
            worst = val.a if worst is None else min(worst, val.a); continue
        if d >= maxdepth: raise SystemExit(f'FAILED on box {(h0, h1, x0, x1)}: {val}')
        if (h1 - h0)/0.32 > (x1 - x0)/(box[3] - box[2]):
            hm = (h0 + h1)/2; stack += [((h0, hm, x0, x1), d + 1), ((hm, h1, x0, x1), d + 1)]
        else:
            xm = (x0 + x1)/2; stack += [((h0, h1, x0, xm), d + 1), ((h0, h1, xm, x1), d + 1)]
    return n, worst

if __name__ == '__main__':
    V = 32.0
    HMAX = 0.3184              # > 1/pi = 0.31831
    for support in ['arc', 'nest']:
        n1, w1 = certify(G_chart1, (0.0, HMAX, 0.0, V), support)
        n2, w2 = certify(G_chart2, (0.0, HMAX, 0.0, 1/V), support)
        print(f'{support}: chart nu in [0,{V}]: {n1} boxes, min lower bound {float(w1.a):.4f}; '
              f'chart s in [0,1/{V}]: {n2} boxes, min lower bound of s*G {float(w2.a):.5f}')
    print('CERTIFIED')
