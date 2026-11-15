"""Second, independent certificate of the boundary inequality (U): ball arithmetic (Arb, through
python-flint) instead of mpmath.iv, with native complex balls and Arb's complex square root.

Same statement as certify_halfplane.py:  G(h, nu) > 0  for  0 <= h <= 1/pi, nu >= 0, where
    G = pi (1-h) |m|^2 - (1 - pi h) Re sqrt(m^2 (w+4)) - h/(1-h),   w = -2 + i nu,
for the decentered arc and the nested support, in the charts nu in [0, V] and s = 1/nu in [0, 1/V]
(the second one for s*G)."""
from flint import arb, acb, ctx
ctx.prec = 64
PI = arb.pi()

def ball(lo, hi):
    """A ball containing [lo, hi]: midpoint and a radius inflated against rounding of the midpoint."""
    mid = (lo + hi)/2
    rad = max(hi - mid, mid - lo)*(1 + 1e-12) + 1e-300
    return arb(mid, rad)

def re_sqrt(z):
    """Real part of the principal square root: sqrt((|z| + Re z)/2), a quantity >= 0.
    Returns a ball containing it; the radicand is clipped at 0 from below."""
    x = (abs(z) + z.real)/2
    hi = float(x.upper())*(1 + 1e-12) + 1e-300       # a float above the upper end of x
    if hi <= 0: return arb(0)
    lo = max(float(x.lower())*(1 - 1e-12), 0.0)       # a float below the lower end of x, clipped
    r_hi = float(arb(hi).sqrt().upper())*(1 + 1e-12)
    r_lo = float(arb(lo).sqrt().lower())*(1 - 1e-12)
    return ball(r_lo, r_hi)

def coeffs(h, support):
    a = (1 - 2*h)/12
    if support == 'arc': return a, None, None
    b = (1 + h)*(3 + h)/30
    c = (121 - 185*h - 67*h*h - h*h*h)/(840*(3 + h))
    return a, b, c

def G1(h, nu, support):
    a, b, c = coeffs(h, support)
    w = acb(arb(-2), nu)
    if support == 'arc':
        m2 = 1 + a*w
    else:
        m2 = 1 + a*w/(1 + b*w/(1 + c*w)).sqrt()
    return PI*(1 - h)*abs(m2) - (1 - PI*h)*re_sqrt(m2*acb(arb(2), nu)) - h/(1 - h)

def G2(h, s, support):
    a, b, c = coeffs(h, support)
    sw = acb(-2*s, arb(1))
    if support == 'arc':
        sm2 = s + a*sw
    else:
        sm2 = s + a*sw/(1 + b*sw/(s + c*sw)).sqrt()
    return PI*(1 - h)*abs(sm2) - (1 - PI*h)*re_sqrt(sm2*acb(2*s, arb(1))) - s*h/(1 - h)

def certify(fun, box, support, maxdepth=40, maxboxes=200000):
    stack = [(box, 0)]; n = 0; worst = None
    while stack:
        (h0, h1, x0, x1), d = stack.pop()
        val = fun(ball(h0, h1), ball(x0, x1), support)
        n += 1
        if n > maxboxes: raise SystemExit('too many boxes')
        lo = val.lower()
        if lo > 0:
            worst = lo if worst is None or lo < worst else worst
            continue
        if d >= maxdepth: raise SystemExit(f'FAILED on box {(h0, h1, x0, x1)}: {val}')
        if (h1 - h0)/(box[1] - box[0]) >= (x1 - x0)/(box[3] - box[2]):
            hm = (h0 + h1)/2; stack += [((h0, hm, x0, x1), d + 1), ((hm, h1, x0, x1), d + 1)]
        else:
            xm = (x0 + x1)/2; stack += [((h0, h1, x0, xm), d + 1), ((h0, h1, xm, x1), d + 1)]
    return n, worst

if __name__ == '__main__':
    V = 32.0; HMAX = 0.3184
    for support in ['arc', 'nest']:
        n1, w1 = certify(G1, (0.0, HMAX, 0.0, V), support)
        n2, w2 = certify(G2, (0.0, HMAX, 0.0, 1/V), support)
        print(f'{support}: chart nu in [0,{V}]: {n1} boxes, min lower bound {float(w1):.4f}; '
              f'chart s in [0,1/{V}]: {n2} boxes, min lower bound of s*G {float(w2):.5f}')
    print('CERTIFIED (Arb)')
