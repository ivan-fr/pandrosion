"""Interval certificate (Arb ball arithmetic, python-flint) for the half-plane theorem of the
three-mean support, degrees p >= 4 (h = 1/p in [0, 1/4]); p in (2, 4] is covered by the written
argument (tan(pi/p) >= 1 and (p-1)|m| >= 1).

Boundary t = i y, w = -2 + i nu, nu = y - 1/y >= 0, g = sqrt(w + 4) = sqrt(2 + i nu),
    m = m0 g + G - n sqrt(1 + d w).
Statement certified:
    Gc(h, nu) = pi (1-h) |m|^2 - (1 - pi h) Re(m g) - h/(1-h) > 0     for 0 <= h <= 1/4, nu >= 0,
in the charts nu in [0, V] and sigma = nu^(-1/2) in [0, V^(-1/2)] (the second for Gc/nu).
Together with 0 <= arg m, arg g < pi/4 (written proof) this gives 0 <= Arg phi(iy) <= pi/p."""
from flint import arb, acb, ctx
ctx.prec = 64
PI = arb.pi()

def ball(lo, hi):
    mid = (lo + hi)/2
    rad = max(hi - mid, mid - lo)*(1 + 1e-12) + 1e-300
    return arb(mid, rad)

def consts(h):
    m0 = (1 - 2*h)*(4*h*h + 21*h + 47)/(60*(4 - h*h))
    G = 16*(1 + h)*(4 - h*h)/(15*(4*h*h + 5))
    n = 49*(1 + h)*(1 - 4*h*h)/(10*(4 - h*h)*(4*h*h + 5))
    d = (4*h*h + 5)/84
    return m0, G, n, d

def G1(h, nu):
    m0, G, n, d = consts(h)
    g = acb(arb(2), nu).sqrt()
    r = acb(1 - 2*d, d*nu).sqrt()
    m = m0*g + G - n*r
    mg = m*g
    return PI*(1 - h)*(m.real*m.real + m.imag*m.imag) - (1 - PI*h)*mg.real - h/(1 - h)

def G2(h, sg):
    """Gc / nu with s = 1/nu = sg^2: scaled quantities g_s = sqrt(s) g, m_s = sqrt(s) m."""
    m0, G, n, d = consts(h)
    s = sg*sg
    g = acb(2*s, arb(1)).sqrt()
    r = acb(s*(1 - 2*d), d).sqrt()
    m = m0*g + G*sg - n*r
    mg = m*g
    return PI*(1 - h)*(m.real*m.real + m.imag*m.imag) - (1 - PI*h)*mg.real - s*h/(1 - h)

def certify(fun, box, maxdepth=60, maxboxes=400000):
    stack = [(box, 0)]; n = 0; worst = None
    while stack:
        (h0, h1, x0, x1), dd = stack.pop()
        val = fun(ball(h0, h1), ball(x0, x1))
        n += 1
        if n > maxboxes: raise SystemExit('too many boxes')
        lo = val.lower()
        if lo > 0:
            worst = lo if worst is None or lo < worst else worst
            continue
        if dd >= maxdepth: raise SystemExit(f'FAILED on box {(h0, h1, x0, x1)}: {val}')
        if (h1 - h0)/(box[1] - box[0]) >= (x1 - x0)/(box[3] - box[2]):
            hm = (h0 + h1)/2; stack += [((h0, hm, x0, x1), dd + 1), ((hm, h1, x0, x1), dd + 1)]
        else:
            xm = (x0 + x1)/2; stack += [((h0, h1, x0, xm), dd + 1), ((h0, h1, xm, x1), dd + 1)]
    return n, worst

def selftest():
    """The scaled formula agrees with the direct one (plain floats)."""
    import cmath, math
    for h in (0.0, 0.1, 0.25):
        for nu in (40.0, 300.0):
            a = float(G1(arb(h), arb(nu)).mid())/nu
            b = float(G2(arb(h), arb(nu**-0.5)).mid())
            assert abs(a - b) < 1e-9*(1 + abs(a)), (h, nu, a, b)

if __name__ == '__main__':
    selftest()
    V = 36.0; HMAX = 0.25
    n1, w1 = certify(G1, (0.0, HMAX, 0.0, V))
    n2, w2 = certify(G2, (0.0, HMAX, 0.0, V**-0.5))
    print(f'three-mean: chart nu in [0,{V}]: {n1} boxes, min lower bound {float(w1):.5f}; '
          f'chart nu^(-1/2) in [0,{V**-0.5:.4f}]: {n2} boxes, min lower bound of Gc/nu {float(w2):.5f}')
    print('CERTIFIED (Arb)')
