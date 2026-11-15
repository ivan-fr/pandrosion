"""Certificate for the sector theorem: boundary inequalities on the ray arg t = beta, beta = 5 pi/6.

Natural branch: q = sqrt(t) * m(w), with principal square roots, w = t + 1/t - 2,
    arc:  m^2 = 1 + a w,          nest: m^2 = 1 + a w / rho,  rho^2 = 1 + b w / (1 + c w).
On the ray t = y e^{i beta}, z = sqrt(t), put K = z conj(m) + m / conj(z). With h = 1/p, M = (p-1) m,
N = (z + M) conj(1/z + M) satisfies  h^2 N = h^2 e^{i beta} + (1-h)^2 |m|^2 + h (1-h) K, and
    (L)  Im K > 0                      gives  arg phi > 0,
    (U)  F <= 0                        gives  arg phi <= 2 beta / p,   where, with theta = 2 beta h,
         F = [h sin(beta) + (1-h) Im K] cos(theta) - h cos(beta) sin(theta)
             - (1-h)^2 |m|^2 sin(theta)/h - (1-h) Re K sin(theta).
By the symmetry y -> 1/y only y >= 1 is needed. Range certified: 0 <= h <= 1/3 (p >= 3), in the charts
y in [1, V] (direct formulas) and s = 1/y in [0, 1/V] (formulas without cancellation, for s*F and Im K).
Ball arithmetic: Arb (python-flint).  Also a floating-point comparison of the two sets of formulas.
"""
import cmath, math
from flint import arb, acb, ctx
ctx.prec = 64
PI = arb.pi()
BETA = 5*PI/6
BETA_F = 5*math.pi/6
E1 = acb(BETA.cos(), BETA.sin())            # e^{i beta}
E1c = E1.conjugate(); EH = acb((BETA/2).cos(), (BETA/2).sin())

def ball(lo, hi):
    mid = (lo + hi)/2
    return arb(mid, max(hi - mid, mid - lo)*(1 + 1e-12) + 1e-300)

def coeffs(h, support):
    a = (1 - 2*h)/12
    if support == 'arc': return a, None, None
    return a, (1 + h)*(3 + h)/30, (121 - 185*h - 67*h*h - h*h*h)/(840*(3 + h))

def sinc_enclosure(h):
    """Enclosure of sin(2 beta h)/h for h >= 0: 2 beta sinc is decreasing on [0, pi]."""
    lo_h, hi_h = h.lower(), h.upper()
    def val(x):
        th = 2*BETA*x
        return 2*BETA if not (x > 0) else th.sin()/x
    v_hi = val(lo_h); v_lo = val(hi_h)
    return v_lo.union(v_hi)

def pieces_direct(h, y, support):
    """Im K, Re K, |m|^2 from the definitions (chart y in [1, V])."""
    a, b, c = coeffs(h, support)
    t = E1*y; z = EH*y.sqrt(); w = t + 1/t - 2
    if support == 'arc':
        m2 = 1 + a*w
    else:
        rho = (1 + b*w/(1 + c*w)).sqrt()
        assert rho.real > 0, 'rho^2 too close to the cut'
        m2 = 1 + a*w/rho
    m = m2.sqrt()
    assert m.real > 0, 'radicand too close to the cut'
    K = z*m.conjugate() + m/z.conjugate()
    return K.imag, K.real, abs(m2)

def pieces_scaled(h, s, support):
    """Im K, s*Re K, s*|m|^2 for y = 1/s, without cancellation (chart s in [0, 1/V])."""
    a, b, c = coeffs(h, support)
    sw = E1 + s*s*E1c - 2*s                       # s*w
    poly = 1 - 2*s*E1c + s*s*E1c*E1c              # w/t
    if support == 'arc':
        rho = acb(1); im_rho2_over_s = arb(0)
    else:
        rho = (1 + b*sw/(s + c*sw)).sqrt()
        assert rho.real > 0, 'rho^2 too close to the cut'
        im_rho2_over_s = b*(1 - s*s)*BETA.sin()/(abs(s + c*sw)**2)
    n2 = s*E1c + a*poly/rho                        # n^2 = m^2/t
    n = n2.sqrt()
    assert n.real > 0, 'n^2 too close to the cut'     # n = m/z is the principal root for y >= 1
    # y * Im(n^2) = -sin(beta) + a * Im(poly/rho)/s
    im_rho_over_s = im_rho2_over_s/(2*rho.real)
    im_inv_rho_over_s = -im_rho_over_s/(abs(rho)**2)
    y_im_n2 = -BETA.sin() + a*(im_inv_rho_over_s + ((-2*E1c + s*E1c*E1c)/rho).imag)
    imK = -y_im_n2/(2*n.real) + (E1*n).imag
    s_reK = n.real + s*(E1*n).real
    s_m2 = abs(s + a*sw/rho)
    return imK, s_reK, s_m2

def F_direct(h, y, support):
    imK, reK, m2 = pieces_direct(h, y, support)
    th = 2*BETA*h
    F = (h*BETA.sin() + (1 - h)*imK)*th.cos() - h*BETA.cos()*th.sin() \
        - (1 - h)**2*m2*sinc_enclosure(h) - (1 - h)*reK*th.sin()
    return imK, F

def F_scaled(h, s, support):
    imK, s_reK, s_m2 = pieces_scaled(h, s, support)
    th = 2*BETA*h
    sF = (s*h*BETA.sin() + (1 - h)*s*imK)*th.cos() - s*h*BETA.cos()*th.sin() \
        - (1 - h)**2*s_m2*sinc_enclosure(h) - (1 - h)*s_reK*th.sin()
    return imK, sF

def certify(fun, box, support, maxboxes=400000):
    stack = [box]; n = 0; wL = None; wU = None
    while stack:
        h0, h1, x0, x1 = stack.pop()
        n += 1
        if n > maxboxes: raise SystemExit('too many boxes')
        try:
            imK, F = fun(ball(h0, h1), ball(x0, x1), support)
            ok = (imK.lower() > 0) and (F.upper() < 0)
        except (AssertionError, ZeroDivisionError):
            ok = False
        if ok:
            l, u = imK.lower(), -F.upper()
            wL = l if wL is None or l < wL else wL
            wU = u if wU is None or u < wU else wU
            continue
        if (h1 - h0)/(box[1] - box[0]) >= (x1 - x0)/(box[3] - box[2]):
            hm = (h0 + h1)/2; stack += [(h0, hm, x0, x1), (hm, h1, x0, x1)]
        else:
            xm = (x0 + x1)/2; stack += [(h0, h1, x0, xm), (h0, h1, xm, x1)]
    return n, wL, wU

def selftest():
    """Floating-point comparison of the direct and scaled formulas."""
    worst = 0
    for support in ['arc', 'nest']:
        for hf in [0.0, 0.05, 0.2, 1/3]:
            for yf in [16.0, 40.0, 300.0]:
                h = arb(hf); y = arb(yf); s = 1/y
                i1, r1, m1 = pieces_direct(h, y, support)
                i2, r2, m2 = pieces_scaled(h, s, support)
                worst = max(worst, abs(float(i1.mid()) - float(i2.mid())), abs(float((s*r1).mid()) - float(r2.mid())),
                            abs(float((s*m1).mid()) - float(m2.mid())))
    assert worst < 1e-9, worst
    return worst

if __name__ == '__main__':
    print('self-test, largest discrepancy between the two sets of formulas:', selftest())
    V = 16.0; HMAX = 1/3 + 1e-9
    for support in ['arc', 'nest']:
        n1, l1, u1 = certify(F_direct, (0.0, HMAX, 1.0, V), support)
        n2, l2, u2 = certify(F_scaled, (0.0, HMAX, 0.0, 1/V), support)
        print(f'{support}: chart y in [1,{V}]: {n1} boxes, Im K >= {float(l1):.4f}, -F >= {float(u1):.4f}; '
              f'chart s in [0,1/{V}]: {n2} boxes, Im K >= {float(l2):.4f}, -s F >= {float(u2):.5f}')
    print('CERTIFIED: sector beta = 5 pi/6, p >= 3')
