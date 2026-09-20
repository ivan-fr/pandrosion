"""Whole-branch contraction of the fixed-circle inverse [2/2] correction (V22, Theorem C).

Independent symbolic and numerical companion to LeanMath.Papers.RectangleFixedCircleBranch.
Run:  python3 verify.py   (writes checks.json next to this file)
"""
import json, sys
from pathlib import Path
import sympy as sp
from mpmath import mp, mpf, sqrt as msqrt, log as mlog

out = {}
p, v, u = sp.symbols('p v u', positive=True)
A = (p+1)*(p+2); B = p**2-4; C = (p-1)*(p-2)
N = C*v**2 - 2*B*v + A
D = A*v**2 - 2*B*v + C
S = sp.expand(2*A*C*(v-1)**4 - N*D)
Q = (p**2-4)*(v**2+1) - 2*(p**2+2)*v
h_prime = p/v + 2*sp.diff(N, v)/N - 2*sp.diff(D, v)/D

def zero(e):
    return sp.simplify(e) == 0

t,z=sp.symbols('t z',real=True)
centered=(1-t)-((1-2/p)+(1+2/p)*t)*z/2+((1-3/p+2/p**2)-t*(1+3/p+2/p**2))*z**2/12
out['centered_quadratic_identity']=zero((N-t*D).subs(v,1+z/p)/12-centered)
out['centered_quadratic_slope_at_root']=zero(sp.diff(centered,z).subs({t:1,z:0})+1)
out['derivative_certificate'] = zero(p*N*D + v*(sp.diff(N, v)*D - N*sp.diff(D, v)) - p*A*C*(v-1)**4)
out['reciprocity'] = zero((N/D).subs(v, 1/v)*(N/D) - 1)
out['h_prime_identity'] = zero(h_prime - p*S/(v*N*D))
out['branch_quadratic'] = zero(sp.diff(N, v)*D - N*sp.diff(D, v) - 12*p*Q)
Su = sp.Poly(sp.expand(S.subs(v, 1+u)), u).all_coeffs()
out['S_coefficients'] = [str(sp.factor(c)) for c in Su]
out['S_coefficients_expected'] = zero(Su[0]-A*C) and zero(Su[1]-12*(p**2-4)) and zero(Su[2]-12*(p**2-16)) and Su[3] == -288 and Su[4] == -144
u1, u2 = sp.symbols('u1 u2', positive=True)
cert = A*C*u1**2*u2**2*(u1+u2) + 12*(p**2-4)*u1**2*u2**2 + 288*u1*u2 + 144*(u1+u2)
out['slope_certificate'] = zero(u2**2*S.subs(v, 1+u1) - u1**2*S.subs(v, 1+u2) + (u2-u1)*cert)
out['Q_shift'] = zero(Q.subs(v, 1+u) - ((p**2-4)*u**2 - 12*u - 12))
rel = sp.Eq((p**2-4)*u**2, 12*(u+1))
Nred = 6*(2*(2*p+1) - (p**2-2*p-2)*u)/(p+2)
Dred = 6*(2*(2*p-1) + (p**2+2*p-2)*u)/(p-2)
out['N_reduced'] = zero(sp.expand((N.subs(v, 1+u) - Nred)*(p+2)) - (p-1)*((p**2-4)*u**2 - 12*(u+1)))
out['D_reduced'] = zero(sp.expand((D.subs(v, 1+u) - Dred)*(p-2)) - (p+1)*((p**2-4)*u**2 - 12*(u+1)))
# large-p certificates
q = sp.symbols('q')
poly = 409*p**4 - 5046*p**3 + 46018*p**2 - 14904*p + 22600
out['large_p_polynomial_in_q'] = [int(c) for c in sp.Poly(sp.expand(poly.subs(p, 10+q)), q).all_coeffs()]
out['large_p_all_coefficients_positive'] = all(c > 0 for c in out['large_p_polynomial_in_q'])
out['r_upper_347'] = zero(sp.expand(sp.Rational(347,100)**2*p**2 - 12*(p**2-1)) - (sp.Rational(409,10000)*p**2 + 12))
out['r_lower_346'] = str(sp.factor(sp.expand(12*(p**2-1) - (sp.Rational(346,100)*p-1)**2)))
out['exp_bound'] = float(sp.Rational(27182818286, 10**10)**5) < 148.42 and 148.42 < 12.3**2
# small p numeric certificates (same rationals as the Lean file)
from fractions import Fraction as F
small = {3: (F(979,100), F(49,5)), 4: (F(1341,100), F(671,50)), 5: (F(1697,100), F(849,50)),
         6: (F(2049,100), F(41,2)), 7: (F(24), F(2401,100)), 8: (F(2749,100), F(55,2)), 9: (F(1549,50), F(3099,100))}
out['small_p'] = {}
for n, (rlo, rhi) in small.items():
    x = 12*(n*n-1)
    assert rlo*rlo <= x <= rhi*rhi
    ulo = (6+rlo)/(n*n-4); uhi = (6+rhi)/(n*n-4)
    Nhi = F(6)*(2*(2*n+1)-(n*n-2*n-2)*ulo)/(n+2)
    Dlo = F(6)*(2*(2*n-1)+(n*n+2*n-2)*ulo)/(n-2)
    lhs = (1+uhi)**n*Nhi**2; rhs = Dlo**2
    out['small_p'][n] = {'rlo': str(rlo), 'rhi': str(rhi), 'ratio': float(lhs/rhs), 'ok': lhs < rhs}
# endpoint inequality v+^p < tau+^2 for p = 3..5000 at 50 digits
mp.dps = 50
worst = None
for n in range(3, 5001):
    rr = msqrt(12*(n*n-1)); vp = (n*n+2+rr)/(n*n-4)
    tp = (7*n*n-4+4*n*msqrt(3*(n*n-1)))/(n*n-4)
    m = 2*mlog(tp) - n*mlog(vp)
    assert m > 0
    if worst is None or m < worst[1]: worst = (n, m)
out['endpoint_margin_min'] = {'p': worst[0], 'margin': float(worst[1])}
out['endpoint_margin_limit'] = float(2*mlog(7+4*msqrt(3)) - 2*msqrt(3))
# direct sampling of the contraction on the branch
out['branch_samples'] = {}
for n in [3, 4, 5, 17, 100]:
    rr = msqrt(12*(n*n-1)); vp = (n*n+2+rr)/(n*n-4); vm = 1/vp
    Af=(n+1)*(n+2); Bf=n*n-4; Cf=(n-1)*(n-2)
    bad = 0; worst_ratio = mpf(0)
    for i in range(1, 2000):
        vv = vm + (vp-vm)*mpf(i)/2000
        if abs(vv-1) < mpf('1e-30'): continue
        Nn = Cf*vv**2-2*Bf*vv+Af; Dd = Af*vv**2-2*Bf*vv+Cf; tt = Nn/Dd
        e = mlog(tt)/n; ep = e + mlog(vv)
        ratio = abs(ep)/abs(e)
        worst_ratio = max(worst_ratio, ratio)
        if not ratio < 1: bad += 1
    out['branch_samples'][n] = {'violations': bad, 'max_ratio': float(worst_ratio)}
Path(__file__).with_name('checks.json').write_text(json.dumps(out, indent=1))
print(json.dumps(out, indent=1))
ok = all(v is True for k, v in out.items() if isinstance(v, bool))
ok = ok and all(d['ok'] for d in out['small_p'].values()) and all(d['violations'] == 0 for d in out['branch_samples'].values())
print('ALL CHECKS PASSED' if ok else 'FAILURE'); sys.exit(0 if ok else 1)
