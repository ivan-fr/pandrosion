"""Exact identities plus adversarial precision checks of the centered architecture."""
import sympy as S
from model import schedule,centered_power,update
p,n,d,q,t,Y=S.symbols('p n d q t Y',nonzero=True)
s=1+q/p
# The multiplication identities assume d_n=p(s^n-1)/n.
assert S.factor((p/(2*n))*((1+n*d/p)**2-1)-(d+n*d*d/(2*p)))==0
assert S.factor((p/(n+1))*((1+n*d/p)*(1+q/p)-1)-(d+(q-d)/(n+1)+n*d*q/(p*(n+1))))==0
C=(p+1+(p-1)*t)/(p-1+(p+1)*t)
assert S.factor(p*(s*C-1)-(q+2*(1+q/p)*(1-t)/(1+t+(t-1)/p)))==0
assert len(schedule(1000000))==25
assert len(schedule(2**19-1))==36
assert len(schedule(983039))==37
import mpmath as m
m.mp.dps=100
worst=0.
for k in [3,4,7,32,100,1000,1000000]:
 for x in [-.69,-.3,-.001,0,.3,.69]:
  got,_=centered_power(x,k);exact=(1+m.mpf(x)/k)**k
  worst=max(worst,float(abs(got-exact)))
assert worst<1e-12
# Programmed-coefficient resolution is finite: report, rather than hide, its error.
print('PASS: exact binary-deficit and AD conjugacy identities; 49 power checks; max error',worst)
