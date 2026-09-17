"""V20: projective erratum, uniform circle chart, scaling and branch sampling."""
from pathlib import Path
import json
import sympy as S
import mpmath as mp
p,t,v=S.symbols('p t v');A=(p+1)*(p+2);B=p*p-4;C=(p-1)*(p-2)
D4=(p+1)*t*t+2*(2*p-1)*(p+1)*t+(2*p-1)*(p-1)
N4=2*p*((2*p-1)*t+p+1)
assert S.expand(N4-D4-(1-t)*((p+1)*t+5*p-1))==0
r=S.Rational(1,3);x=p-3
D=625*x**5+10525*x**4+56797*x**3+88639*x**2+14758*x+664
K=625*x**5+1975*x**4+4147*x**3+2905*x**2+448*x+340
E=288*p*(p-2)*(25*p*p-244)/D
zx=2-E;zy=384*p*(25*p**3-50*p*p-415*p+974)/D;k=K/D
u=5-4*A/(9*C);w=8*(5-2*p)/(9*(p-1));j=-3*E*w/4;h=2+2*j-E*u/2
n=4*v*v+16*(r-v)**2;b=(2-h)*2*v-j*4*(r-v)
I=(2-zx)*(-8*b*(r-v)-zy*n)-(4*(1-k*t)-zy)*((2-zx)*n-4*b*v)
lam=-64*k*E/(9*C)
N=C*v*v-2*B*v+A;Dn=A*v*v-2*B*v+C
assert S.factor(I-lam*(N-t*Dn))==0
assert S.factor(k.subs(p,4)-S.Rational(145,2389))==0
# Dense, reproducible evidence only: no theorem follows from this sample.
mp.mp.dps=90;stats=[]
for pp in [3,5,17]:
 upper=(7*pp*pp-4+4*pp*mp.sqrt(3*(pp*pp-1)))/(pp*pp-4)
 limit=mp.log(upper);samples=[limit*mp.mpf(i)/2001 for i in range(-2000,2001) if i]
 samples += [sign*limit*(1-mp.mpf(10)**(-q)) for q in [6,12,24,40] for sign in [-1,1]]
 largest=mp.mpf(0)
 for logt in samples:
  tt=mp.exp(logt);aa=(pp+1)*(pp+2);bb=pp*pp-4;cc=(pp-1)*(pp-2)
  radical=mp.sqrt((42*pp*pp-24)*tt-3*bb*(1+tt*tt))
  vv=(aa-tt*cc)/(bb*(1-tt)+radical) if tt<=1 else (radical-bb*(1-tt))/(tt*aa-cc)
  e=logt/pp;next_e=e+mp.log(vv);ratio=abs(next_e/e)
  assert ratio<1,(pp,tt,ratio)
  largest=max(largest,ratio)
 stats.append({'p':pp,'samples':len(samples),'max_abs_error_ratio':mp.nstr(largest,18)})
result={'projective_difference_identity':'PASS','uniform_circle_identity':'PASS','uniform_denominator_positive':'all coefficients positive in p-3','renormalization':'Xnew=c^p X; snew=s/c; residual invariant','contraction_sampling':stats,'precision':90,'scope':'Exact symbolic identities plus finite contraction evidence; contraction remains conjectural.'}
Path(__file__).with_name('checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
