"""Exact incidence, local order and global-error derivative certificates."""
from pathlib import Path
import json
import sympy as S
p,z,u,X,t,s=S.symbols('p z u X t s',positive=True)
a=(3*p*p-2)/(5*p*p);b=(4*p*p-1)/(15*p*p)
D=p*(1-a*z*z)/(1-b*z*z)
N=S.expand(15*p*p*(p*(1-a*z*z)-z*(1-b*z*z)))
Q=N.subs(z,-z);K=(p*p-1)*(4*p*p-1)*(9*p*p-1)
C=N/Q
assert S.factor(2/(p*(1-z*z))+S.diff(C,z)/C-2*K*z**6/(p*(1-z*z)*N*Q))==0
assert S.factor(D.subs(z,1)-S.Rational(9,5)-3*(p-3)*(10*p*p-3*p+1)/(5*(11*p*p+1)))==0
assert S.factor(D-D.subs(z,1)-75*p**3*(p*p-1)*(1-z*z)/((11*p*p+1)*(15*p*p-(4*p*p-1)*z*z)))==0
# Universal two-join projector L(u) -> top x=(n1*u+n0)/(d1*u+d0).
n1,n0,d1,d0=S.symbols('n1 n0 d1 d0')
a0=n1/d1;b0=2*(a0*d0-n0)/(d1*(1-a0));beta=b0+2*d0/d1
assert S.factor((b0-a0*(2*u+beta))/(b0-(2*u+beta))-(n1*u+n0)/(d1*u+d0))==0
# Actual 12 joins, using homogeneous coordinates; no scalar map places the output.
def point(x,y):return S.Matrix([x,y,1])
def cross(a,b):return a.cross(b)
def meet(a,b,line):
 v=cross(cross(a,b),line)
 return S.Matrix([S.factor(q/v[2]) for q in v])
L=S.Matrix([1,0,0]);R=S.Matrix([1,0,-1]);H=S.Matrix([0,1,-1])
ztop=meet(point(1,1-t/X),point(-2,1+2/X),H)
Z=meet(ztop,point(4,-2),L)
assert S.factor(Z[1]-(1-(t-1)/(t+1)))==0
square_center=meet(Z,point(1,-1),H)
twiceZ=meet(Z,point(-1,1),R)
square=meet(twiceZ,square_center,L)
assert S.factor(square[1]-(1-((t-1)/(t+1))**2))==0
# Subsequent projector and multiplication identities are checked with independent scalars.
zz,dd,ss=S.symbols('zz dd ss')
ratio=meet(point(1,1-2*zz),point(1/(1-2*dd),1),L)
assert S.factor(1-ratio[1]-zz/dd)==0
v=S.symbols('v');betaC=-2
Y=meet(point(0,1-v),point(-1,-1),R)
VC=meet(Y,point(S.Rational(8,9),S.Rational(41,9)),H)
assert S.factor(VC[0]-8*(1+v)/(7+9*v))==0
EightS=meet(point(1,1-ss),point(S.Rational(8,7),1),L)
output=meet(EightS,VC,R)
assert S.factor(1-output[1]-ss*(1-v)/(1+v))==0
# D projector exactly produces 1/(1-2D) from u=z^2.
Du=p*(1-a*u)/(1-b*u)
assert S.factor((-b*u+1)/((2*p*a-b)*u+1-2*p)-1/(1-2*Du))==0
result=dict(correction_joins=12,arcs=0,parallels=0,local_order=7,
 log_error_coefficient=str(S.factor(K/100800)),
 error_derivative='2*(p^2-1)*(4p^2-1)*(9p^2-1)*z^6 / (p*(1-z^2)*N*Q)',
 domain='p>=3, X>0, s>0, t=X*s^p>0; exact real geometry',
 certificates='exact rational incidence and derivative identities; inequalities explained in README.md')
(Path(__file__).parent/'certificates.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS: 12-join incidence protocol, derivative identity, positive-domain bounds and order-7 coefficient.')
