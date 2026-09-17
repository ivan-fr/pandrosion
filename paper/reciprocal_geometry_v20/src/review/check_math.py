from pathlib import Path
import json
import sympy as S
p,t,v=S.symbols('p t v',positive=True)
a=(p-1)*(2*p-1);b=8*p*p-2;c=(p+1)*(2*p+1)
D4=(p+1)*t*t+2*(2*p-1)*(p+1)*t+(2*p-1)*(p-1)
phis={'AK':p/(p-1+t),'AD':(p+1+(p-1)*t)/(p-1+(p+1)*t),'projective':2*p*((2*p-1)*t+p+1)/D4,'rational5':(a*t*t+b*t+c)/(c*t*t+b*t+a)}
orders={'AK':2,'AD':3,'projective':4,'rational5':5}
expected={'AK':-(p-1)/2,'AD':(p*p-1)/12,'projective':-(p*p-1)*(2*p-1)/72,'rational5':(p*p-1)*(4*p*p-1)/720}
records={}
for name,phi in phis.items():
 n=orders[name];derivative=S.factor(phi+p*t*S.diff(phi,t))
 coefficient=S.factor(S.cancel(derivative/(t-1)**(n-1)).subs(t,1)*p**(n-1)/n)
 assert S.factor(coefficient-expected[name])==0,(name,coefficient)
 for k in range(n):
  assert S.simplify(S.diff(phi,t,k).subs(t,1)-S.prod(-1/p-j for j in range(k)))==0,(name,k)
 records[name]={'order':n,'relative_coefficient':str(coefficient),'derivative':str(derivative),'pade_contact':'verified through degree '+str(n-1)}
# Direct [2/1] convention: inversion of the reciprocal [1/2] correction.
for k in range(4):assert S.simplify(S.diff(1/phis['projective'],t,k).subs(t,1)-S.prod(1/p-j for j in range(k)))==0
A=(p+1)*(p+2);B=p*p-4;C=(p-1)*(p-2);N=C*v*v-2*B*v+A;D=A*v*v-2*B*v+C
assert S.factor(C*N-(C*v-B)**2-3*(p*p-4))==0
assert S.factor(A*D-(A*v-B)**2-3*(p*p-4))==0
assert S.factor(S.diff(N,v)*D-N*S.diff(D,v)-12*p*((p*p-4)*(v*v+1)-2*(p*p+2)*v))==0
assert S.factor(p*N*D+v*(S.diff(N,v)*D-N*S.diff(D,v))-p*A*C*(v-1)**4)==0
# Local logarithmic cubic coefficient of the bilateral geometric center.
x=S.symbols('x');R=S.exp(-p*x)
logG=(p-1)/2*(S.log((p-1)*R+1)-S.log(R+p-1))+(3-p)/2*S.log(R)
coeff=S.factor(S.diff(x+logG,x,3).subs(x,0)/6)
assert S.factor(coeff-(p-2)*(p-1)**2/6)==0
result={'status':'PASS','rational_maps':records,'fixed_circle':'positive quadratics, branch derivative and fourth-power certificate verified symbolically','bilateral_logarithmic_coefficient':str(coeff),'scope':'Algebraic cross-checks; full analytical arguments reviewed in manuscript, not an independent formal verification of every claim.'}
Path(__file__).with_name('math_checks.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
