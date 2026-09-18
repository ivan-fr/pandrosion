"""Exact independent identities and coverage checks for the native incidence audit."""
import json
import re
from pathlib import Path
import sympy as S

W,H,X,s,t,p,a,b,k=S.symbols('W H X s t p a b k',positive=True)
q=S.symbols('q', nonnegative=True)
def point(x,y): return S.Matrix([x,y,1])
def cross(u,v): return u.cross(v)
def parallel(l,Q): return S.Matrix([l[0],l[1],-l[0]*Q[0]-l[1]*Q[1]])
def eq(u,v=0): assert S.simplify(u-v)==0, S.factor(u-v)
A=point(W,H); B=point(W,0); M=point(0,H*(1-1/X)); E=point(W,H*(1-t/X)); P=point(W,H*(1-s))
# Native chain: every determinant is independent of the current exponent.
red=cross(point(0,H*(1-s)),B)
eq(red[1],W)
Lj=point(0,H*(1-a)); Bj=point(W*a,H*(1-a))
nextline=parallel(red,Bj)
eq(nextline.dot(point(0,H*(1-s*a))))
eq(cross(S.Matrix([1,0,0]),nextline)[2],W)
diagonal=cross(point(0,H),B)
eq(cross(S.Matrix([0,1,-Lj[1]]),diagonal)[2],-H)
# Actual report determinant, including both defining joins.
D=point(W+a,H+k*a)
green=cross(M,E)
m=H/(W*X)*(1-t)
eq(cross(cross(A,D),parallel(green,P))[2],-W*a*(k-m))
# AK and AD slopes and strictly positive gaps.
K=point(W*(1-X/p),0)
F=point(W-2*W/(p-1),H-H*(p+1)/(X*(p-1)))
Dc=point(F[0],F[1]-H*t/X)
for D,slope,gap in [
 (K,H*p/(W*X),H/(W*X)*(p-1+t)),
 (Dc,H/(2*W*X)*(p+1+(p-1)*t),H/(2*W*X)*(p-1+(p+1)*t))]:
 eq((D[1]-H)/(D[0]-W),slope);eq(slope-m,gap)
# Projective preparation: use the actual homogeneous cross product.
Z=point(W*(1+(5*p-1)/(2*p*(2*p-1))),H*(1+(p+1)/((2*p-1)*X)))
ell=S.Matrix([0,1,-H*(1+(5*p-1)/((p+1)*X))])
hD=cross(cross(Z,E),ell)
eq(hD[2],H/((2*p-1)*X)*((2*p-1)*t+p+1))
Dx,Dy=hD[0]/hD[2],hD[1]/hD[2]
num=2*p*((2*p-1)*t+p+1);pole=(p+1)*t+5*p-1
den=(p+1)*t**2+2*(2*p-1)*(p+1)*t+(2*p-1)*(p-1)
eq(Dx-W,W*(5*p-1)*pole/((p+1)*num))
eq((Dy-H)/(Dx-W),H/(W*X)*num/pole)
eq(H/(W*X)*num/pole-m,H/(W*X)*den/pole)
# Transverse moving circles; no branch clamp or numeric square-root sampling.
alpha=(5*p+2)/(p-2)
r=H/X*(t+alpha);delta2=(H/X)**2*(alpha**2-1)
eq(r**2-delta2,(H/X)**2*(t*t+2*alpha*t+1))
eq((5*p+2)**2-(p-2)**2,24*p*(p+1))
beta=S.symbols('beta',positive=True);height=S.symbols('height',positive=True)
Da=point(W-W/beta,H-H/(X*beta)-height)
ka=H/(W*X)+beta*height/W
eq((Da[1]-H)/(Da[0]-W),ka)
eq(ka-m,H/(W*X)*t+beta*height/W)
# Positive coefficients after p=q+3 certify the residual polynomials on t>0,q>=0.
for poly in [p-1+t,p-1+(p+1)*t,(2*p-1)*t+p+1,pole,den,(p-2)*(t*t+1)+2*(5*p+2)*t]:
 coeffs=S.Poly(S.expand(poly.subs(p,q+3)),q,t).coeffs()
 assert all(c>0 for c in coeffs)
# Machine-readable coverage and links must agree with declarations in the checked module.
data=json.loads(Path('docs/NATIVE_NONDEGENERACY.json').read_text())
lean=Path('LeanMath/Papers/RectangleNativeNondegeneracy.lean').read_text()
names=set(re.findall(r'^theorem (\w+)',lean,re.M))
assert len(data['rows'])>=50
for row in data['rows']:
 assert row['lean_theorem'].split('.')[-1] in names,row
 assert row['classification'] in ['A','B']
 assert row['projectively_continuable'] and not row['needs_alternate_chart']
for method in ['AK','AD','projective','arc']:
 assert len([r for r in data['rows'] if r['method']==method])>=12
print(json.dumps({'status':'PASS','audit_rows':len(data['rows']),'scope':'exact symbolic incidence identities and report coverage; no scalar convergence inference'}))
