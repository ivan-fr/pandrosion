import sympy as s
v,p,h,j,zx,zy,k,l=s.symbols('v p h j zx zy k l'); W=s.Integer(2); H=s.Integer(4)
d=s.Matrix([2*W*v,H*(1-2*v)]); B=s.Matrix([W,0]); M=s.Matrix([h,j]); G=B-2*((B-M).dot(d))*d/(d.dot(d)); Y=s.factor(zy+(G[1]-zy)*(W-zx)/(G[0]-zx)); q=s.factor(1-Y/H)
num,den=s.fraction(q); A=(p+1)*(p+2); b=p*p-4; C=(p-1)*(p-2); N=C*v*v-2*b*v+A; D=A*v*v-2*b*v+C
sol=s.solve(s.Poly(den-l*D,v).coeffs(),[h,j,zx],dict=True)[0]; print('den solution',sol)
eq=s.Poly(s.expand((num-l*k*N).subs(sol)),v).coeffs(); print('eq',list(map(s.factor,eq))); so=s.solve(eq,[zy,k,l],dict=True); print(so)
for a in so:
 print({t:s.factor(z.subs(a)) for t,z in sol.items()},a)
