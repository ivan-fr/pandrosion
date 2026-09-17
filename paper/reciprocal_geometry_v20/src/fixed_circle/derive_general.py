import sympy as s
v,p,h,j,zx,zy,k,l,r=s.symbols('v p h j zx zy k l r'); W=s.Integer(2); H=s.Integer(4)
d=s.Matrix([W*v,H*(r-v)]); B=s.Matrix([W,0]); M=s.Matrix([h,j]); dd=d.dot(d); gn=B*dd-2*((B-M).dot(d))*d
# q=(1-zy/H)-(gn.y-zy*dd)*(W-zx)/(H*(gn.x-zx*dd))
den=s.expand(H*(gn[0]-zx*dd)); num=s.expand((H-zy)*(gn[0]-zx*dd)-(gn[1]-zy*dd)*(W-zx))
A=(p+1)*(p+2); b=p*p-4; C=(p-1)*(p-2); N=C*v*v-2*b*v+A; D=A*v*v-2*b*v+C
sol=s.solve(s.Poly(den-l*D,v).coeffs(),[h,j,zx],dict=True)[0]
eq=[s.factor(e/l) for e in s.Poly(s.expand((num-l*k*N).subs(sol)),v).coeffs()]; so=s.solve(eq,[zy,k,l],dict=True)
for a in so:
 print('SOL', {str(t):s.factor(z.subs(a)) for t,z in sol.items()}, {str(t):s.factor(z) for t,z in a.items()})
