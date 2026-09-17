"""Independent intersections, symbolic certificates, high precision benchmark."""
from pathlib import Path
import json
import sympy as sp
import mpmath as mp
mp.mp.dps = 250

def parameters(p):
    q=sp.Rational
    if p==4:
        return tuple(map(mp.mpf,[str(x.evalf(255)) for x in [q(1,3),q(13502,7167),q(3328,2389),-q(214,2389),q(2432,2389),q(145,2389)]]))
    p=mp.mpf(p); L=p**3+12*p*p+39*p-26
    return (mp.mpf('.5'), 2-72*p*(p+4)/((p-1)*L),24*p*(p-2)*(p+4)/((p-1)*L),2-24*p*(p+4)*(p-2)/((p-4)*L),24*p*(p*p+2*p-26)/((p-4)*L),(p-2)*(p*p-4*p+13)/L)

def cross(a,b): return a[0]*b[1]-a[1]*b[0]
def sub(a,b): return (a[0]-b[0],a[1]-b[1])
def meet(a,b,c,d):
    u,v=sub(b,a),sub(d,c); den=cross(u,v)
    if not den: raise ValueError('parallel lines')
    f=cross(sub(c,a),v)/den
    return (a[0]+f*u[0],a[1]+f*u[1])
def hub(f):
    if f==1: raise ValueError('fixed hub at infinity')
    return (2*f/(f-1),mp.mpf(4))
def phi(p,t):
    A=(p+1)*(p+2);B=p*p-4;C=(p-1)*(p-2)
    delta=(42*p*p-24)*t-3*B*(1+t*t)
    if delta<0: raise ValueError('outside real domain')
    r=mp.sqrt(delta)
    return (A-t*C)/(B*(1-t)+r) if t<=1 else (r-B*(1-t))/(t*A-C)

def construct(p,X,s):
    rho,h,j,zx,zy,k=parameters(p)
    O=(0,mp.mpf(4)); C0=(0,0); A0=(2,mp.mpf(4)); B0=(2,0)
    P=(2,4*(1-s)); V=meet(C0,P,O,A0); Q=P; saved=None; lines=[(C0,P,'CP')]
    for i in range(1,p):
        f=rho if i==1 else k*X*2**(p-3)/rho if i==p-1 else mp.mpf('.5')
        F=hub(f); L=meet(F,Q,O,C0); lines.append((F,Q,'projection gauche'))
        if i==1: saved=L
        Q=meet(V,L,A0,B0);lines.append((V,L,'multiplication par s'))
    Z=(zx,zy); M=(h,j); direction=sub(Q,Z); off=sub(Z,M)
    aa=sum(x*x for x in direction);bb=2*sum(x*y for x,y in zip(direction,off));cc=sum(x*x for x in off)-((2-h)**2+j*j)
    disc=bb*bb-4*aa*cc
    if disc<0:raise ValueError('line misses circle')
    choices=[]
    for sign in (-1,1):
        lam=(-bb+sign*mp.sqrt(disc))/(2*aa);G=(zx+lam*direction[0],zy+lam*direction[1])
        U=meet(B0,G,O,A0); F=meet(U,saved,A0,B0); value=1-F[1]/4;v=value/s
        # Geometric branch: R'(v)<0, equivalent central arc.
        derivative_numerator=(p*p-4)*(v*v+1)-2*(p*p+2)*v
        choices.append((derivative_numerator,value,G,U,F))
    good=[a for a in choices if a[0]<0]
    if len(good)!=1:raise ValueError('tangent or ambiguous branch')
    _,value,G,U,F=good[0];lines += [(Z,Q,'ZT ∩ Γ'),(B0,G,'BG ∩ OA'),(U,saved,'lecture sur AB')]
    assert len(lines)==2*p+2
    return value,lines

def symbolic():
    p,v,t=sp.symbols('p v t');A=(p+1)*(p+2);B=p*p-4;C=(p-1)*(p-2);N=C*v*v-2*B*v+A;D=A*v*v-2*B*v+C
    assert sp.expand(p*N*D+v*(sp.diff(N,v)*D-N*sp.diff(D,v))-p*A*C*(v-1)**4)==0
    assert sp.expand(B*B*(1-t)**2-(C-t*A)*(A-t*C)-((42*p*p-24)*t-3*B*(1+t*t)))==0
    L=p**3+12*p*p+39*p-26; k=(p-2)*(p*p-4*p+13)/L
    h=2-72*p*(p+4)/((p-1)*L);j=24*p*(p-2)*(p+4)/((p-1)*L);zx=2-24*p*(p+4)*(p-2)/((p-4)*L);zy=24*p*(p*p+2*p-26)/((p-4)*L)
    norm=(2*v)**2+(4*(sp.Rational(1,2)-v))**2;dot=(2-h)*2*v-j*4*(sp.Rational(1,2)-v)
    incidence=(2-zx)*(-2*dot*4*(sp.Rational(1,2)-v)-zy*norm)-(4*(1-k*t)-zy)*((2-zx)*norm-4*dot*v)
    factor=-384*p*(p-2)*(p+4)*(p*p-4*p+13)/((p-4)*(p-1)*L**2)
    assert sp.factor(incidence-factor*(N-t*D))==0
    return 'general discriminant, derivative and circle identities: exact'

def run():
    out={'symbolic':symbolic()}; errors=[]
    for p in [3,4,5,6,7,8,12,20,32]:
        for X in map(mp.mpf,['1.3','2','5']):
            a=X**(-mp.mpf(1)/p)
            for logt in map(mp.mpf,['-1.5','-.7','-.1','.1','.7','1.5']):
                s=a*mp.exp(logt/p)
                if abs(s-1)<mp.mpf('1e-100'):continue
                value,_=construct(p,X,s); expected=s*phi(p,X*s**p)
                errors.append(abs(value-expected))
                assert errors[-1]<mp.mpf('1e-210'),(p,X,s,errors[-1])
    out['independent_geometries']=len(errors);out['max_error']=mp.nstr(max(errors),8)
    a=mp.power(2,-mp.mpf(1)/3);s=mp.mpf(3)/4;hist=[]
    for i in range(4):
        hist.append({'iteration':i,'s':mp.nstr(s,90),'relative_error':mp.nstr(abs(s/a-1),12)})
        s=s*phi(3,2*s**3)
    out['benchmark_p3']=hist
    out['thresholds']={str(d):next(r['iteration'] for r in hist if mp.mpf(r['relative_error'])<=mp.power(10,-d)) for d in [6,12,30,60]}
    # Both roots are positive: disproves the sign-only selection in the prompt.
    t=mp.mpf('.05');r=mp.sqrt((42*9-24)*t-15*(1+t*t));out['two_positive_roots_at_t_005']=[str((20-2*t)/(5*(1-t)+eps*r)) for eps in [1,-1]]
    Path(__file__).with_name('results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':run()
