"""Independent line/circle construction and symbolic certificates. Not Lean."""
from pathlib import Path
import json
import mpmath as mp
import sympy as S

def join(a,b):return (a[1]-b[1],b[0]-a[0],a[0]*b[1]-b[0]*a[1])
def cross(l,m):
    a,b,c=l;d,e,f=m;det=a*e-b*d
    assert det
    return ((b*f-c*e)/det,(c*d-a*f)/det)
def parallel(l,p):return (l[0],l[1],-l[0]*p[0]-l[1]*p[1])
def geometry(p,X,s,mode='arc',W=2,H=4):
    X,s,W,H=map(mp.mpf,(X,s,W,H));p=mp.mpf(p)
    C=(mp.mpf(0),mp.mpf(0));B=(W,mp.mpf(0));O=(mp.mpf(0),H);A=(W,H)
    P=(W,H*(1-s));M=(mp.mpf(0),H*(1-1/X))
    base=join(C,B);left=join(C,O);right=join(B,A);diag=join(O,B)
    hor=parallel(base,P);L=cross(hor,left);Bj=cross(hor,diag);red=join(L,B)
    chain=[(L,Bj)];redsegments=[(L,B)]
    for j in range(2,int(p)+1):
        Ln=cross(parallel(red,Bj),left);redsegments.append((Bj,Ln))
        hor=parallel(base,Ln);Bj=cross(hor,diag);chain.append((Ln,Bj))
    E=cross(hor,right);t=X*s**int(p)
    pts=dict(C=C,B=B,O=O,A=A,P=P,M=M,E=E)
    if mode=='AK':
        K=(W*(1-X/p),mp.mpf(0));pts['K']=K;support=join(A,K)
    elif mode=='AD':
        F=(W-2*W/(p-1),H-H*(p+1)/(X*(p-1)));radius=abs(A[1]-E[1])
        D=(F[0],F[1]-radius);pts.update(F=F,D=D);support=join(A,D)
    elif mode=='projective':
        Z=(W*(1+(5*p-1)/(2*p*(2*p-1))),H*(1+(p+1)/((2*p-1)*X)))
        ell=H*(1+(5*p-1)/((p+1)*X));D=cross(join(Z,E),(0,1,-ell))
        pts.update(Z=Z,D=D);support=join(A,D)
    else:
        assert p>2
        beta=(p-1)*mp.sqrt((p-2)/(12*p));alpha=(5*p+2)/(p-2)
        d=W/beta;delta=H/X*mp.sqrt(alpha**2-1)
        F=(W-d+delta,H-H/(X*beta));G=(W,H+H*alpha/X)
        # Radius is the already available length EG, not the update formula.
        radius=mp.sqrt((E[0]-G[0])**2+(E[1]-G[1])**2)
        xD=W-d;D=(xD,F[1]-mp.sqrt(radius**2-(xD-F[0])**2))
        pts.update(F=F,G=G,D=D);support=join(A,D)
    green=join(M,E);T=cross(parallel(green,P),support)
    Pnext=cross(parallel(base,T),right);pts.update(T=T,Pnext=Pnext)
    return dict(points=pts,chain=chain,red=redsegments,support=support,green=green,
                value=1-Pnext[1]/H,radius=locals().get('radius'),t=t,mode=mode)

def correction(p,t):
    g=(p-1)*mp.sqrt(((p-2)*(t*t+1)+(10*p+4)*t)/(12*p))
    return (1+g)/(t+g)

def verify():
    p,t,q=S.symbols('p t q',positive=True)
    Q=((p-2)*(t*t+1)+(10*p+4)*t)/(12*p)
    A=(p-1)*(t*t+1)+(10*p+2)*t
    B=(t+1)*(6*p*t-(t-1)**2)
    K=(p*p-5*p-2)*(t-1)**2+12*p*(3*p+1)*t
    assert S.factor(Q*A*A-B*B-(p+1)*(t-1)**4*K/(12*p))==0
    g=(p-1)*q;gp=(p-1)*S.diff(Q,t)/(2*q)
    raw=g*(1+g)*(t+g)+p*t*((t-1)*g*gp-g*(1+g))
    pref=(p-2)*(p-1)**2/(12*p)
    assert S.rem(S.together(raw-pref*(q*A-B)),q*q-Q,q)==0
    assert S.factor(Q.subs(t,1/t)-Q/t**2)==0
    assert S.factor(K-6*p*p*(p+1)*t-(p*p-5*p-2)*((t-1)**2-6*p*t))==0
    # Explicit local Taylor contact for four sample degrees, independently of
    # the general derivative proof in the paper.
    u=S.symbols('u');coefficients={}
    for pp in [3,4,5,7]:
        gg=(pp-1)*S.sqrt(Q.subs({p:pp,t:1+u}))
        phi=S.series((1+gg)/(1+u+gg),u,0,6).removeO()
        err=S.series(phi-(1+u)**(-S.Rational(1,pp)),u,0,6).removeO().expand()
        c=S.factor(err.coeff(u,5)*pp**5)
        assert S.expand(err-err.coeff(u,5)*u**5)==0
        assert c==S.Rational((pp-2)*(pp*pp-1)*(3*pp+1),1440)
        coefficients[str(pp)]=str(c)
    mp.mp.dps=160;maximum=mp.mpf(0);count=0;other_errors={k:mp.mpf(0) for k in ['AK','AD','projective']}
    for pp in [3,4,5,7,12,32]:
        for X in ['0.5','2','7']:
            for tt in ['0.01','0.3','0.9','1.1','3','100']:
                tt=mp.mpf(tt);xx=mp.mpf(X);ss=(tt/xx)**(mp.mpf(1)/pp)
                got=geometry(pp,xx,ss)['value'];expected=ss*correction(pp,tt)
                maximum=max(maximum,abs(got-expected));count+=1
                aa=xx**(-mp.mpf(1)/pp)
                assert min(ss,aa)<got<max(ss,aa)
                assert abs(correction(pp,tt)*correction(pp,1/tt)-1)<mp.mpf('1e-150')
                formulas={'AK':ss*pp/(pp-1+tt),
                          'AD':ss*(pp+1+(pp-1)*tt)/(pp-1+(pp+1)*tt),
                          'projective':ss*2*pp*((2*pp-1)*tt+pp+1)/((pp+1)*tt**2+2*(2*pp-1)*(pp+1)*tt+(2*pp-1)*(pp-1))}
                for name,value in formulas.items():
                    actual=geometry(pp,xx,ss,name)['value']
                    other_errors[name]=max(other_errors[name],abs(actual-value))
                    assert abs(actual-value)<mp.mpf('1e-150')
    result={'symbolic':'Derivative numerator, squared identity, reciprocity and sign decomposition exact',
            'local_coefficients':coefficients,'independent_arc_geometries':count,
            'working_digits':160,'max_error':mp.nstr(maximum,12),
            'additional_geometries':{k:{'cases':count,'max_error':mp.nstr(v,12)} for k,v in other_errors.items()},
            'proof_scope':'Global monotone convergence proved in paper; finite checks do not replace proof.'}
    Path(__file__).with_name('verification.json').write_text(json.dumps(result,indent=2)+'\n')
    mp.mp.dps=280;aa=mp.power(2,-mp.mpf(1)/3);benchmark={}
    maps={'AK':lambda s,t:3*s/(2+t),'AD':lambda s,t:s*(4+2*t)/(2+4*t),
          'projective':lambda s,t:s*6*(5*t+4)/(4*t*t+40*t+10),
          'arc':lambda s,t:s*correction(3,t)}
    for name,fn in maps.items():
        ss=mp.mpf(3)/4;errors=[]
        while True:
            error=abs(ss/aa-1);errors.append(error)
            if error<=mp.mpf('1e-60'):break
            ss=fn(ss,2*ss**3)
        benchmark[name]={'steps':[next(i for i,e in enumerate(errors) if e<=mp.power(10,-d)) for d in [6,12,30,60]],
                         'errors':[mp.nstr(e,14) for e in errors]}
    Path(__file__).with_name('benchmark.json').write_text(json.dumps(benchmark,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':verify()
