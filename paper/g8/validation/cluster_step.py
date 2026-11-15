import mpmath as mp
mp.mp.dps=120
def run(K,sep,d,label):
    cl=[mp.mpf(1)+sep*(j-(K-1)/mp.mpf(2))*(1+mp.mpf(j)/7) for j in range(K)]
    out=[mp.mpf(-2),mp.mpc(3,1)]
    roots=cl+out
    def logder(w):
        return mp.fsum([1/(w-r) for r in roots]),mp.fsum([1/(w-r)**2 for r in roots])
    z=[1+d*mp.exp(2j*mp.pi*(k+0.3)/K) for k in range(K)]
    zo=[r*(1+mp.mpf('1e-9')) for r in out]
    g0=mp.fsum(cl)/K
    spread=lambda pts:max(abs(p-g0) for p in pts)
    print(label,'| cluster radius',mp.nstr(max(abs(r-g0) for r in cl),3),'| start distance',mp.nstr(d,3))
    pts=z[:]
    for it in range(1,7):
        new=[]
        for k,w in enumerate(pts):
            A,B=logder(w)
            A-=mp.fsum([1/(w-y) for l,y in enumerate(pts) if l!=k])+mp.fsum([1/(w-y) for y in zo])
            B-=mp.fsum([1/(w-y)**2 for l,y in enumerate(pts) if l!=k])+mp.fsum([1/(w-y)**2 for y in zo])
            p=len(roots);t=(p*B-A*A)/((p-1)*A*A);q=(1+t)/2
            new.append(w-p/(A*(1+(p-1)*q)))
        pts=new
        print('   present sweep',it,'-> distance to the cluster',mp.nstr(spread(pts),3))
    w=z[0]
    A,B=logder(w)
    A-=mp.fsum([1/(w-y) for y in zo]);B-=mp.fsum([1/(w-y)**2 for y in zo])
    p=K;t=(p*B-A*A)/((p-1)*A*A)
    N=1/A;u=p*N/(1-t)
    g=w-u;r=u*mp.root(t,p)
    model=[g+r*mp.exp(2j*mp.pi*j/p) for j in range(p)]
    print('   cluster step (one evaluation): centre error',mp.nstr(abs(g-g0),3),'| radius of the K points',mp.nstr(abs(r),3),'| distance to the cluster',mp.nstr(spread(model),3))
    print('   nearest-root distances / spacing:',[mp.nstr(min(abs(m_-c) for c in cl)/sep,2) for m_ in model])
run(5,mp.mpf('1e-30'),mp.mpf('1e-3'),'five roots 1e-30 apart')
run(2,mp.mpf('1e-48'),mp.mpf('1e-9'),'pair 1e-48 apart (Mignotte-like)')
run(3,mp.mpf('1e-12'),mp.mpf('1e-2'),'three roots 1e-12 apart')
