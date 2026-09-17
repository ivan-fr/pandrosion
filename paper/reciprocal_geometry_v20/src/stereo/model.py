"""Projective incidences; similarity-normalized inverse stereographic display.
Sphere intersections are never used to compute projective incidences.
"""
import numpy as np

def cross(a,b):
    c=np.cross(a,b); m=np.max(np.abs(c))
    if m<1e-13: raise ValueError('Coincident points or lines')
    return c/m

def affine(q):
    if abs(q[2])<1e-12: return None
    return np.array(q[:2])/q[2]

def parameters(p):
    if p==4:return (1/3,13502/7167,3328/2389,-214/2389,2432/2389,145/2389)
    L=p**3+12*p*p+39*p-26
    return (.5,2-72*p*(p+4)/((p-1)*L),24*p*(p-2)*(p+4)/((p-1)*L),2-24*p*(p+4)*(p-2)/((p-4)*L),24*p*(p*p+2*p-26)/((p-4)*L),(p-2)*(p*p-4*p+13)/L)

def normalized(q):
    x,y,w=q
    return np.array([x-w,y-2*w,2*w]) # xi=(x-1)/2, eta=(y-2)/2

def stereo(q):
    x,y,w=normalized(q);d=x*x+y*y+w*w
    return np.array([2*x*w,2*y*w,x*x+y*y-w*w])/d

def sphere_line_coeff(l):
    a,b,c=l
    return np.array([2*a,2*b,a+2*b+c])

def line_samples(l,n=321):
    a,b,c=l;norm=np.hypot(a,b);base=-c*np.array([a,b])/(norm*norm);direction=np.array([-b,a])/norm
    theta=np.linspace(-np.pi/2,np.pi/2,n);cs=np.cos(theta);sn=np.sin(theta)
    return np.c_[base[0]*cs+direction[0]*sn,base[1]*cs+direction[1]*sn,cs]

def geometry(p=3,X=2,s=.75):
    if p<3 or X<=0 or s<=0: raise ValueError('p>=3 and X,s>0 required')
    rho,h,j,zx,zy,k=parameters(p);M=np.array([h,j]);radius=np.hypot(2-h,j)
    pts={name:np.array(val,dtype=float) for name,val in {'O':[0,4,1],'A':[2,4,1],'B':[2,0,1],'C':[0,0,1],'P':[2,4*(1-s),1],'Z':[zx,zy,1]}.items()}
    top=np.array([0,1,-4.]);left=np.array([1,0,0.]);right=np.array([1,0,-2.]);ops=[]
    def meet(a,b,rail,name):
        l=cross(pts[a],pts[b]);pt=cross(l,rail);pts[name]=pt;ops.append((a,b,name,l));return name
    meet('C','P',top,'V');curr='P'
    for i in range(1,p):
        f=rho if i==1 else k*X*2**(p-3)/rho if i==p-1 else .5
        hub='F'+str(i);pts[hub]=np.array([2*f,4*(f-1),f-1])
        a=meet(hub,curr,left,'L'+str(i));curr=meet('V',a,right,'T' if i==p-1 else 'Q'+str(i))
    l=cross(pts['Z'],pts['T']);a,b,c=l;norm=np.hypot(a,b);dist=(a*h+b*j+c)/norm;d2=radius*radius-dist*dist
    if d2<=1e-13:raise ValueError('Outside the transverse circle domain')
    foot=M-dist*np.array([a,b])/norm;offset=np.sqrt(d2)*np.array([-b,a])/norm
    candidates=[]
    for xy in [foot+offset,foot-offset]:
        dx=xy[0]-2;dy=xy[1];den=4*dx+2*dy
        v=rho*4*dx/den if abs(den)>1e-14 else np.inf
        slope=(p*p-4)*(v*v+1)-2*(p*p+2)*v
        candidates.append((slope,xy,v))
    good=[z for z in candidates if z[0]<0]
    if len(good)!=1:raise ValueError('Cannot distinguish inverse branch')
    chosen=good[0];pts['G']=np.r_[chosen[1],1.];pts['Gother']=np.r_[next(z[1] for z in candidates if z is not chosen),1.]
    ops.append(('Z','T','G',l));meet('B','G',top,'U');meet('U','L1',right,'Pnext')
    value=1-affine(pts['Pnext'])[1]/4
    return dict(p=p,X=X,s=s,rho=rho,k=k,M=M,radius=radius,points=pts,ops=ops,value=value)

def verify():
    cases=0;maxerr=0;maxsphere=0;maxline=0;maxcircle=0
    for p in [3,4,5,7,12]:
      for X in [1.3,2,5]:
       for logt in [-1.5,-.4,0,.4,1.5]:
        s=(np.exp(logt)/X)**(1/p);g=geometry(p,X,s);t=X*s**p;A=(p+1)*(p+2);B=p*p-4;C=(p-1)*(p-2);disc=(42*p*p-24)*t-3*B*(1+t*t)
        v=(A-t*C)/(B*(1-t)+np.sqrt(disc)) if t<=1 else (np.sqrt(disc)-B*(1-t))/(t*A-C)
        maxerr=max(maxerr,abs(g['value']-s*v));assert abs(g['value']-s*v)<1e-8
        for pt in g['points'].values():maxsphere=max(maxsphere,abs(np.dot(stereo(pt),stereo(pt))-1))
        for *_,l in g['ops']:
            abc=sphere_line_coeff(l)
            for pt in line_samples(l,25):
                z=stereo(pt);err=abs(abc[0]*z[0]+abc[1]*z[1]+abc[2]*(1-z[2]));maxline=max(maxline,err)
        center=(g['M']-np.array([1,2]))/2;rad=g['radius']/2;c=np.dot(center,center)-rad*rad
        for theta in np.linspace(0,2*np.pi,40):
            world=g['M']+g['radius']*np.array([np.cos(theta),np.sin(theta)]);z=stereo(np.r_[world,1]);err=abs(-2*center[0]*z[0]-2*center[1]*z[1]+(1-c)*z[2]+1+c);maxcircle=max(maxcircle,err)
        cases+=1
    special=[]
    for label,p,X,s in [('initial infinity',3,2,1.),('final infinity',3,2,(7.75/2)**(1/3)),('fixed infinity',3,113/10,.75)]:
        g=geometry(p,X,s);special.append({'case':label,'value':g['value'],'infinite_points':[name for name,q in g['points'].items() if affine(q) is None]})
    assert maxsphere<1e-12 and maxline<1e-11 and maxcircle<1e-11
    return {'cases':cases,'max_formula_error':maxerr,'max_sphere_residual':maxsphere,'max_line_plane_residual':maxline,'max_circle_plane_residual':maxcircle,'infinity_cases':special}
if __name__=='__main__':
    from pathlib import Path
    import json
    result=verify();Path(__file__).with_name('verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
