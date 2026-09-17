from pathlib import Path
import json,sys
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import mpmath as mp
from model import geometry,affine,stereo,line_samples
OUT=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parents[2]/'figures'
OUT.mkdir(parents=True,exist_ok=True)
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':8.5,'axes.titlesize':9,'axes.labelsize':8.5,'pdf.fonttype':42,'axes.spines.top':False,'axes.spines.right':False})
BLUE='#176B9B';ORANGE='#BB641F';GRAY='#81909A';DARK='#253640';GREEN='#397964'
def save(fig,name):
    fig.savefig(OUT/(name+'.pdf'),bbox_inches='tight');fig.savefig(OUT/(name+'.png'),dpi=150,bbox_inches='tight');plt.close(fig)
def plane(ax,g,n,limits=None,numbered=False):
    pts=g['points'];h,j=g['M'];r=g['radius'];theta=np.linspace(0,2*np.pi,361)
    ax.plot(h+r*np.cos(theta),j+r*np.sin(theta),c=ORANGE,lw=1.35,label='Fixed circle Γ')
    for a,b in [('O','A'),('A','B'),('B','C'),('C','O')]:
        v=np.array([affine(pts[a]),affine(pts[b])]);ax.plot(*v.T,c=GRAY,lw=.8)
    for i,(a,b,name,l) in enumerate(g['ops'][:n]):
        aa,bb,cc=l;d=aa*aa+bb*bb;base=-cc*np.array([aa,bb])/d;direction=np.array([-bb,aa])/np.sqrt(d);v=np.array([base-30*direction,base+30*direction]);ax.plot(*v.T,c=BLUE if i==n-1 else GRAY,lw=1.65 if i==n-1 else .7,alpha=1 if i==n-1 else .55)
        pt=affine(pts[name])
        if numbered and pt is not None and i<n-1:
            ax.annotate(str(i+1),pt,xytext=(-7,-13),textcoords='offset points',fontsize=8,color=BLUE)
    names=['O','A','B','C','P',g['ops'][n-1][2]] if n else ['O','A','B','C','P']
    if n>=2*g['p']:names+=['G','Gother','T','Z']
    if n>=2*g['p']+1:names+=['U','L1']
    if n>=1:names+=['V']
    offsets={'P':(7,8),'Pnext':(7,-15),'O':(-15,6),'A':(8,10),'B':(8,-12),'C':(-15,-10),'T':(7,-15),'G':(-16,10),'Gother':(6,12),'U':(-18,-12),'Z':(8,3),'L1':(-22,0),'V':(3,10)}
    for name in dict.fromkeys(names):
        pt=affine(pts[name])
        if pt is None:continue
        ax.scatter(*pt,s=13,c=BLUE if name==g['ops'][n-1][2] else DARK,zorder=4)
        ax.annotate({'Pnext':'P⁺','Gother':'G′','L1':'L₁'}.get(name,name),pt,xytext=offsets.get(name,(5,8)),textcoords='offset points',fontsize=8,arrowprops={'arrowstyle':'-','lw':.4,'color':GRAY} if name in ['Pnext','T','U'] else None)
    if limits is None:limits=(min(h-r-.4,-2.5),max(h+r+.7,4.8),min(j-r-.4,-.5),max(j+r+.6,4.9))
    ax.set(xlim=limits[:2],ylim=limits[2:],aspect='equal',xlabel='x',ylabel='y')
    ax.grid(alpha=.13)
def sphere(ax,g,n,yaw=-.61,pitch=.38):
    def project(z):
        x=np.cos(yaw)*z[0]-np.sin(yaw)*z[1];y=np.sin(yaw)*z[0]+np.cos(yaw)*z[1]
        return np.array([x,np.cos(pitch)*z[2]-np.sin(pitch)*y,np.sin(pitch)*z[2]+np.cos(pitch)*y])
    def curve(z,color,lw=1,alpha=1):
        arr=np.array([project(a) for a in z]);front=arr[:,2]>=0
        for mask,style,opacity in [(front,'-',alpha),(~front,'--',alpha*.28)]:
            vv=arr[:,:2].copy();vv[~mask]=np.nan;ax.plot(*vv.T,c=color,lw=lw,ls=style,alpha=opacity)
    t=np.linspace(0,2*np.pi,361);ax.plot(np.cos(t),np.sin(t),c=GRAY,lw=.7)
    for lat in [-.6,0,.6]:curve(np.c_[np.sqrt(1-lat*lat)*np.cos(t),np.sqrt(1-lat*lat)*np.sin(t),np.full_like(t,lat)],GRAY,.5,.45)
    for l in [[0,1,-4],[1,0,0],[1,0,-2]]:curve([stereo(q) for q in line_samples(l)],GRAY,.6,.45)
    h,j=g['M'];r=g['radius'];curve([stereo([h+r*np.cos(a),j+r*np.sin(a),1]) for a in t],ORANGE,1.8)
    for i,(*_,line) in enumerate(g['ops'][:n]):curve([stereo(q) for q in line_samples(line)],BLUE if i==n-1 else GRAY,1.8 if i==n-1 else .65,1 if i==n-1 else .45)
    current=g['ops'][n-1][2];inf=affine(g['points'][current]) is None
    labels=[('N' if not inf else current+' = N',np.array([0,0,1]),(3,12))]
    if not inf:labels.append(({'Pnext':'P⁺'}.get(current,current),stereo(g['points'][current]),(8,-16)))
    if n>=2*g['p']:labels += [('G',stereo(g['points']['G']),(-18,9))] if current!='G' else []
    for name,z,off in labels:
        xy=project(z)[:2];ax.scatter(*xy,s=20,c=BLUE,zorder=5);ax.annotate(name,xy,xytext=off,textcoords='offset points',fontsize=9,arrowprops={'arrowstyle':'-','lw':.4,'color':GRAY})
    ax.set(xlim=(-1.16,1.16),ylim=(-1.16,1.2),aspect='equal');ax.axis('off')
g=geometry()
fig,axs=plt.subplots(1,2,figsize=(6.6,3.3),layout='constrained')
plane(axs[0],g,5,(-5.3,8.8,-2.8,5.3));axs[0].set_title('(a) Five telescope joins')
plane(axs[1],g,8);axs[1].set_title('(b) Circle crossing and readout')
save(fig,'fixed_circle_construction')
fig,axs=plt.subplots(2,2,figsize=(6.6,6.1),layout='constrained')
for row,s in enumerate([.75,1.]):
    gg=geometry(s=s);n=6 if row==0 else 1
    plane(axs[row,0],gg,n);axs[row,0].set_title('Plane: circle crossing' if row==0 else 'Plane: CP parallel to OA')
    sphere(axs[row,1],gg,n);axs[row,1].set_title('Sphere: Γ excludes N' if row==0 else 'Sphere: V reaches N')
save(fig,'stereographic_circle')
fig,axs=plt.subplots(1,2,figsize=(6.6,2.85),layout='constrained');p=3;A=20;B=5;C=2
v=np.geomspace(.05,20,1200);R=(C*v*v-2*B*v+A)/(A*v*v-2*B*v+C);vminus=(11-np.sqrt(96))/5;vplus=1/vminus;mask=(v>vminus)&(v<vplus)
axs[0].plot(np.log(v),np.log(R),c=GRAY,lw=1.2,label='Other branches');axs[0].plot(np.log(v[mask]),np.log(R[mask]),c=BLUE,lw=2,label='Selected branch');axs[0].scatter([0],[0],c=BLUE,s=20);axs[0].annotate('v = t = 1',(0,0),xytext=(10,10),textcoords='offset points');axs[0].axhline(np.log(.05),c=ORANGE,lw=.8,ls='--');axs[0].set(xlabel='log v',ylabel='log R(v)',title='The inverse is branch-dependent (p = 3)');axs[0].legend(fontsize=7)
ps=np.arange(3,51);z=(7*ps*ps-4)/(ps*ps-4);upper=z+np.sqrt(z*z-1);lower=1/upper
axs[1].fill_between(ps,lower,upper,color=BLUE,alpha=.10);axs[1].plot(ps,upper,c=BLUE);axs[1].plot(ps,lower,c=BLUE);axs[1].set(yscale='log',xlabel='Root degree p',ylabel='Admissible residual t',title='Real transverse domain Δ > 0');axs[1].axhline(7+4*np.sqrt(3),c=GRAY,lw=.8,ls='--');axs[1].axhline(7-4*np.sqrt(3),c=GRAY,lw=.8,ls='--');axs[1].text(22,17,'τ₊ → 7 + 4√3',fontsize=8);axs[1].text(22,.045,'τ₋ → 7 − 4√3',fontsize=8)
for ax in axs:ax.grid(alpha=.15)
save(fig,'branch_domain')
mp.mp.dps=280;p=3;X=mp.mpf(2);target=X**(-mp.mpf(1)/p)
def radical(s,t):
    d=(42*p*p-24)*t-3*(p*p-4)*(1+t*t);r=mp.sqrt(d)
    v=((p+1)*(p+2)-t*(p-1)*(p-2))/((p*p-4)*(1-t)+r) if t<=1 else (r-(p*p-4)*(1-t))/(t*(p+1)*(p+2)-(p-1)*(p-2))
    return s*v
methods=[('Pencil Halley',BLUE,9,lambda s,t:s*(4+2*t)/(2+4*t)),('Rational [2/2]',GREEN,13,lambda s,t:s*(10*t*t+70*t+28)/(28*t*t+70*t+10)),('Fixed circle',ORANGE,8,radical)]
fig,axs=plt.subplots(1,2,figsize=(6.6,2.9),layout='constrained');data={}
for name,color,cost,fn in methods:
    s=mp.mpf(3)/4;digits=[];errs=[]
    for i in range(5):
        err=abs(s/target-1);errs.append(mp.nstr(err,16));digits.append(float(-mp.log10(err)) if err else 280);s=fn(s,X*s**p)
    counts=[next(i for i,d in enumerate(digits) if d>=goal) for goal in [6,12,30,60]];data[name]={'digits':digits,'errors':errs,'steps':counts,'lines':[cost*c for c in counts]}
    axs[0].plot(range(5),np.minimum(digits,200),'-o',ms=4,c=color,label=name)
    axs[1].plot([6,12,30,60],data[name]['lines'],'-o',ms=4,c=color,label=name)
axs[0].set(xlabel='Iteration',ylabel='Correct relative decimal digits',title='p = 3, X = 2, s₀ = 3/4',ylim=(0,205),xticks=range(5));axs[0].legend(fontsize=7)
axs[1].set(xlabel='Requested relative decimal digits',ylabel='Mobile straight lines',title='Same start; fixed preparation excluded',xticks=[6,12,30,60]);axs[1].legend(fontsize=7)
for ax in axs:ax.grid(alpha=.15)
save(fig,'accuracy_work');(OUT.parent/'data'/'benchmark.json').write_text(json.dumps(data,indent=2)+'\n')
fig,axs=plt.subplots(1,2,figsize=(6.6,3.4),layout='constrained')
for ax,p in zip(axs,[4,7]):
    gg=geometry(p,2,2**(-1/p)*.95);plane(ax,gg,2*p+2);ax.set_title(f'p = {p}: {2*p+2} mobile joins'+(' (ρ = 1/3)' if p==4 else ' (ρ = 1/2)'))
save(fig,'general_degrees')
# Classical enclosure/center, retained because it supplies exact acceptance bounds.
fig,axs=plt.subplots(1,2,figsize=(6.6,2.85),layout='constrained');Rs=np.geomspace(.25,4,401);p=3;lower=Rs*(p/(Rs+p-1))**(p-1);upper=Rs*((p-1+1/Rs)/p)**(p-1);root=Rs**(1/p);center=np.sqrt(lower*upper)
axs[0].fill_between(Rs,lower,upper,color=BLUE,alpha=.10);axs[0].plot(Rs,lower,c=BLUE,lw=1,label='Bilateral bounds');axs[0].plot(Rs,upper,c=BLUE,lw=1);axs[0].plot(Rs,root,c=DARK,lw=1.6,label='Exact cube root');axs[0].plot(Rs,center,c=ORANGE,lw=1.3,label='Geometric center');axs[0].set(xlabel='Residual R',ylabel='Correction factor',title='Classical bounds remain useful');axs[0].legend(fontsize=7)
a,b=mp.mpf(8)/9,mp.mpf(2);a,b=float(a),float(b);cx=(b-a)/2;radius=(a+b)/2;theta=np.linspace(0,np.pi,301);axs[1].plot(cx+radius*np.cos(theta),radius*np.sin(theta),c=ORANGE);axs[1].plot([-a,b],[0,0],c=GRAY);h=np.sqrt(a*b);axs[1].plot([0,0],[0,h],c=BLUE,lw=1.8);axs[1].scatter([-a,0,b,0],[0,0,0,h],c=DARK,s=15)
for text,point,off in [('−a',(-a,0),(-8,-15)),('0',(0,0),(-3,-15)),('b',(b,0),(-2,-15)),('√(ab)',(0,h),(8,3))]:axs[1].annotate(text,point,xytext=off,textcoords='offset points')
axs[1].set(aspect='equal',xlim=(-1.2,2.3),ylim=(-.3,1.65),title='Mean-proportional center: a = 8/9, b = 2');axs[1].axis('off');save(fig,'bilateral_center')
print(OUT)
