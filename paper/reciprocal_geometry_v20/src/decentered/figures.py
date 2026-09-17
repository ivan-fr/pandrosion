from pathlib import Path
import sys
import numpy as np
import mpmath as mp
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from verify import geometry
OUT=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parents[2]/'figures'
OUT.mkdir(parents=True,exist_ok=True)
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':8.5,'axes.titlesize':10,'pdf.fonttype':42})
BLUE='#176B9B';GREEN='#398465';ORANGE='#BB641F';GRAY='#a6b2b9';DARK='#253640'
def seg(ax,a,b,**kw):ax.plot(*np.array([a,b],dtype=float).T,**kw)
def draw(ax,mode):
    g=geometry(3,2,mp.mpf(3)/4,mode);P=g['points'];ax.set_aspect('equal');ax.axis('off')
    for a,b in [('O','A'),('A','B'),('B','C'),('C','O'),('O','B')]:seg(ax,P[a],P[b],c=GRAY,lw=.9)
    for a,b in g['chain']:seg(ax,a,(2,a[1]),c=GRAY,lw=.65)
    for a,b in g['red']:seg(ax,a,b,c=GRAY,lw=.65)
    for a,b in [('M','E'),('P','T')]:seg(ax,P[a],P[b],c=GREEN,lw=1.4)
    seg(ax,P['T'],P['Pnext'],c=BLUE,lw=1.1)
    if mode=='AK':seg(ax,P['A'],P['K'],c=BLUE,lw=1.6);labels=['O','A','B','C','M','E','P','T','Pnext','K'];lim=(-.6,2.7,-.55,4.7)
    elif mode=='AD':
        seg(ax,P['A'],P['D'],c=BLUE,lw=1.6);seg(ax,(P['F'][0],float(P['D'][1])-.4),P['O'],c=GRAY,lw=.9,ls='--')
        theta=np.linspace(-np.pi*.85,-np.pi*.15,100);F=np.array(P['F'],float);r=float(g['radius']);ax.plot(F[0]+r*np.cos(theta),F[1]+r*np.sin(theta),c=ORANGE,lw=1.4)
        seg(ax,P['F'],P['D'],c=ORANGE,lw=.8,ls=':');seg(ax,P['A'],P['E'],c=ORANGE,lw=2.5,alpha=.45)
        labels=['O','A','B','F','M','E','P','T','Pnext','D'];lim=(-1.9,2.8,-2.3,4.7)
    elif mode=='projective':
        seg(ax,P['E'],P['D'],c=ORANGE,lw=1.3);seg(ax,P['A'],P['D'],c=BLUE,lw=1.6)
        y=float(P['D'][1]);seg(ax,(-.4,y),(5.2,y),c=ORANGE,lw=.9,ls='--');ax.text(.1,y+.2,'ℓ (fixed)',color=ORANGE)
        labels=['O','A','B','C','M','E','P','T','Pnext','Z','D'];lim=(-.6,5.4,-.5,12)
    else:
        F=np.array(P['F'],float);D=np.array(P['D'],float);r=float(g['radius']);ang=np.arctan2(D[1]-F[1],D[0]-F[0]);theta=np.linspace(ang-.28,ang+.32,120)
        ax.plot(F[0]+r*np.cos(theta),F[1]+r*np.sin(theta),c=ORANGE,lw=1.6)
        seg(ax,P['F'],P['D'],c=ORANGE,lw=.85,ls=':');seg(ax,P['E'],P['G'],c=ORANGE,lw=2)
        seg(ax,(D[0],D[1]-1),(D[0],5),c=GRAY,lw=1,ls='--');seg(ax,P['A'],P['D'],c=BLUE,lw=1.6)
        seg(ax,F,(D[0],F[1]),c=GRAY,lw=.8,ls=':');ax.text((D[0]+F[0])/2,F[1]+1,'δ',color=GRAY)
        labels=['O','A','B','C','F','G','D'];lim=(D[0]-5,F[0]+5,D[1]-4,float(P['G'][1])+4)
        ax.text(3,20,'radius EG',rotation=90,color=ORANGE,fontsize=8)
        inset=ax.inset_axes([.46,.58,.48,.32]);inset.set_aspect('equal');inset.set(xlim=(-.4,3.2),ylim=(-.3,4.6));inset.set_xticks([]);inset.set_yticks([]);inset.set_title('Correction detail',fontsize=8)
        for aa,bb in [('O','A'),('A','B'),('B','C'),('C','O')]:seg(inset,P[aa],P[bb],c=GRAY,lw=.7)
        for aa,bb in [('M','E'),('P','T')]:seg(inset,P[aa],P[bb],c=GREEN,lw=1)
        seg(inset,P['A'],P['T'],c=BLUE,lw=1.2);seg(inset,P['T'],P['Pnext'],c=BLUE,lw=1)
        for name in ['A','E','P','T','Pnext']:
            pt=np.array(P[name],float);inset.scatter(*pt,s=8,c=DARK);inset.annotate({'Pnext':'P⁺'}.get(name,name),pt,xytext={'A':(5,3),'E':(5,4),'P':(5,0),'T':(-12,-5),'Pnext':(5,-12)}[name],textcoords='offset points',fontsize=7)
    offsets={'O':(-12,7),'A':(7,6),'B':(6,-12),'C':(-12,-12),'F':(7,0),'M':(-16,-2),'E':(7,7),'P':(7,-3),'T':(-14,-10),'Pnext':(7,-14),'K':(-7,-14),'D':(-15,-8),'Z':(7,-2),'G':(7,0)}
    for name in labels:
        pt=np.array(P[name],float);ax.scatter(*pt,s=12,c=DARK,zorder=5)
        ax.annotate({'Pnext':'P⁺','F':'F = C' if mode=='AD' else 'F'}.get(name,name),pt,xytext=offsets[name],textcoords='offset points',fontsize=8,
          arrowprops={'arrowstyle':'-','color':GRAY,'lw':.4} if name in ['Pnext','T'] else None)
    ax.set(xlim=lim[:2],ylim=lim[2:])
    return g
fig,axs=plt.subplots(1,2,figsize=(6.6,4.8),layout='constrained')
for ax,mode,title in zip(axs,['AK','AD'],['(a) Pandrosion AK · order 2','(b) Pandrosion AD · order 3']):draw(ax,mode);ax.set_title(title)
fig.savefig(OUT/'pandrosion_ak_ad.pdf',bbox_inches='tight');fig.savefig(OUT/'pandrosion_ak_ad.png',dpi=170,bbox_inches='tight');plt.close(fig)
fig,axs=plt.subplots(1,2,figsize=(6.6,5.8),layout='constrained')
for ax,mode,title in zip(axs,['projective','arc'],['(a) Projective AD [2/1] · order 4','(b) Decentered AD arc · order 5']):draw(ax,mode);ax.set_title(title)
fig.savefig(OUT/'pandrosion_projective_arc.pdf',bbox_inches='tight');fig.savefig(OUT/'pandrosion_projective_arc.png',dpi=170,bbox_inches='tight');plt.close(fig)
print(OUT)
