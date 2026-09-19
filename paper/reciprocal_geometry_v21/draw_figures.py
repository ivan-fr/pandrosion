"""Readable, independently scaled construction views for the geometry-first V21."""
from pathlib import Path
import sys
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Circle
ROOT=Path(__file__).parent
sys.path.insert(0,str(ROOT.parent/'reciprocal_geometry_v20/src/fixed_circle'))
from verify import construct
v,lines=construct(3,2,.75)
lines=[(np.array(a,dtype=float),np.array(b,dtype=float),n) for a,b,n in lines]
Z,T=lines[5][:2];B,G=lines[6][:2];U,L=lines[7][:2];Pp=np.array([2.,4*(1-float(v))]);center=np.array([-152/113,126/113]);radius=np.linalg.norm(B-center)
blue='#176b9b';orange='#bd5a20';ink='#253640';gray='#b9c3c8'
def seg(ax,a,b,c=gray,ls='-',lw=1.3):ax.plot(*zip(a,b),color=c,ls=ls,lw=lw)
def pt(ax,p,label,off=(5,5),c=ink):
 ax.plot(*p,'o',ms=4,color=c);ax.annotate(label,p,xytext=off,textcoords='offset points',fontsize=12,color=c)
fig,axes=plt.subplots(1,2,figsize=(10.8,5.1),layout='constrained')
a=axes[0];a.set_aspect('equal');a.set_xlim(-5.2,5);a.set_ylim(-2.7,5.6);a.axis('off');a.set_title('(a) The prepared circle solves the quadratic',fontsize=13)
a.add_patch(Circle(center,radius,fill=False,ec=orange,lw=2));seg(a,Z,G,blue,lw=2);seg(a,B,G,ink,lw=1.5)
for x in [0,2]:seg(a,[x,0],[x,4])
seg(a,[-2.2,4],[4.5,4]);seg(a,[0,0],[2,0]);
for p,l,o in [(Z,'Z',(6,-10)),(T,'T',(4,8)),(G,'G',(-18,8)),(B,'B',(5,-10)),(center,r'$O_\Gamma$',(5,-13))]:pt(a,p,l,o)
# Join labels are in the caption, leaving the circle boundary unobstructed.
a=axes[1];a.set_aspect('equal');a.set_xlim(-2.35,2.8);a.set_ylim(.3,4.65);a.axis('off');a.set_title('(b) The last join reads the correction',fontsize=13)
seg(a,[-2.2,4],[2.3,4]);seg(a,[0,.5],[0,4.2]);seg(a,[2,.5],[2,4.2]);seg(a,U,Pp,blue,lw=2)
for p,l,o in [(U,'U',(-12,8)),(L,r'$L_1$',(5,7)),(Pp,r'$P^+$',(6,-12)),(np.array([2.,1.]),'P',(6,5))]:pt(a,p,l,o)
a.text(-2.1,.55,r'$L_1=L(\rho s)$'+'\n'+r'$U=\mathcal{U}_{\rho/v}$'+'\n'+r'$P^+=R(sv)$',fontsize=12)
fig.savefig(ROOT/'figures/fixed_circle.pdf');fig.savefig(ROOT/'figures/fixed_circle.png',dpi=180)
# Decentered arc: full circle geometry and separate, undistorted local report.
p=7;X=W=2.;H=4.;s=.75;t=X*s**p
beta=(p-1)*np.sqrt((p-2)/(12*p));alpha=(5*p+2)/(p-2);d=W/beta;delta=H/X*np.sqrt(alpha**2-1)
F=np.array([W-d+delta,H-H/(X*beta)]);rad=H/X*(t+alpha)
D=np.array([W-d,F[1]-np.sqrt(rad**2-delta**2)])
A=np.array([W,H]);E=np.array([W,H*(1-s**p)]);M=np.array([0,H*(1-1/X)]);P=np.array([W,H*(1-s)])
k=(D[1]-H)/(D[0]-W);m=(E[1]-M[1])/W
T=np.array([W-H*s/(k-m),H-k*H*s/(k-m)]);out=np.array([W,T[1]])
g=(p-1)*np.sqrt(((p-2)*(t*t+1)+(10*p+4)*t)/(12*p))
assert abs(1-out[1]/H-s*(1+g)/(t+g))<1e-12
fig,axes=plt.subplots(1,2,figsize=(10.8,5.0),layout='constrained')
a=axes[0];a.set_aspect('equal');a.axis('off');a.set_xlim(F[0]-rad-1,F[0]+rad+1);a.set_ylim(F[1]-rad-3,F[1]+rad+2);a.set_title('(a) A displaced center leaves a square root',fontsize=13)
a.add_patch(Circle(F,rad,fill=False,ec=orange,lw=2));seg(a,[D[0],D[1]-2],[D[0],F[1]+8],blue);seg(a,F,D,gray,ls='--');seg(a,F,[D[0],F[1]],gray,ls=':')
pt(a,F,r'$O_{arc}$',(5,7));pt(a,D,r'$D_{arc}$',(5,-14));
G0=np.array([W,H+H*alpha/X]);seg(a,E,G0,orange,lw=1.3);pt(a,E,'E',(6,-10));pt(a,G0,r'$G_0$',(6,0));a.text(F[0]-5,F[1]+rad*.55,r'$\mathrm{radius}=EG_0$',fontsize=12);a.text(F[0]-rad*.62,F[1]-rad*.7,r'$x_D=W-d_0$'+'\n'+r'$|y_D-y_{O_{arc}}|=\sqrt{EG_0^2-\delta^2}$',fontsize=12)
a=axes[1];a.set_aspect('equal');a.axis('off');a.set_xlim(-1.0,3.2);a.set_ylim(min(-1,D[1]-1.2),5);a.set_title('(b) Local support and horizontal readout',fontsize=13)
for u,w in [([0,0],[0,H]),([0,H],A),(A,[W,0]),([W,0],[0,0])]:seg(a,u,w)
# The original triangle power stage remains visible behind the support.
seg(a,[0,H],[W,0],gray,lw=.7)
prev=np.array([W*s,H*(1-s)])
for jj in range(1,p+1):
    left=np.array([0,H*(1-s**jj)]);bj=np.array([W*s**jj,left[1]])
    seg(a,left,[W,left[1]],gray,lw=.5)
    if jj==1:seg(a,left,[W,0],'#c5a29b',lw=.6)
    else:seg(a,prev,left,'#c5a29b',lw=.6)
    prev=bj
seg(a,A,D,blue,lw=2);seg(a,M,E,orange,lw=2);seg(a,P,T,orange,lw=2);seg(a,T,out,blue,lw=2)
for q,l,o in [(A,'A',(5,6)),(D,r'$D_{arc}$',(-34,-14)),(M,'M',(-18,4)),(E,'E',(6,8)),(P,'P',(7,2)),(out,r'$P^+$',(7,-14)),(T,'T',(-16,-5))]:pt(a,q,l,o)
fig.savefig(ROOT/'figures/decentered_arc.pdf');fig.savefig(ROOT/'figures/decentered_arc.png',dpi=180)
print('PASS: fixed-circle and decentered-arc readouts; independent equal-axis views')
