"""Coordinate-derived fast-power geometry; checks parallels and final AD report."""
from pathlib import Path
import json
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import FancyArrowPatch
ROOT=Path(__file__).parent
W,H=2.,4.;U=np.array([W+H,H]);B=np.array([W,0.]);A=np.array([W,H])
R=lambda v:np.array([W,H*(1-v)])
Z=lambda v:np.array([W+H*v,H])
def cross(v,w):return v[0]*w[1]-v[1]*w[0]
def mul(a,b):
 # Copy R(a) along UB to y=H; then through that point parallel to UR(b).
 ra=R(a);rb=R(b);top=ra+(H-ra[1])/(B-U)[1]*(B-U)
 out=top+(W-top[0])/(rb-U)[0]*(rb-U)
 assert np.allclose(top,Z(a)) and np.allclose(out,R(a*b))
 return out
fig=plt.figure(figsize=(10,7.4),layout='constrained');gs=fig.add_gridspec(2,2,height_ratios=[4,1.25])
blue='#137c82';orange='#bc571c';gray='#9caeb4';ink='#193944'
def line(ax,p,q,c=gray,ls='-',lw=1.3):ax.plot([p[0],q[0]],[p[1],q[1]],color=c,ls=ls,lw=lw)
def point(ax,p,name,offset=(5,5),c=ink):
 ax.plot(*p,'o',ms=4,color=c);ax.annotate(name,p,xytext=offset,textcoords='offset points',fontsize=10,color=c)
def setup(ax):
 ax.set_aspect('equal');ax.set_xlim(-.35,6.5);ax.set_ylim(-.35,4.65);ax.axis('off')
 line(ax,[-.1,H],[6.25,H]);line(ax,[W,-.2],[W,4.2]);point(ax,A,'A',(-14,8));point(ax,B,'B',(-14,-12));point(ax,U,r'$U_\times$',(5,8));line(ax,U,B,ls='--')
ax=fig.add_subplot(gs[0,0]);setup(ax);ax.set_title('(a) One geometric multiplication',loc='left',fontsize=13,pad=15)
a,b=.64,.42;out=mul(a,b)
line(ax,R(a),Z(a),blue,ls='--',lw=2);line(ax,U,R(b),orange,lw=2);line(ax,Z(a),out,orange,lw=2)
point(ax,R(a),r'$R(a)$',(-44,-6),blue);point(ax,R(b),r'$R(b)$',(-44,-4),orange)
point(ax,Z(a),r'$Z(a)$',(-12,10),blue);point(ax,out,r'$R(ab)$',(-47,2),orange)
ax.text(2.5,.35,r'Dashed teal: copy parallel to $U_\times B$'+'\nOrange pair: parallel multiplication lines',fontsize=9,color=ink)
ax=fig.add_subplot(gs[0,1]);ax.set_aspect('equal');ax.axis('off');ax.set_xlim(-.4,2.7);ax.set_ylim(-.25,4.55)
ax.set_title('(b) Fast output E feeds the AD support',loc='left',fontsize=13,pad=15)
p=13;s=.82;X=2.;values=[s];n=1;ops=[]
for bit in bin(p)[3:]:
 point_out=mul(values[-1],values[-1]);v=1-point_out[1]/H;n*=2;values.append(v);ops.append('square')
 if bit=='1':
  point_out=mul(s,values[-1]);v=1-point_out[1]/H;n+=1;values.append(v);ops.append('times s')
assert n==p and abs(values[-1]-s**p)<1e-14
E=R(values[-1]);P=R(s);M=np.array([0,H*(1-1/X)]);F=np.array([W-2*W/(p-1),H-H*(p+1)/(X*(p-1))]);D=F-[0,H*s**p]
k=(D[1]-A[1])/(D[0]-A[0]);m=(E[1]-M[1])/W
T=np.array([W-H*s/(k-m),H-k*H*s/(k-m)]);PP=np.array([W,T[1]])
sp=1-PP[1]/H;expected=s*(p+1+(p-1)*X*s**p)/(p-1+(p+1)*X*s**p)
assert abs(sp-expected)<1e-14 and abs(cross(T-P,E-M))<1e-12
for c,d in [([0,0],[0,H]),([0,H],A),(A,B),(B,[0,0])]:line(ax,c,d)
line(ax,M,E,orange,lw=1.8);line(ax,A,T,blue,lw=2);line(ax,P,T,orange,lw=2);line(ax,T,PP,blue,lw=2)
line(ax,F,D,blue,ls='--');line(ax,A,E,orange,lw=3)
for q,label,off in [(A,'A',(5,6)),(B,'B',(5,-10)),(M,'M',(-16,-4)),(E,r'$E=R(s^{13})$',(8,-4)),(P,'P',(8,-4)),(PP,r"$P^+$",(8,-6)),(T,'T',(-17,-12)),(F,'F',(-18,4)),(D,'D',(-18,-5))]:point(ax,q,label,off)
ax.text(.03,.12,r'$FD=AE$'+'\n'+r'$PT\parallel ME$'+'\n'+r'$TP^+\perp AB$',fontsize=10,color=ink)
ax=fig.add_subplot(gs[1,:]);ax.axis('off');ax.set_xlim(-.5,5.65);ax.set_ylim(-.55,1.1)
exponents=[1,2,3,6,12,13]
for i,(n,v) in enumerate(zip(exponents,values)):
 ax.text(i,.35,rf'$R(s^{{{n}}})$',ha='center',va='center',fontsize=12,bbox=dict(boxstyle='round,pad=.35',fc='white',ec=blue))
 ax.text(i,-.15,f'{v:.5f}',ha='center',fontsize=9,color=ink)
 if i<5:
  ax.annotate('',(i+.73,.35),(i+.28,.35),arrowprops=dict(arrowstyle='->',color=ink))
  ax.text(i+.5,.82,'square' if ops[i]=='square' else r'$\times s$',ha='center',fontsize=9)
ax.text(-.4,1.02,'(c) Binary schedule: 13 = (1101)₂; five multiplications instead of twelve',fontsize=12)
fig.savefig(ROOT/'figures/fast_geometry.pdf');fig.savefig(ROOT/'figures/fast_geometry.png',dpi=170)
(ROOT/'fast_geometry_checks.json').write_text(json.dumps(dict(p=p,X=X,s=s,W=W,H=H,exponents=exponents,values=values,E=E.tolist(),D=D.tolist(),T=T.tolist(),s_next=sp,expected=expected,checks='Geometric intersections, parallelism and AD readout agree to 1e-12 or better.'),indent=2)+'\n')
print('PASS: copied and multiplied incidences; binary exponent 13; final AD intersection',sp)
