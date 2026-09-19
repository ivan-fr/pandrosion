"""Actual five-join product incidences and an illustrative residual-order test."""
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import mpmath as mp
from model import Diagram,base
mp.mp.dps=80
HERE=Path(__file__).resolve().parent
OUT=HERE.parents[1]/'paper/reciprocal_geometry_v21/figures'
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':9,'pdf.fonttype':42})
ink='#253640';blue='#176B9B';orange='#BD5A18';green='#218369'
fig,(ax,bx)=plt.subplots(1,2,figsize=(10.2,4.65),gridspec_kw={'width_ratios':[1.6,1]})
d=Diagram(3,2,mp.mpf('.75'))
a=mp.mpf('1.4');b=mp.mpf('.6');P=d.R(a);Q=d.R(b)
V=base.cross(base.join(d.C,Q),d.top)
L=d.left_project(mp.mpf('.5'),P)
Z=base.cross(base.join(V,L),d.right)
L2=d.left_project(mp.mpf('.5'),Z)
R=d.right_project(mp.mpf('.25'),L2)
assert abs(d.value(R)-a*b)<mp.mpf('1e-70')
def seg(a,b,color,lw=1.4,style='-'):
 ax.plot([float(a[0]),float(b[0])],[float(a[1]),float(b[1])],color=color,lw=lw,ls=style)
for x in [0,2]:ax.plot([x,x],[-1.85,4.25],color='#BDC7CC',lw=.8)
ax.plot([-2.35,5.25],[4,4],color='#BDC7CC',lw=.8)
ax.plot([0,2],[0,0],color='#BDC7CC',lw=.8)
for A,B,c in [(d.C,V,orange),(d.hub(mp.mpf('.5')),P,blue),(V,L,blue),
              (d.hub(mp.mpf('.5')),Z,blue),(d.hub(mp.mpf('.25')),R,green)]:seg(A,B,c)
points=[(d.C,'C',(-12,-10)),(P,'R(a)',(7,0)),(Q,'R(b)',(7,0)),(V,'V',(0,8)),
        (L,'L(a/2)',(-44,-9)),(Z,'R(ab/2)',(7,0)),(L2,'L(ab/4)',(7,4)),
        (R,'R(ab)',(7,0)),(d.hub(mp.mpf('.5')),r'$U_{1/2}$',(-12,9)),
        (d.hub(mp.mpf('.25')),r'$U_{1/4}$',(-12,9))]
for P,label,off in points:
 ax.plot(float(P[0]),float(P[1]),'o',ms=3.6,color=green if label=='R(ab)' else ink)
 ax.annotate(label,(float(P[0]),float(P[1])),xytext=off,textcoords='offset points',color=ink)
ax.set(xlim=(-2.6,5.7),ylim=(-2.05,4.8),aspect='equal')
ax.set_title('Ruler-only product: five joins',loc='left',fontweight='bold',color=ink,pad=18)
ax.axis('off')
ax.text(.02,-.04,'Example: a = 1.4, b = 0.6, ab = 0.84\nIf b = 1, reuse R(a): zero joins.',transform=ax.transAxes,color=ink,fontsize=9)
# All values use one oriented rail; horizontal ticks are annotation, not extra joins.
t=mp.mpf(2);u=mp.mpf('1.1')
square=d.mul(d.R(u),d.R(u));product=d.mul(d.R(t),square)
assert abs(d.value(square)-u*u)<mp.mpf('1e-70')
assert abs(d.value(product)-t*u*u)<mp.mpf('1e-70')
assert square[1]>=d.R(t)[1] and product[1]<=d.B[1]
bx.set_title('Gate on one oriented rail',loc='left',fontweight='bold',color=ink,pad=18)
bx.plot([0,0],[.75,2.65],color=ink,lw=1)
for val,label in [(1,'1'),(float(u*u),r'$u^2=1.21$'),(2,r'$t=2$'),(float(t*u*u),r'$tu^2=2.42$')]:
 bx.plot([-.055,.055],[val,val],color=green,lw=2)
 bx.plot(0,val,'o',ms=4,color=green)
 bx.text(.12,val,label,va='center',color=ink)
bx.annotate('',xy=(-.21,2.6),xytext=(-.21,.8),arrowprops={'arrowstyle':'->','color':ink})
bx.text(-.32,1.7,'Increasing rail value',rotation=90,ha='center',va='center',fontsize=8,color=ink)
bx.set(xlim=(-.5,1.3),ylim=(2.8,.62));bx.axis('off')
bx.text(0,-.04,r'$1\leq t,\quad u^2\leq t,\quad 1\leq tu^2$'+'\nThree comparisons: accept this trial.',transform=bx.transAxes,color=green,fontsize=10)
fig.subplots_adjust(left=.025,right=.97,top=.86,bottom=.15,wspace=.18)
OUT.mkdir(exist_ok=True)
for suffix in ['pdf','png']:
 fig.savefig(OUT/f'circle_safeguard.{suffix}',dpi=190,bbox_inches='tight')
print('PASS: five-join product and controller figure incidences')
