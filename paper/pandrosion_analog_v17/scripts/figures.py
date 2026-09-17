from pathlib import Path
import json
import numpy as np
import mpmath as mp
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch,Polygon,Arc
P=Path(__file__).resolve().parents[1];F=P/'figures';F.mkdir(exist_ok=True)
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,'axes.spines.top':False,'axes.spines.right':False,'pdf.fonttype':42})
TEAL='#137c82';ORANGE='#c15d40';BLUE='#3865a0';GRAY='#7d8e92';INK='#193944'
def save(fig,name):
 fig.savefig(F/(name+'.pdf'),bbox_inches='tight');fig.savefig(F/(name+'.png'),dpi=160,bbox_inches='tight');plt.close(fig)
def seg(ax,a,b,c=GRAY,**kw):ax.plot([a[0],b[0]],[a[1],b[1]],color=c,lw=1.5,**kw)
def point(ax,q,label,offset=(5,5),color=INK):
 ax.scatter(*q,s=20,color=color,zorder=5);ax.annotate(label,q,xytext=offset,textcoords='offset points',fontsize=10,color=color)
W,H,X,p,s=2.,4.,2.,3,.75
C=(0,0);B=(W,0);O=(0,H);A=(W,H);M=(0,2);E=(W,H*(1-s**p));D=(0,-H*s**p);P0=(W,H*(1-s));K=(2/3,0)
fig,axes=plt.subplots(1,2,figsize=(10,6.2))
for ax in axes:
 for a,b in [(C,B),(B,A),(A,O),(O,C),(O,B)]:seg(ax,a,b)
 ax.set_aspect('equal');ax.axis('off');ax.set_xlim(-.7,3.2)
for j in range(1,4):
 L=(0,H*(1-s**j));Q=(W*s**j,L[1]);prev=B if j==1 else (W*s**(j-1),H*(1-s**(j-1)))
 seg(axes[0],L,Q,BLUE);seg(axes[0],L,prev,ORANGE)
 point(axes[0],Q,'$B_'+str(j)+'$',(5,-12 if j==2 else 4),BLUE)
point(axes[0],P0,'$P$',(7,-8));point(axes[0],E,'$E$',(7,4));seg(axes[0],M,E,TEAL)
seg(axes[0],(W*s**3,E[1]),E,BLUE,ls=':')
for q,label,off in [(O,'$O$',(-15,6)),(A,'$A$',(6,6)),(C,'$C$',(-15,-8)),(B,'$B$',(6,-8)),(M,'$M$',(-20,0))]:point(axes[0],q,label,off)
axes[0].set_ylim(-.4,4.6);axes[0].set_title('(a) Nested proportional triangles',fontsize=12,pad=15)
ax=axes[1]
k=H/(2*W*X)*(p+1+(p-1)*X*s**p);m=H/(W*X)*(1-X*s**p)
T=(W-H*s/(k-m),H-k*H*s/(k-m));Pn=(W,T[1])
seg(ax,A,D,TEAL);seg(ax,M,E,ORANGE);seg(ax,P0,T,ORANGE);seg(ax,T,Pn,BLUE)
seg(ax,C,D,GRAY,ls='--')
ax.add_patch(Arc(C,2*H*s**p,2*H*s**p,theta1=255,theta2=315,color=TEAL,lw=1.1,ls=':'))
for q,label,off in [(A,'$A$',(5,5)),(O,'$O$',(-17,5)),(C,'$F=C$',(-40,0)),(B,'$B$',(5,-12)),(D,'$D$',(-15,-16)),(M,'$M$',(-20,0)),(E,'$E$',(7,0)),(P0,'$P$',(8,6)),(T,'$T$',(-18,-15)),(Pn,'$P^+$',(8,-13))]:point(ax,q,label,off)
ax.annotate('',xy=(-.25,D[1]),xytext=(-.25,0),arrowprops=dict(arrowstyle='<->',color=TEAL));ax.text(-.32,D[1]/2,'$AE$',ha='right',va='center',color=TEAL)
ax.annotate('',xy=(2.5,E[1]),xytext=(2.5,H),arrowprops=dict(arrowstyle='<->',color=TEAL));ax.text(2.58,(E[1]+H)/2,'$AE$',va='center',color=TEAL)
ax.set_ylim(-2.15,4.6);ax.set_title('(b) One moving-line AD update',fontsize=12,pad=15)
fig.tight_layout(w_pad=3);save(fig,'geometry')
# General fixed anchor sketch: exact scale, p=4, X=2, W=2,H=4,s=.8.
p=4;s=.8;E=np.array([2,4*(1-s**p)]);anchor=np.array([2-4/(p-1),4-4*(p+1)/(2*(p-1))]);D=anchor-np.array([0,4*s**p])
fig,ax=plt.subplots(figsize=(6,4.3));ax.axis('off');ax.set_aspect('equal')
for a,b in [(C,B),(B,A),(A,O),(O,C)]:seg(ax,a,b)
seg(ax,A,D,TEAL);seg(ax,anchor,D,BLUE);seg(ax,A,E,BLUE)
for q,l,off in [(A,'$A$',(6,6)),(E,'$E$',(6,0)),(anchor,'$F$',(-20,4)),(D,'$D$',(-20,-8)),(C,'$C$',(-15,-10))]:point(ax,q,l,off)
ax.text(2.2,3.2,'$AE=Hs^p$',color=BLUE);ax.text(-.3,-.45,'$FD=AE$',color=BLUE)
ax.set_xlim(-.45,4);ax.set_ylim(-1.4,4.4);save(fig,'anchor')
# Convergence and geometric workload, same visible initial value.
fig,ax=plt.subplots(1,2,figsize=(10,3.9),layout='constrained');mp.mp.dps=350
for method,c in [('Raw',GRAY),('AK',BLUE),('AD',TEAL)]:
 s=mp.mpf(3)/4;r=mp.root(2,3);ns=[];err=[]
 for n in range(7):
  e=abs(2*s*s/r-1)
  if e==0 or e<mp.mpf('1e-150'):break
  ns.append(n);err.append(float(e))
  if method=='Raw':s=1-1/(2*(1+s+s*s))
  elif method=='AK':s=3*s/(2+2*s**3)
  else:s=s*(4+4*s**3)/(2+8*s**3)
 ax[0].semilogy(ns,err,'o-',label=method,color=c)
ax[0].set(xlabel='Updates',ylabel='Relative visible-root error',title='Same visible start: $v_0=9/8$');ax[0].legend()
g=json.loads((P/'scripts/geometric_cost_results.json').read_text())['cubic_reference']['rows']
for name,c in [('raw',GRAY),('AK',BLUE),('AD',TEAL),('compact_halley',ORANGE)]:
 ax[1].plot([v['relative_digits']for v in g],[v[name]['elementary_traces']for v in g],'o-',label=name.replace('_',' '),color=c)
ax[1].set(xlabel='Requested relative decimal digits',ylabel='Counted elementary traces',yscale='log',title='Explicit construction protocols');ax[1].legend(fontsize=8)
for a in ax:a.grid(alpha=.15)
save(fig,'convergence_cost')
# Digital benchmark, timing spread.
b=json.loads((P/'data/benchmark.json').read_text());fig,ax=plt.subplots(figsize=(7,3.5),layout='constrained')
for method,c in zip(['Newton','Halley','AD inverse','mpmath.root'],[BLUE,ORANGE,TEAL,GRAY]):
 v=[x for x in b['rows']if x['method']==method];a=np.array([x['median_us']for x in v]);lo=np.array([x['q1_us']for x in v]);hi=np.array([x['q3_us']for x in v])
 ax.errorbar([x['p']for x in v],a,yerr=[a-lo,hi-a],fmt='o-',capsize=3,color=c,label=method)
ax.set(xlabel='Root degree $p$',ylabel='Median wall time per solve (µs)',title='Python / mpmath • 140 digits working precision');ax.legend(ncol=2,fontsize=9);ax.grid(alpha=.15);save(fig,'timing')
# Analog results, traced from retained source data only.
r=json.loads((P/'analog_p4/results.json').read_text());fig,ax=plt.subplots(1,2,figsize=(10,3.8),layout='constrained')
for name,c in [('loaded',ORANGE),('buffered',TEAL)]:
 a=np.loadtxt(P/f'analog_p4/ad_{name}.csv',delimiter=',',skiprows=1);t=np.linspace(626e-6,649e-6,200);v=np.interp(t,a[:,0],a[:,1]);ax[0].plot((t-t[0])*1e6,(v/v[0]-1)*100,color=c,label=name)
ax[0].set(xlabel='Hold interval (µs)',ylabel='State-voltage change (%)',title='AD memory loading, $m=2$');ax[0].legend()
for z,c in zip(r['results'],[TEAL,ORANGE]):
 v=[x for x in z['buffered']if x['m']not in[1,2]];ax[1].plot([x['m']for x in v],[x['error']*1e6 for x in v],'o-',color=c,label=z['mode'])
ax[1].set(xlabel='Normalized input $m$',ylabel='Relative output error (ppm)',title='Buffered, fixed calibration');ax[1].legend()
for a in ax:a.grid(alpha=.15)
save(fig,'analog_results')
# Functional architecture with explicit sampling and feedback.
fig,ax=plt.subplots(figsize=(10,4));ax.set_xlim(0,10);ax.set_ylim(0,4);ax.axis('off')
def box(x,y,w,h,t):
 ax.add_patch(FancyBboxPatch((x,y),w,h,boxstyle='round,pad=.04',facecolor='#eef5f3',edgecolor=TEAL,lw=1.3));ax.text(x+w/2,y+h/2,t,ha='center',va='center',fontsize=9)
def arrow(a,b):ax.annotate('',xy=b,xytext=a,arrowprops=dict(arrowstyle='->',color=INK,lw=1.3))
box(.2,2,1.6,.8,'State hold\n10 nF');box(2.25,2,1.4,.8,'Read\nfollower');box(4.1,2,1.9,.8,'$t=ms^3$\n$N,D$ networks');box(6.5,2,1.3,.8,'$V_sN/D$');box(8.25,2,1.5,.8,'Candidate\n10 nF')
for a,b in [((1.85,2.4),(2.2,2.4)),((3.7,2.4),(4.05,2.4)),((6.05,2.4),(6.45,2.4)),((7.85,2.4),(8.2,2.4))]:arrow(a,b)
ax.plot([9,9,1,1],[1.95,.55,.55,1.9],color=INK,lw=1.3);ax.annotate('',xy=(1,1.96),xytext=(1,1.1),arrowprops=dict(arrowstyle='->',color=INK));ax.text(5,.2,'Memory transfer, clock B • candidate acquired on clock A',ha='center',fontsize=9)
box(2.1,3.1,1.8,.55,'Inverse readout');box(4.5,3.1,2.4,.55,'Two-op-amp calibration')
arrow((2.95,2.85),(2.95,3.05));arrow((3.95,3.37),(4.45,3.37));arrow((6.95,3.37),(8.1,3.37));ax.text(8.2,3.37,'$V_{out}$',va='center')
save(fig,'architecture')
# Servo diagram kept schematic, internal transistor assumption explicit.
fig,ax=plt.subplots(figsize=(9,3.6));ax.axis('off');ax.set_xlim(0,9);ax.set_ylim(0,3.6)
ax.add_patch(Polygon([[1.7,1.4],[1.7,2.9],[3,2.15]],fill=False,edgecolor=TEAL,lw=1.5));ax.text(1.8,2.53,'+');ax.text(1.8,1.65,'−');ax.text(2.2,2.15,'A',fontsize=10)
arrow((.1,2.65),(1.65,2.65));ax.text(.1,2.9,'$U_{cmd}$');arrow((3,2.15),(4,2.15));ax.text(3.3,2.4,'$U_0$')
box(4,1.8,1.7,.7,'NPN $Q_u$\n(assumed model)');ax.plot([5.75,7],[2.15,2.15],color=INK);box(7,1.8,1.7,.7,'$R_u=28$ kΩ\nto $U_2=0$')
ax.plot([6.2,6.2,1.2,1.2,1.7],[2.15,.8,.8,1.65,1.65],color=INK);ax.text(6.2,2.4,'$U_1$',ha='center')
ax.plot([3.5,3.5,4],[2.15,3.15,3.15],color=INK);box(4,2.93,1.7,.45,'2 MΩ');ax.plot([5.75,6.2,6.2],[3.15,3.15,2.15],color=INK)
ax.text(4.5,.2,'Feedback controls $U_1-U_2$; DD is tied to the positive supply.',ha='center',fontsize=10);save(fig,'servo')
print('Seven vector figure sets generated')
