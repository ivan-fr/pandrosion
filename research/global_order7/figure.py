"""Render the actual homogeneous incidence steps; no illustrative fake points."""
from pathlib import Path
import json,subprocess
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
ROOT=Path(__file__).resolve().parents[2]
g=json.loads(subprocess.check_output(['node','--input-type=module','-e',"import {order7} from './research/global_order7/prototype.mjs'; console.log(JSON.stringify(order7(3,2*.75**3,.75,2)));"],cwd=ROOT,text=True))
xy={n:(q[0]/q[2],q[1]/q[2]) for n,q in g['points'].items()}
fig,axes=plt.subplots(3,4,figsize=(12,11))
for i,ax in enumerate(axes.flat):
 ax.set(xlim=(-2.5,4.5),ylim=(-5.7,5.2));ax.set_aspect('equal');ax.axis('off')
 for x in [0,1]:ax.axvline(x,color='#ccd4da',lw=1)
 ax.axhline(1,color='#ccd4da',lw=1)
 for j,op in enumerate(g['ops'][:i+1]):
  a,b,c=op['line'];color='#0077ad' if j==i else '#d6dfe3'
  if abs(b)>1e-12:
   xs=[-2.5,4.5];ax.plot(xs,[(-a*x-c)/b for x in xs],color=color,lw=1.7 if j==i else .65)
  else:ax.axvline(-c/a,color=color,lw=1)
 op=g['ops'][i]
 for number,n in enumerate([op['a'],op['b'],op['n']]):
  x,y=xy[n];ax.plot(x,y,'o',ms=3,color='#0b7656' if n==op['n'] else '#243744');ax.annotate(n,(x,y),xytext=((10,-15) if y>4 else (10,12) if y < -4.5 else [(-38,-20),(9,18),(10,-6)][number]),textcoords='offset points',fontsize=7,arrowprops=dict(arrowstyle='-',lw=.4,color='#506472'),bbox=dict(facecolor='white',edgecolor='none',alpha=.85,pad=.3))
 ax.set_title(f"{i+1}. {op['a']} — {op['b']} → {op['n']}",fontsize=9)
fig.suptitle('Global order 7: twelve joins after the power stage\np = 3, X = 2, s = 3/4 · fixed preparation excluded',fontsize=14)
fig.tight_layout(rect=(0,0,1,.94))
folder=Path(__file__).parent
fig.savefig(folder/'construction.svg');fig.savefig(folder/'construction.png',dpi=110)
p=folder/'construction.svg';p.write_text('\n'.join(x.rstrip() for x in p.read_text().splitlines())+'\n')
