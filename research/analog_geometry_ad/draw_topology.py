"""Block-level model topology, showing the common and changed signal paths."""
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch
HERE=Path(__file__).resolve().parent
fig,axs=plt.subplots(2,1,figsize=(11.5,6.9),layout='constrained')
blue='#176B9B';orange='#BD5A20';ink='#253640';gray='#84939D'
def box(ax,x,y,w,h,text,color=blue):
 ax.add_patch(FancyBboxPatch((x,y),w,h,boxstyle='round,pad=.02',facecolor='white',edgecolor=color,lw=1.5))
 ax.text(x+w/2,y+h/2,text,ha='center',va='center',fontsize=11,color=ink)
def arrow(ax,xy1,xy2,color=ink):ax.annotate('',xy=xy2,xytext=xy1,arrowprops={'arrowstyle':'->','color':color,'lw':1.5})
for ax in axs:ax.set(xlim=(0,11.3),ylim=(0,2.85));ax.axis('off')
a=axs[0];a.set_title('Matched direct correction: multiplier, then divider',loc='left',fontsize=13)
a.text(.15,1.67,'w, b',fontsize=12);box(a,1,1.25,2.1,.9,'n = -w b\nloaded pole');box(a,4.1,1.25,2.3,.9,'delta = n / (1 + a w)\nloaded pole');box(a,8,1.25,2.9,.9,'q + delta\ncommon candidate RC')
arrow(a,(.7,1.7),(1,1.7));arrow(a,(3.1,1.7),(4.1,1.7));arrow(a,(6.4,1.7),(8,1.7));a.text(3.95,.86,'1 + a w supplied algebraically',fontsize=10,color=gray)
a.text(.15,.35,'Same per-cell pole, load, gain/offset model, electrical trims and paired internal noise.',fontsize=11,color=ink)
a=axs[1];a.set_title('Geometric feedback correction: summer and multiplier in a loop',loc='left',fontsize=13)
a.text(.15,1.67,'b',fontsize=12);box(a,1,1.25,2.1,.9,'m = b + a delta\nloaded pole',orange);box(a,4.1,1.25,2.3,.9,'delta = -w m\nloaded pole',orange);box(a,8,1.25,2.9,.9,'q + delta\ncommon candidate RC')
arrow(a,(.7,1.7),(1,1.7));arrow(a,(3.1,1.7),(4.1,1.7));arrow(a,(6.4,1.7),(8,1.7));a.text(5.2,2.5,'w',fontsize=12);arrow(a,(5.3,2.42),(5.3,2.16))
a.plot([7,7,2.05],[1.7,.58,.58],color=orange,lw=1.5);arrow(a,(2.05,.58),(2.05,1.25),orange);a.text(3.2,.16,'Feedback is dynamic; saturation and settling are simulated.',fontsize=10,color=orange)
fig.suptitle('Correction cells compared on the SAME V30 binary-power and sample/hold backbone\nBehavioral finite-bandwidth models; not transistor schematics',fontsize=14)
for suffix in ['png','svg']:fig.savefig(HERE/f'comparison_topology.{suffix}',dpi=180,bbox_inches='tight')
svg=HERE/'comparison_topology.svg'
svg.write_text('\n'.join(line.rstrip() for line in svg.read_text().splitlines())+'\n')
