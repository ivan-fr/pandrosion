"""Schematic of the finite-current storage model, not a transistor implementation."""
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch
P=Path(__file__).resolve().parent
fig,ax=plt.subplots(figsize=(12,4.3),layout='constrained');ax.set(xlim=(0,12),ylim=(0,4));ax.axis('off')
blue='#176B9B';orange='#BD5A20';ink='#253640'
def box(x,y,w,h,text):
 ax.add_patch(FancyBboxPatch((x,y),w,h,boxstyle='round,pad=.04',facecolor='white',edgecolor=blue,lw=1.5))
 ax.text(x+w/2,y+h/2,text,ha='center',va='center',fontsize=10,color=ink)
def arrow(a,b):ax.annotate('',xy=b,xytext=a,arrowprops=dict(arrowstyle='->',color=ink,lw=1.4))
def cap(x,y):
 ax.plot([x,x],[y,y-.55],color=ink);ax.plot([x-.22,x+.22],[y-.55,y-.55],color=ink)
 ax.plot([x-.22,x+.22],[y-.67,y-.67],color=ink);ax.plot([x,x],[y-.67,y-1.05],color=ink)
 ax.plot([x-.2,x+.2],[y-1.05,y-1.05],color=ink);ax.text(x+.25,y-.65,'C + parasitic',fontsize=9,va='center')
def switch(x,label):
 ax.plot([x,x+.18],[2.5,2.5],color=ink);ax.plot([x+.18,x+.67],[2.5,2.76],color=orange,lw=2)
 ax.plot([x+.72,x+.9],[2.5,2.5],color=ink);ax.text(x+.45,3.15,label,ha='center',fontsize=10,color=orange)
ax.text(.05,2.5,'AD\ncandidate',va='center',fontsize=10)
box(1.1,2.03,1.8,.94,'Candidate driver\n±2 mA; 10 Ω\nlocal pole ≈1 µs');arrow((.77,2.5),(1.06,2.5));arrow((2.96,2.5),(3.35,2.5))
switch(3.35,'Sample clock');ax.plot([4.25,5.5],[2.5,2.5],color=ink);cap(4.65,2.5)
box(5.5,2.03,1.8,.94,'Trim + buffer\n±2 mA; 10 Ω\nlocal pole ≈1 µs');arrow((7.36,2.5),(7.75,2.5));switch(7.75,'Transfer clock')
ax.plot([8.65,10.6],[2.5,2.5],color=ink);cap(9.1,2.5);arrow((10.6,2.5),(11.5,2.5));ax.text(10.4,2.85,'State q',fontsize=11,color=blue)
for x in [4.65,9.1]:
 ax.annotate('Q(V) at opening',xy=(x,2.5),xytext=(x,3.6),ha='center',fontsize=9,color=orange,arrowprops=dict(arrowstyle='->',color=orange))
ax.text(6,.25,'Electrical-reference calibration • charge on both edges • kT/C noise • leakage • finite acquisition',ha='center',fontsize=11,color=ink)
ax.set_title('Memory/acquisition redesign: power chain and AD correction stay unchanged',fontsize=14,pad=15)
for ext in ['png','svg']:fig.savefig(P/f'memory_model.{ext}',dpi=180,bbox_inches='tight')
f=P/'memory_model.svg';f.write_text('\n'.join(x.rstrip()for x in f.read_text().splitlines())+'\n')
