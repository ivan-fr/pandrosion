"""Electrical schematic of the existing behavioral SPICE topology, not a transistor design."""
from pathlib import Path
import sys,json
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon,Circle
ROOT=Path(__file__).parent
sys.path.insert(0,str(ROOT.parents[1]/'research/analog_fast_ad'))
from spice import deck
from revised_circuit import revision
cfg=revision(25,1,20261001)
text=deck(3,1.2,config=cfg)
for line in ['Ssample candidate stored sample 0 SW','Supdate stored_read state update 0 SW','Sreset state 0 reset 0 SW','Rcandidate candidate_drive candidate 10','Ccandidate candidate 0 100n','Rport_q q 0','Cport_q q 0 2p']:
 assert line in text,line
assert cfg['memory_cap']==100e-9 and cfg['switch_ron']==230
fig,axes=plt.subplots(3,1,figsize=(10.5,9),layout='constrained')
ink='#193944';teal='#137c82';orange='#bc571c'
for ax in axes:ax.set_xlim(0,16);ax.set_ylim(-.1,3.5);ax.axis('off')
def wire(ax,*pts,**kw):ax.plot(*zip(*pts),color=ink,lw=1.3,**kw)
def label(ax,x,y,t,**kw):ax.text(x,y,t,color=ink,fontsize=10,ha=kw.pop('ha','center'),va='center',**kw)
def dot(ax,x,y):ax.plot(x,y,'o',color=ink,ms=3)
def ground(ax,x,y):
 wire(ax,(x,y+.13),(x,y))
 for d,w in [(0,.22),(-.07,.14),(-.14,.06)]:wire(ax,(x-w,y+d),(x+w,y+d))
def cap(ax,x,y,name):
 wire(ax,(x,y),(x,y-.57));wire(ax,(x-.25,y-.57),(x+.25,y-.57));wire(ax,(x-.25,y-.7),(x+.25,y-.7));wire(ax,(x,y-.7),(x,y-1.25));ground(ax,x,y-1.25);label(ax,x+.35,y-.9,name,ha='left')
def resistor(ax,x,y,name,vertical=False):
 if vertical:
  wire(ax,(x,y),(x,y-.3));z=[(x,y-.3)]+[(x+(.12 if i%2 else -.12),y-.35-.1*i) for i in range(6)]+[(x,y-1.)];wire(ax,*z);wire(ax,(x,y-1),(x,y-1.25));ground(ax,x,y-1.25);label(ax,x+.35,y-.7,name,ha='left')
 else:
  z=[(x-.5,y)]+[(x-.4+.16*i,y+(.1 if i%2 else -.1)) for i in range(6)]+[(x+.5,y)];wire(ax,*z);label(ax,x,y+.38,name)
def switch(ax,x,y,name):
 wire(ax,(x-.6,y),(x-.28,y));wire(ax,(x-.25,y),(x+.24,y+.2));wire(ax,(x+.3,y),(x+.6,y));dot(ax,x-.28,y);dot(ax,x+.3,y);label(ax,x,y+.52,name)
def source(ax,x,y,name):
 wire(ax,(x,y),(x,y-.25));ax.add_patch(Polygon([(x,y-.25),(x+.33,y-.62),(x,y-.99),(x-.33,y-.62)],closed=True,fill=False,ec=teal,lw=1.6));label(ax,x,y-.48,'+');label(ax,x,y-.8,'−');wire(ax,(x,y-.99),(x,y-1.25));ground(ax,x,y-1.25);label(ax,x-.45,y-.63,name,ha='right')
ax=axes[0];ax.set_title('(a) Candidate and next-state sample / transfer',loc='left',fontsize=13)
y=2.35;source(ax,1.1,y,'Bcandidate');wire(ax,(1.1,y),(2,y));resistor(ax,2.5,y,'10 Ω');wire(ax,(3,y),(5,y));dot(ax,4,y);cap(ax,4,y,'100 nF');label(ax,4,y+.35,'candidate')
switch(ax,5.6,y,'Ssample');wire(ax,(6.2,y),(8.8,y));dot(ax,7,y);cap(ax,7,y,'Cnext\n100 nF');resistor(ax,9,y,'Rnext\n1 TΩ',True);wire(ax,(8.8,y),(9,y));label(ax,7.8,y+.35,'stored')
source(ax,12,y,'Bstored');wire(ax,(12,y),(13,y));switch(ax,13.6,y,'Supdate');wire(ax,(14.2,y),(15.5,y));label(ax,15.2,y+.35,'state');dot(ax,15.2,y)
ax.annotate('',xy=(11.7,2.25),xytext=(9,2.35),arrowprops=dict(arrowstyle='->',color=orange,ls='--',connectionstyle='arc3,rad=-.5'))
label(ax,12,.15,r'$V_{stored\_read}=(V_{stored}-a_m)/b_m$')
ax=axes[1];ax.set_title('(b) State storage, reset and modeled disturbances',loc='left',fontsize=13)
y=2.4;wire(ax,(.7,y),(14.8,y));label(ax,.7,y+.35,'state');cap(ax,1.7,y,'Cstate\n100 nF');resistor(ax,4.3,y,'Rleak\n1 TΩ',True)
for x,txt in [(7.3,'Ileak − Icomp'),(10.5,'Icharge + Ithermal')]:
 wire(ax,(x,y),(x,y-.32));ax.add_patch(Circle((x,y-.66),.32,fill=False,ec=ink,lw=1.3));ax.annotate('',(x,y-.88 if x<9 else y-.43),(x,y-.43 if x<9 else y-.88),arrowprops=dict(arrowstyle='->',color=ink));wire(ax,(x,y-.98),(x,y-1.3));ground(ax,x,y-1.3);label(ax,x,y+.4,txt);dot(ax,x,y)
wire(ax,(14.8,y),(14.8,1.95));dot(ax,14.8,1.9);dot(ax,14.8,1.2);wire(ax,(14.8,1.9),(15.04,1.26));wire(ax,(14.8,1.2),(14.8,.95));ground(ax,14.8,.95);label(ax,13.65,1.6,'Sreset')
label(ax,7.8,.15,'Leakage compensation subtracts from Ileak; charge and thermal pulses enter the state.')
ax=axes[2];ax.set_title('(c) Loaded first-order cell: read buffer q and each binary stage',loc='left',fontsize=13)
y=2.35;source(ax,1.5,y,'Bj');wire(ax,(1.5,y),(3,y));resistor(ax,3.5,y,'10 Ω');wire(ax,(4,y),(11.2,y));label(ax,6,y+.35,r'$v_j$');cap(ax,5.2,y,'Cstage');resistor(ax,8.1,y,'Rport',True);cap(ax,11.2,y,'2 pF')
label(ax,2,.2,r'$V_{j,drive}=\mathrm{clip}_{[-2,2]}(f_j)$',ha='left')
label(ax,14,1.5,'Read cell: sense state\nPower cell: sense previous vj\nand buffered q',ha='center')
label(ax,9,.15,'Cstage and Rport follow the selected error profile; Bj includes fitted trims.')
fig.savefig(ROOT/'figures/analog_circuit.pdf');fig.savefig(ROOT/'figures/analog_circuit.png',dpi=180)
(ROOT/'circuit_checks.json').write_text(json.dumps(dict(source='research/analog_fast_ad/spice.py',memory_cap_F=cfg['memory_cap'],switch_ron_ohm=cfg['switch_ron'],checked='Sample/update/reset node pairs, candidate RC, q port loading, memory values'),indent=2)+'\n')
print('PASS: schematic topology and precision memory/switch values checked against generated deck')
