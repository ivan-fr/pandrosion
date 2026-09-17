from pathlib import Path
import json,csv
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle,Polygon
P=Path(__file__).parent
r=json.loads((P/'results.json').read_text());cal=json.loads((P/'calibration.json').read_text())
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,'svg.fonttype':'none','axes.spines.top':False,'axes.spines.right':False})
colors={'AD':'#7856a3','Halley':'#197f76'};gray='#8c979b';ink='#263b42';red='#ba624c'
fig,axs=plt.subplots(1,3,figsize=(14,4.5))
for mode in ['AD','Halley']:
 a=[x for x in r['nominal_grid']if x['mode']==mode and x['profile']=='trimmed_stress']
 axs[0].plot([x['m']for x in a],[100*x['final_error']for x in a],'o-',label=mode,color=colors[mode])
axs[0].axhline(.1,color=gray,ls='--',label='Objectif exploratoire 0,1 %');axs[0].set_ylim(0,.11);axs[0].set_xlabel('Entrée normalisée m');axs[0].set_ylabel('Erreur relative finale (%)');axs[0].set_title('Modèles avec erreurs résiduelles fixées');axs[0].legend(fontsize=8);axs[0].grid(alpha=.2)
rows=[x for x in r['memory_corners']if x['mode']=='AD'and x['sign']==1]
a=np.zeros((3,3))
for i,c in enumerate([100,1000,10000]):
 for j,t in enumerate([1,5,20]):a[i,j]=next(abs(x['final_error'])*100 for x in rows if np.isclose(x['hold_pf'],c)and x['acquisition_us']==t)
im=axs[1].imshow(a,cmap='YlOrRd',aspect='auto',vmin=0,vmax=1.2)
for i in range(3):
 for j in range(3):axs[1].text(j,i,f'{a[i,j]:.3f} %',ha='center',va='center',color='white'if a[i,j]>.8 else ink)
axs[1].set_xticks([0,1,2],['1','5','20']);axs[1].set_yticks([0,1,2],['100 pF','1 nF','10 nF']);axs[1].set_xlabel('Fenêtre d’acquisition (µs)');axs[1].set_title('AD à m = 1,6 : mémoire et injection')
for mode in ['AD','Halley']:
 row=next(x for x in cal['results']if x['mode']==mode and x['profile']=='untrimmed_stress')
 axs[2].semilogy([x['m']for x in row['held_out']],[abs(x['raw_error'])*100 for x in row['held_out']],'--o',color=colors[mode],alpha=.5,label=mode+' brut')
 axs[2].semilogy([x['m']for x in row['held_out']],[abs(x['corrected_error'])*100 for x in row['held_out']],'-s',color=colors[mode],label=mode+' corrigé')
axs[2].set_xlabel('Entrées distinctes des deux points de réglage');axs[2].set_ylabel('|Erreur relative| (%)');axs[2].set_title('Étalonnage hors ligne : modèle fixe');axs[2].legend(fontsize=8);axs[2].grid(alpha=.2)
fig.tight_layout(pad=1.7,w_pad=2.4)
for ext in ['png','svg']:fig.savefig(P/f'p1_results.{ext}',dpi=170,facecolor='white')
plt.close(fig)
fig,ax=plt.subplots(figsize=(12,6.7));ax.set_xlim(0,12);ax.set_ylim(0,7);ax.axis('off')
def wire(a,b):ax.plot([a[0],b[0]],[a[1],b[1]],color=ink,lw=1.3)
def resistor(a,b,label):
 x1,y1=a;x2,y2=b;mx=(x1+x2)/2;my=(y1+y2)/2
 if y1==y2:
  wire(a,(mx-.3,my));wire((mx+.3,my),b);ax.add_patch(Rectangle((mx-.3,my-.12),.6,.24,fill=False,edgecolor=ink));ax.text(mx,my+.22,label,ha='center',fontsize=10)
 else:
  wire((mx,min(y1,y2)),(mx,my-.3));wire((mx,my+.3),(mx,max(y1,y2)));ax.add_patch(Rectangle((mx-.12,my-.3),.24,.6,fill=False,edgecolor=ink));ax.text(mx+.2,my,label,va='center',fontsize=10)
def ground(x,y):
 for k,w in enumerate([.18,.12,.06]):wire((x-w,y-.07*k),(x+w,y-.07*k))
for x,title,rref,rt,formula in [(0,'Numérateur N', '10 kΩ','20 kΩ','N = Vref/2 + Vt/4'),(6,'Dénominateur D','20 kΩ','10 kΩ','D = Vref/4 + Vt/2')]:
 ax.text(x+2.7,6.5,title,color=colors['AD'],ha='center',weight='bold',fontsize=13)
 ax.text(x+.15,4.9,'Vref',ha='left');resistor((x+.65,4.5),(x+2.55,4.5),rref)
 ax.text(x+2.55,6.05,'Vt',ha='center');resistor((x+2.55,5.85),(x+2.55,4.5),rt)
 resistor((x+2.55,4.5),(x+2.55,3.2),'20 kΩ');ground(x+2.55,3.2)
 ax.plot(x+2.55,4.5,'o',ms=4,color=ink);wire((x+2.55,4.5),(x+3.35,4.5))
 ax.add_patch(Polygon([(x+3.35,4.0),(x+3.35,5.0),(x+4.15,4.5)],closed=True,fill=False,edgecolor=colors['AD'],lw=1.5));ax.text(x+3.58,4.5,'1',ha='center',va='center',color=colors['AD']);wire((x+4.15,4.5),(x+5.35,4.5));ax.text(x+4.7,4.73,'buffer',ha='center',fontsize=9)
 ax.text(x+2.8,2.7,formula,ha='center',color=ink,fontsize=12)
ax.text(6,1.8,'t = m s³  ·  Vt = 4t  ·  Vref = 4 V  ·  Vs⁺ = Vs N / D',ha='center',fontsize=13,color=ink)
ax.text(6,1.15,'Ces deux réseaux réalisent les sommes du pas AD cubique. Les mémoires sont isolées par des buffers.',ha='center',fontsize=10,color=ink)
ax.text(6,.62,'Acquisition nominale : 20 µs  ·  maintien : 10 nF  ·  injection testée : 2 pC',ha='center',fontsize=11,color=colors['AD'])
ax.text(6,.08,'Valeurs nominales ; amplificateurs et multiplicateurs décrits par des macromodèles propres, pas par un PDK.',ha='center',fontsize=9,color=gray)
fig.suptitle('P1 · réseaux résistifs du report AD',weight='bold',fontsize=17,color=ink,y=.98);fig.subplots_adjust(top=.89,bottom=.06,left=.025,right=.975)
for ext in ['png','svg']:fig.savefig(P/f'p1_schematic.{ext}',dpi=170,facecolor='white')
plt.close(fig)
# Machine-readable comparisons, one row per frozen model/input.
with (P/'comparison.csv').open('w')as f:
 keys=['mode','m','profile','final_error','final_geometry_error','time_to_0p1pct_us','peak_port_ratio_after_reset'];w=csv.DictWriter(f,fieldnames=keys);w.writeheader()
 for x in r['nominal_grid']:w.writerow({k:x[k]for k in keys})
print('Figures and comparison.csv generated.')
