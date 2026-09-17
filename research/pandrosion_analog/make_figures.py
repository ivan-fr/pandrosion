from pathlib import Path
import json
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch,FancyArrowPatch
P=Path(__file__).parent
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,'svg.fonttype':'none','axes.spines.top':False,'axes.spines.right':False})
ink='#243b42';teal='#187e77';purple='#7956a4';orange='#bf6648';gray='#8b989c'
fig,ax=plt.subplots(figsize=(13,6.8));ax.set_xlim(0,13);ax.set_ylim(0,7);ax.axis('off')
def box(x,y,w,h,title,sub,color=teal):
 ax.add_patch(FancyBboxPatch((x,y),w,h,boxstyle='round,pad=.08,rounding_size=.12',edgecolor=color,facecolor='#f8faf9',lw=1.5))
 ax.text(x+w/2,y+h*.68,title,ha='center',va='center',weight='bold',color=color,fontsize=11)
 ax.text(x+w/2,y+h*.26,sub,ha='center',va='center',color=ink,fontsize=9.5)
def arrow(a,b,color=gray,rad=0):ax.add_patch(FancyArrowPatch(a,b,arrowstyle='-|>',mutation_scale=13,lw=1.5,color=color,connectionstyle=f'arc3,rad={rad}'))
box(.25,4.7,1.5,1.1,'Entrée m','1 ≤ m ≤ 2')
box(2.3,4.7,2.2,1.1,'Chaîne de produits','q₂ = s², …, qₚ = sᵖ')
box(5.1,4.7,1.6,1.1,'Résidu t','t = m qₚ')
box(7.3,4.7,2.1,1.1,'Rapport AD','N = 1 + αt\nD = α + t')
box(10.05,4.7,2.35,1.1,'Valeur suivante','s⁺ = s N / D',purple)
arrow((1.83,5.25),(5.02,5.25),rad=-.4);arrow((4.58,5.25),(5.02,5.25));arrow((6.78,5.25),(7.22,5.25));arrow((9.48,5.25),(9.97,5.25))
box(9.65,2.4,2.75,1.15,'Mémoire candidate','Buffer · interrupteur φA\nCondensateur 100 pF',purple)
box(4.75,2.4,2.9,1.15,'Mémoire de l’état s','Buffer · interrupteur φB\nCondensateur 100 pF',purple)
arrow((11.2,4.62),(11.2,3.63),purple);arrow((9.57,2.98),(7.73,2.98),purple)
ax.text(8.65,3.25,'copie isolée',ha='center',color=gray,fontsize=9)
arrow((5.1,3.65),(3.4,4.62),purple)
ax.plot([6.2,6.2,4.85,4.85,11.2],[3.64,4.25,4.25,6.35,6.35],color=purple,lw=1.2);arrow((11.2,6.35),(11.2,5.88),purple)
ax.text(8.8,6.47,'État maintenu pendant le calcul',color=purple,ha='center',fontsize=10)
box(.25,.45,3.5,1.1,'Sortie géométrique','y = m sᵖ⁻¹ · voie de comparaison')
box(4.75,.45,2.9,1.1,'Sortie réciproque','y = 1/s · même limite',purple)
arrow((6.2,2.32),(6.2,1.63),purple)
arrow((3.4,4.62),(2.,1.63),teal,rad=.15)
ax.text(9.9,1.22,'α = (p − 1)/(p + 1)\nφA et φB ne se recouvrent pas.\nInitialisation : s = 1.',ha='center',va='center',color=ink,fontsize=11,linespacing=1.6)
fig.suptitle('Pandrosion AD · prototype analogique échantillonné',fontsize=17,color=ink,weight='bold',y=.985)
fig.text(.5,.015,'Blocs arithmétiques comportementaux ; architecture testée dans SPICE, pas encore un schéma transistor.',ha='center',fontsize=10,color=gray)
fig.subplots_adjust(left=.025,right=.975,bottom=.05,top=.91)
for ext in ['png','svg']:fig.savefig(P/f'architecture.{ext}',dpi=170,facecolor='white')
plt.close(fig)
w=np.loadtxt(P/'spice_waveform.csv',delimiter=',',skiprows=1)
e=json.loads((P/'error_results.json').read_text());sp=json.loads((P/'spice_results.json').read_text())
fig,axs=plt.subplots(1,3,figsize=(14,4.5))
ax=axs[0];sel=w[:,0]<65e-6
ax.plot(w[sel,0]*1e6,w[sel,4],color=purple,label='Sortie 1/s');ax.axhline(2**(1/3),ls='--',lw=1,color=teal,label='∛2');ax.set_ylim(.98,1.28);ax.set_xlabel('Temps simulé (µs)');ax.set_ylabel('Tension de sortie (V)');ax.set_title('SPICE nominal : p = 3, m = 2');ax.legend(fontsize=9);ax.grid(alpha=.2)
ax=axs[1];rows=e['monte_carlo'];ps=[x['p']for x in rows]
ax.plot(ps,[x['inverse']['p95_abs_ppm']/1e4 for x in rows],'o-',color=purple,label='Sortie 1/s');ax.plot(ps,[x['geometry']['p95_abs_ppm']/1e4 for x in rows],'s-',color=teal,label='Sortie m sᵖ⁻¹');ax.set_xticks(ps);ax.set_xlabel('Degré p');ax.set_ylabel('95e percentile |erreur relative| (%)');ax.set_title('Erreurs illustratives : 2 000 tirages / p');ax.legend(fontsize=9);ax.grid(alpha=.2)
ax=axs[2];co=[r for r in sp['mismatch_corners']if r['p']==16];x=np.arange(2);width=.32
ax.bar(x-width/2,[abs(r['final_inverse_error'])*100 for r in co],width,color=purple,label='Sortie 1/s');ax.bar(x+width/2,[abs(r['final_geometry_error'])*100 for r in co],width,color=teal,label='Sortie m sᵖ⁻¹');ax.set_xticks(x,['Gain des produits\n+0,1 % chacun','Offset de mise à jour\n+0,5 mV']);ax.set_ylabel('|Erreur relative| (%)');ax.set_title('SPICE p = 16 : le type d’erreur compte');ax.legend(fontsize=9);ax.grid(axis='y',alpha=.2)
fig.tight_layout(pad=1.8,w_pad=2)
for ext in ['png','svg']:fig.savefig(P/f'prototype_results.{ext}',dpi=170,facecolor='white')
plt.close(fig)
print('Architecture and results figures saved.')
