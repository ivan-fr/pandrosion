"""Create reviewable scientific figures and result tables from retained measurements."""
from pathlib import Path
import json,math
import numpy as np
import mpmath as mp
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch
P=Path(__file__).resolve().parent;D=P/'results'
r=json.loads((D/'transistor.json').read_text());comp=json.loads((D/'comparison.json').read_text())
get=lambda ident:next(x for x in r if x['id']==ident)
mp.mp.dps=80
fig,ax=plt.subplots(1,2,figsize=(12,4.5),layout='constrained')
ns=[1,2,4,6];errs=[get(f'depth_p3.7_n{n}')['relative_error'] if n!=6 else get('root_p3.7_X2_calFalse')['relative_error'] for n in ns];ideal=[]
for n in ns:
 t=mp.mpf(1)/mp.mpf('3.7');a=mp.floor(t*2**n)/2**n;lam=(t-a)*2**n;A=mp.power(2,a);z=mp.power(2,mp.mpf(1)/2**n)-1
 out=A*(12+6*(2+lam)*z+(lam+1)*(lam+2)*z*z)/(12+6*(2-lam)*z+(lam-1)*(lam-2)*z*z)
 ideal.append(float(abs(out/mp.power(2,t)-1)))
ax[0].semilogy(ns,errs,'o-',label='SPICE : transistors et miroirs');ax[0].semilogy(ns,ideal,'o-',label='Padé mathématique exact');ax[0].axhline(1e-6,color='gray',ls='--',label='1 ppm');ax[0].set(xlabel='Subdivisions',ylabel='Erreur relative',title='X = 2 ; p = 3,7 : ajouter des cellules peut nuire');ax[0].set_xticks(ns);ax[0].legend(fontsize=8)
for rev in [False,True]:
 a=np.loadtxt(D/'raw'/f'step_1e-12_1e-09_{rev}'/'trace.txt',skiprows=1);ax[1].plot(a[:,0]*1e6,a[:,1]/1e-5,label='2 → 1' if rev else '1 → 2')
ax[1].axhline(1,color='gray',ls='--');ax[1].axhline(math.sqrt(2),color='gray',ls=':');ax[1].set(xlabel='Temps (µs)',ylabel='Courant / I₀',title='Moyenne calibrée : oscillations en descente');ax[1].legend(title='Entrée B, A = 1');fig.savefig(P/'measurements.png',dpi=170);fig.savefig(P/'measurements.svg');plt.close(fig)
fig,ax=plt.subplots(figsize=(12,4));ax.set(xlim=(0,12),ylim=(0,4));ax.axis('off')
boxes=[(.1,1.5,2,1,'Commande numérique\nX, p ; exposants, λ\ncoefficients préchargés'),(2.7,1.5,2.1,1,'6 moyennes\nboucle translinéaire\nmiroirs BJT réels'),(5.4,1.5,2.3,1,'3 produits : A², AB, B²\n2 sommes positives\nproduit / quotient final'),(8.3,1.5,3.4,1,'Sortie courant → charge RC\nlecture / maintien → SAR 20 bits\nconvertisseurs comportementaux')]
for x,y,w,h,label in boxes:ax.add_patch(FancyBboxPatch((x,y),w,h,boxstyle='round,pad=.06',facecolor='#e8eff6',edgecolor='#334b62'));ax.text(x+w/2,y+h/2,label,ha='center',va='center',fontsize=9)
for x,y in [(2.15,2.65),(4.85,5.35),(7.75,8.25)]:ax.annotate('',xy=(y,2),xytext=(x,2),arrowprops=dict(arrowstyle='->',lw=1.5))
ax.text(6,3.5,'Prototype simulé : noyau à 226 BJT, lecture de Padé homogène',ha='center',fontsize=15);ax.text(6,.65,'I₀ = 10 µA · rails +4 V / −2,5 V · références et biais externes idéaux\nSchéma de blocs ; connexions électriques exactes dans les netlists. Aucun routage silicium.',ha='center',fontsize=10)
fig.savefig(P/'architecture.png',dpi=170,bbox_inches='tight');fig.savefig(P/'architecture.svg',bbox_inches='tight');plt.close(fig)
lines=['# Mesures comparatives exécutées','', 'Même couple (p, X). V30 et P6 : macromodèles calibrés, pas des circuits transistor. Nouvelle chaîne : modèle BJT générique, n=6, sans correction des moyennes. Les niveaux de fidélité diffèrent ; ce tableau ne classe pas les énergies.', '', '| p | X | V30, 4,785 ms (ppm) | P6, 180 µs / 16 lectures (ppm) | Nouvelle chaîne BJT (ppm) |','|---:|---:|---:|---:|---:|']
for x in comp:
 p=x['p'];xx=x['X'];q=next(t for t in r if t['id'].startswith('root_') and t['id'].endswith('calFalse') and t['p']==p and t['X']==xx)
 lines.append(f'| {p:g} | {xx:g} | {x["V30"]["configured_adc_relative_error"]*1e6:.6g} | {x["P6_policy_errors"]["avg16"]*1e6:.6g} | {q["relative_error"]*1e6:.6g} |')
lines += ['', 'Les huit paires sont un contrôle commun, pas un nouvel échantillonnage représentatif. Les étalonnages électriques et ADC sont recalculés une fois par p à 25 °C, puis partagés entre les deux macromodèles. Les deux échecs P6 à 1 ppm de ce protocole sont conservés. Les performances des campagnes P6 historiques à 64 cas restent des résultats de leurs propres protocoles.','','## Profondeur, X=2 et p=3,7','','| n | Erreur mathématique | Erreur BJT |','|---:|---:|---:|']
for n,e,m in zip(ns,ideal,errs):lines.append(f'| {n} | {e:.7g} | {m:.7g} |')
lines += ['', 'Les balayages n=1 et n=2 à X=500000 sortent de la plage visée des courants intermédiaires ; ils sont des diagnostics de saturation, pas des candidats retenus.','', '## Sources numériques','','- [Campagne transistor](results/transistor.json) : 118 essais, dont quatre délais de solveur au démarrage.','- [Calibration mesurée](results/calibration.json) : références rationnelles ; gains et offsets gelés.','- [V30/P6](results/comparison.json) : sorties, trajectoires et coefficients de calibration.','- [Primitives communes](results/matched.json) : 32 simulations, charge et erreurs identiques par primitive. Le profil « ideal » signifie gain/offset nuls ; les pertes résistives restent présentes.','- [Contrôles P5/P6 à transistors](results/controls.json) : 12 simulations. Modèles et I₀ alignés, terminaisons de sortie historiques conservées.','- [Bruit petit signal](results/noise.json), [interfaces](results/interface.json), [démarrages avec rampes](results/ramped.json), [contrôles](results/checks.json).','']
(P/'MEASUREMENTS.md').write_text('\n'.join(lines))
for p in P.glob('*.svg'):p.write_text('\n'.join(l.rstrip() for l in p.read_text().splitlines())+'\n')
print('Generated figures and MEASUREMENTS.md')
