from pathlib import Path
import json,csv
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch,Polygon
P=Path(__file__).parent
r=json.loads((P/'results.json').read_text())
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':11,'axes.spines.top':False,'axes.spines.right':False})
colors=['#117c83','#c35e3d']
f,ax=plt.subplots(1,2,figsize=(12,4.8),layout='constrained')
for z,c in zip(r['results'],colors):
 vals=[x for x in z['nominal'] if x['m'] not in [1,2]]
 ax[0].plot([x['m'] for x in vals],[x['corrected_error']*1e6 for x in vals],'o-',color=c,label=z['mode'])
 cases=['ref_minus','ref_plus','ratio_minus','ratio_plus','amp_shift']
 means=[max(abs(x['corrected_error'])*1e6 for x in z['frozen_calibration_corners'] if x['case']==k) for k in cases]
 offset=-.17 if z['mode']=='AD' else .17
 ax[1].bar(np.arange(5)+offset,means,.32,color=c,label=z['mode'])
ax[0].set(xlabel='Entrée normalisée m',ylabel='Erreur relative (ppm)',title='Après étalonnage à m = 1 et 2')
ax[0].axhline(0,color='#777',lw=.8);ax[0].legend();ax[0].grid(alpha=.15)
ax[1].set_xticks(range(5),['Réf.\n−200 ppm','Réf.\n+200 ppm','Ratio\n−100 ppm','Ratio\n+100 ppm','Offset AOP\n+25 µV'])
ax[1].set(ylabel='Erreur absolue maximale (ppm)',title='Réglages gelés • deux entrées testées')
ax[1].legend();f.suptitle('P2 • Modèles fonctionnels SPICE, sans bruit ni modèle fabricant',fontsize=14)
f.savefig(P/'p2_results.png',dpi=170);f.savefig(P/'p2_results.svg');plt.close(f)
# Wiring diagram of the electrically simulated calibration stage.
f,ax=plt.subplots(figsize=(13,6));ax.set_xlim(0,13);ax.set_ylim(0,6);ax.axis('off')
def line(points,**kw):ax.plot(*zip(*points),color='#233b42',lw=1.7,**kw)
def resistor(x1,x2,y,label):
 line([(x1,y),(x1+.2,y)]);line([(x2-.2,y),(x2,y)])
 ax.add_patch(plt.Rectangle((x1+.2,y-.11),x2-x1-.4,.22,fill=False,lw=1.5,color='#117c83'))
 ax.text((x1+x2)/2,y+.22,label,ha='center',fontsize=10)
def op(x,y,name):
 ax.add_patch(Polygon([[x,y-.6],[x,y+.6],[x+1.2,y]],fill=False,lw=1.6,color='#117c83'))
 ax.text(x+.1,y+.23,'−');ax.text(x+.1,y-.36,'+');ax.text(x+.45,y,name,fontsize=10)
ax.text(.3,5.5,'P2 — Étage d’étalonnage analogique simulé',fontsize=19,weight='bold',color='#173b43')
ax.text(.3,5.07,'Deux inverseurs à contre-réaction • alimentation prévue ±15 V • source de réglage externe',fontsize=11)
op(3.5,2.9,'A1');op(8.7,2.9,'A2')
line([(.4,3.2),(1,3.2)]);resistor(1,2.7,3.2,'10 kΩ');line([(2.7,3.2),(3.5,3.2)])
ax.text(.3,3.5,'Vbrut',color='#117c83')
line([(2.9,3.2),(2.9,4.2),(3.2,4.2)]);resistor(3.2,5.3,4.2,'Rf = 10 kΩ × a');line([(5.3,4.2),(5.6,4.2),(5.6,2.9),(4.7,2.9)])
line([(.4,1.8),(1,1.8)]);resistor(1,2.7,1.8,'1 MΩ');line([(2.7,1.8),(2.9,1.8),(2.9,3.2)])
ax.text(.3,1.35,'Vtrim (réglable)',fontsize=10)
line([(3.5,2.6),(3.2,2.6),(3.2,2.15)]);ax.text(3.2,1.95,'0 V',ha='center',fontsize=9)
line([(5.6,2.9),(5.9,2.9),(5.9,3.2)]);resistor(5.9,8,3.2,'10 kΩ');line([(8,3.2),(8.7,3.2)])
line([(8.2,3.2),(8.2,4.2)]);resistor(8.2,10.6,4.2,'10 kΩ');line([(10.6,4.2),(10.9,4.2),(10.9,2.9),(9.9,2.9),(12,2.9)])
ax.text(11.1,3.2,'Vcorrigé',color='#117c83')
line([(8.7,2.6),(8.4,2.6),(8.4,2.15)]);ax.text(8.4,1.95,'0 V',ha='center',fontsize=9)
ax.text(6.5,.9,'Relation idéale : Vcorrigé = a · Vbrut + 0,01 a · Vtrim',ha='center',fontsize=15)
ax.text(6.5,.35,'SPICE ajoute gain fini, bande passante, offset, courant de polarisation et limitation de courant.',ha='center',fontsize=11)
f.savefig(P/'p2_calibration.png',dpi=170,bbox_inches='tight');f.savefig(P/'p2_calibration.svg',bbox_inches='tight');plt.close(f)
lines=[]
for z in r['results']:
 nom=z['nominal'];held=[x for x in nom if x['m'] not in [1,2]];corn=z['frozen_calibration_corners']
 lines.append(f"| {z['mode']} | {100*max(abs(x['raw_error']) for x in nom):.6f} % | {100*max(abs(x['corrected_error']) for x in held):.6f} % | {100*max(abs(x['corrected_error']) for x in corn):.6f} % |")
settings='\n'.join(f"- {z['mode']} : Rf = {z['feedback_ohms']:.6f} Ω ; Vtrim = {z['trim_volts']:.9f} V." for z in r['results'])
report=f'''# Pandrosion analogique P2 — étalonnage électrique et référence réelle

17 septembre 2026. Suite de P1, conservé séparément. **40 simulations SPICE de la chaîne et 2 vérifications indépendantes de l'étage de correction.** Le résultat est une étude de faisabilité pour un prototype de laboratoire ; ce n'est pas une puce conçue au niveau transistor.

## Ce qui change

La correction affine auparavant appliquée en Python est maintenant effectuée par deux amplificateurs en contre-réaction avec résistances dans le circuit SPICE. Python ajuste les deux commandes aux entrées m=1 et m=2, puis les gèle ; aucune correction logicielle des sorties de validation n'est appliquée. La référence passe de 4 V à 4,096 V, les commutateurs à 120 Ω, et des résistances d'isolation de 100 Ω sont ajoutées aux cellules mémoire de 10 nF. Les références moitié et double utilisent désormais un pont et des amplificateurs en contre-réaction.

![Schéma de l'étage de correction](p2_calibration.png)

## Domaine et formule

Pour p=3, m∈[1,2], l'état géométrique suit idéalement

    s⁺ = s (1 + m s³/2) / (1/2 + m s³),  s₀ = 1.
    y = 1/s ; y → ∛m.

L'inversion de l'état transforme exactement cette itération en Halley. P2 conserve donc Halley direct comme témoin. Une construction à la règle et au compas ne démontre pas une meilleure consommation électronique.

Convention électrique : Vin=4,096m V est imposée indépendamment de Vref. La cible est Vout=4,096∛m V. Les valeurs d'entrée vont de 4,096 à 8,192 V ; les rails proposés sont ±15 V. Reset 50 µs, calcul 30 µs, acquisitions 20 µs, cycle 100 µs, six cycles ; mesure à 645 µs. Cette mesure finale n'est pas une mesure de temps minimal d'établissement.

## Résultats calculés

| Chaîne | Erreur brute max., six entrées | Après correction, quatre entrées inédites | Variations isolées, réglages gelés |
|---|---:|---:|---:|
{chr(10).join(lines)}

Entrées inédites : 1,1 ; 1,35 ; 1,6 ; 1,9. Les deux points d'étalonnage sont exclus du maximum corrigé. Chaque scénario de variation est testé à 1,1 et 1,9 uniquement. Il n'y a ni balayage continu ni garantie de maximum sur tout l'intervalle. Les erreurs internes du cœur sont celles du scénario déterministe `untrimmed_stress` de P1 : gain ±0,1 %, offset ±5 mV, offset buffer ±1 mV, résistances ±0,1 %, fuite 5 nA et injection 5 pC, suivant un vecteur de signes fixe. Ce sont des hypothèses de stress, pas des spécifications constructeur assemblées.

![Courbes et sensibilité](p2_results.png)

## Étalonnage effectivement simulé

Le premier inverseur reçoit Vbrut via 10 kΩ et Vtrim via 1 MΩ ; sa résistance de retour est Rf. Le second a un gain −1. Au régime idéal,

    Vcorrigé = a Vbrut + 0,01 a Vtrim,  a = Rf/(10 kΩ).

Les deux paramètres calculés sont :

{settings}

Ce sont des valeurs continues de simulation, pas des valeurs E96 ni des réglages réalisables avec cette résolution sans instrumentation. Vtrim est encore une source de laboratoire idéale. Son générateur, le potentiomètre ou le DAC, sa résolution et son bruit restent à réaliser. Le modèle d'amplificateur est écrit ici : gain ouvert 10⁶, GBW 10 MHz, slew rate 20 V/µs, courant limité à 5 mA, résistance de sortie 10 Ω, limitation interne voisine de ±13 V, biais 20 pA. Offsets de correction +25 et −25 µV. Il ne reproduit pas tous les pôles, l'impédance ni la stabilité d'un composant réel. Deux essais indépendants vérifient le transfert affine à moins de 50 µV pour des entrées de 2 et 5 V.

## Sensibilité et choix de composants candidats

- **AD734** pour les produits/divisions : la fiche indique W=XY/U et une limitation d'entrée X liée à U. Attention : la commande précise du dénominateur demande de contrôler la différence U1−U2 ; brancher directement une tension sur U0 ne suffit pas. Les figures 22–23 et 28 distinguent les montages. P2 utilise encore le dénominateur fonctionnel idéal du cœur P1 et ne simule pas cette interface physique. Le routage des broches, les impédances d'entrée et cette commande sont une étape indispensable avant une carte. [Fiche AD734](https://www.analog.com/media/en/technical-documentation/data-sheets/ad734.pdf).
- **OPA192 / OPA4192** comme candidats pour les amplificateurs : plage d'alimentation compatible avec ±15 V, GBW 10 MHz, slew rate typique 20 V/µs. La page TI annonce une charge capacitive jusqu'à 1 nF : les mémoires de 10 nF nécessitent une étude de stabilité avec isolation. Les 100 Ω ajoutés sont une hypothèse de conception, non une validation constructeur. [TI OPA192](https://www.ti.com/product/OPA192).
- **ADG1211**, quadruple commutateur : résistance typique 120 Ω et fonctionnement sous ±15 V. Le modèle conserve volontairement les 5 nA et 5 pC du stress P1 ; il ne prétend pas modéliser ce composant. [ADG1211](https://www.analog.com/en/products/adg1211.html).
- **ADR4540**, référence nominale 4,096 V. Une variation ±200 ppm est testée comme sensibilité après étalonnage, sans l'attribuer à une température particulière. [ADR4540](https://www.analog.com/en/products/adr4540.html).

Les autres variations isolées sont ±100 ppm sur Rf et +25 µV sur les offsets des deux amplificateurs de correction. Les réglages ne sont pas recalculés. Ces variations ne sont pas des coins thermiques complets : le drift du multiplicateur, la référence du générateur d'entrée et les corrélations ne sont pas modélisés.

Un calcul utile explique l'effet de la référence. À Vin constant, le circuit idéal fournit Vout=Vref^(2/3) Vin^(1/3). Une petite variation relative ε de Vref produit donc environ (2/3)ε en sortie. Une variation de 200 ppm donne environ 133 ppm, soit 0,0133 %. Avec une entrée ratiométrique Vin=m Vref, l'interprétation serait différente ; les conventions ne doivent pas être mélangées.

## Portée et prochaine décision matérielle

P2 montre qu'un étage électrique peut remplacer la correction hors ligne dans le modèle. Les erreurs faibles après réglage sont propres au modèle et au vecteur d'erreurs retenu. Elles ne garantissent pas une précision de silicium, une supériorité AD/Halley ni une nouveauté historique.

Les sources comportementales n'absorbent pas un courant d'alimentation réaliste : aucun chiffre d'énergie, puissance ou surface ne peut être déduit de ces essais. Le bruit, les tolérances des condensateurs, les composants parasites, le vieillissement, l'impédance réelle des ports AD734, la commande de dénominateur, l'électronique des horloges et les protections ne sont pas validés. Les buffers et le gain 5/3 de Halley restent des macros P1. Aucune nouvelle preuve Lean n'est ajoutée : les garanties du modèle mathématique exact ne couvrent pas ces circuits.

La prochaine étape est de réaliser et vérifier **une seule cellule XY/U avec sa vraie commande de dénominateur**, puis la mémoire isolée, avant d'assembler les cinq cellules arithmétiques de la chaîne AD à sortie inverse seule. La sortie géométrique de diagnostic porte le modèle actuel à six cellules, contre trois pour le cœur Halley direct. Ces nombres ne comptent pas les amplificateurs auxiliaires et ne constituent pas une comparaison de consommation.

## Reproduction

Python avec numpy et matplotlib ; ngspice accessible dans PATH (ou /opt/homebrew/bin/ngspice).

```sh
python simulate_p2.py
python verify_stage.py
python make_report.py
```

`core_p1.py` est une copie autonome du générateur P1 ; `simulate_p2.py` en transforme explicitement le circuit. `ad_p2.cir` et `halley_p2.cir` sont les netlists finales à m=2 ; les `.log` et `.csv` contiennent les résultats. Les `.cir` peuvent être exécutés seuls avec `ngspice -b` dans un répertoire temporaire ; ils écrivent `waveform.txt`. `results.json` conserve les réglages, toutes les entrées et les scénarios. `stage_validation.json` contient les deux contrôles indépendants.
'''
(P/'README.md').write_text(report)
with (P/'comparison.csv').open('w') as f:
 w=csv.DictWriter(f,fieldnames=list(r['results'][0]['nominal'][0])+['case']);w.writeheader()
 for z in r['results']:
  for x in z['nominal']+z['frozen_calibration_corners']:w.writerow(x)
(P/'requirements.txt').write_text('numpy>=2.0\nmatplotlib>=3.8\n')
print('Report and figures written')
