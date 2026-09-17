import json
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch,Polygon
P=Path(__file__).parent
r=json.loads((P/'results.json').read_text());cs=r['cells'][:-1]
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':11,'axes.spines.top':False,'axes.spines.right':False})
f,ax=plt.subplots(1,2,figsize=(12,4.8),layout='constrained')
a=np.loadtxt(P/'cell_nominal.csv',delimiter=',',skiprows=1);b=np.loadtxt(P/'cell_naive.csv',delimiter=',',skiprows=1)
ax[0].plot(a[:,0]*1e6,a[:,1],color='#263d46',ls='--',label='Consigne U')
ax[0].plot(a[:,0]*1e6,a[:,2],color='#117d83',label='U avec asservissement')
ax[0].plot(b[:,0]*1e6,b[:,2],color='#c45f3f',label='Commande directe U0')
ax[0].set(xlabel='Temps simulé (µs)',ylabel='Dénominateur (V)',title='Cellule isolée • scénario nominal');ax[0].legend(loc='lower right',fontsize=9)
for z,c in zip(r['chains'],['#117d83','#c45f3f']):
 v=[x for x in z['nominal'] if x['m'] not in [1,2]]
 ax[1].plot([x['m'] for x in v],[x['corrected_error']*1e6 for x in v],'o-',color=c,label=z['mode'])
ax[1].set(xlabel='Entrée normalisée m',ylabel='Erreur relative (ppm)',title='Boucle intégrée • étalonnage gelé')
ax[1].axhline(0,lw=.6,color='#666');ax[1].legend()
f.suptitle('P3 • Commande du dénominateur avec transistor simplifié',fontsize=15)
for x in ax:x.grid(alpha=.15)
for ext in ['png','svg']:f.savefig(P/f'p3_results.{ext}',dpi=170)
plt.close(f)
f,ax=plt.subplots(figsize=(13,6));ax.set_xlim(0,13);ax.set_ylim(0,6);ax.axis('off')
def line(x):ax.plot(*zip(*x),color='#2b454c',lw=1.7)
def box(x,y,w,h,s):
 ax.add_patch(FancyBboxPatch((x,y),w,h,boxstyle='round,pad=0.06',facecolor='#eff6f4',edgecolor='#117d83',lw=1.5));ax.text(x+w/2,y+h/2,s,ha='center',va='center',fontsize=11)
ax.text(.3,5.5,'P3 — Commander le dénominateur au bon endroit',fontsize=19,weight='bold',color='#173b43')
ax.text(.3,5.03,'Topologie de principe • U2 à la masse • modèle interne Qu/Ru simplifié',fontsize=12)
ax.add_patch(Polygon([[2.4,2.5],[2.4,4],[3.9,3.25]],fill=False,edgecolor='#117d83',lw=1.7))
ax.text(2.55,3.65,'+');ax.text(2.55,2.8,'−');ax.text(2.94,3.26,'AOP',ha='center',fontsize=10)
line([(.3,3.7),(2.4,3.7)]);ax.text(.3,3.97,'U demandé')
line([(3.9,3.25),(4.8,3.25)]);ax.text(4.15,3.57,'U0',ha='center')
box(4.8,2.7,2,1.1,'Qu\ntransistor NPN')
line([(6.8,3.25),(8.2,3.25)]);ax.text(7.4,3.58,'U1 mesuré',ha='center',color='#117d83')
box(8.2,2.7,2.1,1.1,'Ru ≈ 28 kΩ\nvers U2 = 0 V')
line([(7.4,3.25),(7.4,1.65),(1.9,1.65),(1.9,2.8),(2.4,2.8)])
ax.text(4.6,1.85,'Contre-réaction sur U1',ha='center',fontsize=11)
line([(4.35,3.25),(4.35,4.4),(5,4.4)]);box(5,4.15,1.8,.5,'2 MΩ');line([(6.8,4.4),(7.4,4.4),(7.4,3.25)])
box(10.85,2.7,1.6,1.1,'Cœur\nXY/U')
ax.annotate('',xy=(11.65,2.65),xytext=(7.4,1.65),arrowprops=dict(arrowstyle='->',color='#117d83',lw=1.5,connectionstyle='angle,angleA=0,angleB=-90,rad=10'))
ax.text(9.7,1.18,'U = U1 − U2',color='#117d83',ha='center')
ax.text(6.5,.55,'L’amplificateur compense la chute base-émetteur ; U0 seul ne fixe pas U.',fontsize=13,ha='center')
ax.text(6.5,.12,'Broche DD reliée à VP pour désactiver la référence interne • schéma de principe, pas plan de fabrication',fontsize=10,ha='center')
for ext in ['png','svg']:f.savefig(P/f'p3_servo.{ext}',dpi=170,bbox_inches='tight')
plt.close(f)
rows=[]
for z in r['chains']:
 held=[x for x in z['nominal'] if x['m'] not in [1,2]]
 rows.append(f"| {z['mode']} | {1e6*max(abs(x['corrected_error']) for x in held):.3f} ppm | {1e6*max(x['servo_error_at_sample_volts'] for x in z['nominal']):.3f} µV |")
naive=r['cells'][-1]
text=f'''# Pandrosion analogique P3 — cellule XY/U et commande du dénominateur

17 septembre 2026. **58 simulations SPICE : 28 cellules isolées, 28 essais des chaînes intégrées et deux contrôles avec pas temporel réduit.** P1 et P2 sont conservés sans modification.

La commande de dénominateur par amplificateur et transistor simplifié fonctionne dans les scénarios testés et préserve la convergence numérique observée des chaînes cubiques AD et Halley. Cette étape remplace une entrée idéale U par une boucle électronique dynamique. **Il s'agit d'un modèle de faisabilité, pas d'un modèle constructeur AD734 ni d'une validation de carte ou de puce.**

## Correction de la référence documentaire

La commande précise de dénominateur est la **figure 29 de la fiche AD734, révision E**, et non la figure 28 mentionnée dans P2 ; cette dernière concerne la racine carrée. La topologie a aussi été inspectée visuellement dans la figure 10, page 8, de la révision C du même fabricant, hébergée par DigiKey. Sources : [AD734 révision E](https://www.analog.com/media/en/technical-documentation/data-sheets/ad734.pdf), [copie de la révision C](https://media.digikey.com/pdf/Data%20Sheets/Analog%20Devices%20PDFs/AD734.pdf).

Pour notre usage à dénominateur positif : entrée + de l'amplificateur à la consigne, entrée − à U1 (broche 4), sortie à U0 (3), U2 (5) à la masse, résistance 2 MΩ entre U0 et U1. DD (13) est reliée à VP (14) pour désactiver la référence interne. W (12) est rebouclée sur Z1 (11), Z2 (10) à la masse. Les paires X1/X2 et Y1/Y2 reçoivent les signaux différentiels. Alimentation proposée ±15 V, découplages locaux à prévoir conformément à la fiche. Ces connexions sont issues du montage documenté ; elles ne constituent pas une invention nouvelle.

![Commande du dénominateur](p3_servo.png)

## Modèle simulé et hypothèses

Un NPN approximatif représente Qu, avec Ru=28 kΩ entre son émetteur U1 et la masse. Le collecteur est raccordé à une alimentation idéale +15 V dans notre approximation ; le circuit interne réel qui reçoit ce courant n'est pas reproduit. Le cœur calcule encore XY/U au moyen d'une source comportementale dynamique.

Paramètres supposés du NPN, **non extraits du silicium AD734** : Is=10⁻¹⁵ A, β=199, Vaf=100 V, Cje=2 pF, Cjc=1 pF, Tf=0,3 ns. Capacité supplémentaire sur U1 : 2, 20 ou 200 pF. Ru : 22,4 / 28 / 33,6 kΩ, correspondant à un balayage ±20 %. La fiche indique cette tolérance de la résistance interne, mais la conversion réelle courant–dénominateur et ses compensations internes ne sont pas modélisées.

L'amplificateur réutilise le modèle P2 : gain ouvert 10⁶, GBW 10 MHz, slew rate 20 V/µs, courant limité à 5 mA, résistance de sortie 10 Ω, offset +25 µV. Ce modèle à un pôle ne suffit pas à garantir les marges de stabilité du composant réel. Aucun modèle constructeur ni PDK n'est utilisé.

## Essais isolés

La commande passe de 1,024 à 4,096 puis 3,25 V, avec transitions de 100 ns. X=1 V, Y=4 V ; le quotient idéal est 4/U. Le produit et les entrées X/Y restent idéaux dans cet essai, avec une réponse de sortie à constante de temps 100 ns.

Les 27 combinaisons Ru × capacité × température (0, 27, 70 °C) passent :

- Erreur finale de dénominateur inférieure à **{max(abs(x['final_den_error']) for x in cs)*1e6:.3f} ppm**.
- Après la fin du front montant, établissement de U à ±0,1 % en au plus **{max(x['rise_settle_0p1pct_us'] for x in cs):.3f} µs**.
- Après le front descendant, au plus **{max(x['fall_settle_0p1pct_us'] for x in cs):.3f} µs**.

L'établissement signifie que tous les échantillons restants du plateau testé sont dans la bande. Ce n'est ni une marge de phase ni une garantie d'absence d'oscillation dans toutes les conditions. La température affecte le transistor SPICE ; le modèle d'amplificateur, les résistances et le reste du cœur n'ont pas de dérive thermique ajoutée. Il ne s'agit donc pas d'une qualification thermique du circuit.

Un contrôle volontairement naïf impose directement la consigne à U0, sans asservissement : l'erreur finale de U atteint **{naive['final_den_error']*100:.2f} %**, et celle de XY/U **+{naive['final_output_error']*100:.2f} %**. Il illustre la chute base-émetteur qui manquait au modèle initial ; il ne représente pas le montage recommandé par le fabricant.

![Résultats de P3](p3_results.png)

## Réintégration dans les boucles

Une commande DEN indépendante est ajoutée à chaque cellule arithmétique : six pour le modèle AD avec sortie géométrique de diagnostic, trois pour Halley direct. Pour une version AD avec la seule sortie inverse, cinq cellules arithmétiques suffiraient ; P3 conserve le diagnostic. Les limiteurs de port utilisent maintenant les dénominateurs effectivement produits par ces commandes.

La formule exacte de l'état AD reste, pour p=3 :

    s⁺ = s (1 + m s³/2) / (1/2 + m s³), s₀ = 1 ; y = 1/s.

Par inversion, elle est conjuguée à Halley. Les hypothèses électroniques ne modifient pas cette identité idéale, mais les trajectoires simulées comportent des erreurs.

Même convention P2 : Vin=4,096m V, cible 4,096∛m V, m∈[1,2]. Après reset et six cycles, lecture à 645 µs. Étalonnage électrique ajusté à m=1 et 2, puis gelé. Entrées inédites : 1,1 ; 1,35 ; 1,6 ; 1,9.

| Chaîne | Erreur de sortie maximale, entrées inédites | Écart de commande U au point de lecture, six entrées |
|---|---:|---:|
{chr(10).join(rows)}

Quatre essais supplémentaires par chaîne changent Ru à 22,4 ou 33,6 kΩ avec capacité 200 pF, aux entrées 1,1 et 1,9, sans réétalonnage. Ils passent le seuil de 30 ppm choisi pour cette étude. Ce ne sont pas des maxima sur tout l'intervalle ni des coins complets de fabrication. Les erreurs déterministes du cœur sont celles du scénario P2 `untrimmed_stress`, sans ajouter la variabilité réelle du multiplicateur.

Les deux répétitions à pas maximal 20 ns, au lieu de 100 ns, vérifient la sortie finale à m=2 pour AD et Halley ; les écarts sont conservés dans `VALIDATION.json`. Cela vérifie la sensibilité au pas sur ces deux sorties finales, pas la précision de toutes les pointes transitoires.

## Décision pour la suite

L'asservissement du dénominateur mérite d'être retenu pour un prototype de laboratoire. **La priorité suivante est l'impédance réelle des ports X/Y et la charge imposée aux mémoires**, puis la vérification avec modèles fabricants et mesures sur une cellule. Le cœur P1/P2, encore utilisé ici, ne reproduit pas ces impédances : relier directement ses mémoires à une entrée physique peut changer fortement le résultat.

Le calcul numérique globalement convergent ne garantit pas la convergence d'un circuit saturé. La garde max(U,0,4 V) du modèle sert au démarrage numérique ; une protection physique contre un dénominateur trop faible et le séquencement d'alimentation restent à concevoir. Le modèle de servo ajoute un courant de collecteur mais le cœur et les amplificateurs utilisent encore des sources comportementales : **aucun bilan crédible d'énergie, puissance, surface ou avantage AD/Halley n'en découle**. Pas de nouvelle preuve Lean, pas de résultat de silicium et pas de nouveauté historique revendiqués.

## Fichiers et reproduction

Python, numpy, matplotlib et ngspice sont nécessaires.

```sh
python simulate_p3.py
python verify_p3.py
python make_report.py
```

`core_p1.py` et `p2_base.py` sont des copies autonomes des générateurs précédents. `cell_nominal.cir`, `cell_naive.cir`, `ad_p3.cir`, `halley_p3.cir` sont exécutables avec ngspice ; lancer chaque circuit dans son propre répertoire car ils écrivent tous `waveform.txt`. Les CSV et logs sont conservés. Les paramètres de modèle sont explicites dans `simulate_p3.py`. `results.json` contient les 56 essais principaux ; `VALIDATION.json` documente les deux contrôles supplémentaires.
'''
(P/'README.md').write_text(text)
(P/'requirements.txt').write_text('numpy>=2.0\nmatplotlib>=3.8\n')
print('Report and figures generated')
