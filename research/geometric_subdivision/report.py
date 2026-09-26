"""Generate the report and scientific figures from saved SPICE waveforms."""
import json,shutil,hashlib,subprocess,sys
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from spice import ROOT,steady_metrics


def enrich(path,key,folder):
 d=json.loads(path.read_text())
 for i,r in enumerate(d[key]):
  if 'error' in r:continue
  r.update(steady_metrics(r,np.loadtxt(folder/f'case_{i:03d}'/'trace.csv',skiprows=1)))
 path.write_text(json.dumps(d,indent=2)+'\n');return d

def main():
 main=enrich(ROOT/'results/summary.json','rows',ROOT/'results')
 validation=enrich(ROOT/'validation.json','depth',ROOT/'depth')
 stress=enrich(ROOT/'stress/summary.json','rows',ROOT/'stress')
 for r in stress['resolution']:
  bits=int(r['profile'].replace('resolution',''));r.update(steady_metrics(r,np.loadtxt(ROOT/'stress'/f'bits_{bits}'/'trace.csv',skiprows=1)))
 (ROOT/'stress/summary.json').write_text(json.dumps(stress,indent=2)+'\n')
 accuracy=enrich(ROOT/'accuracy/summary.json','rows',ROOT/'accuracy')
 allrows=main['rows']+validation['depth']+stress['rows']+stress['resolution']+accuracy['rows']
 figs=ROOT/'figures';figs.mkdir(exist_ok=True)
 fig,axes=plt.subplots(1,2,figsize=(12,4.6),layout='constrained')
 for ax,p in zip(axes,[3.7,1e6]):
  rows=[r for r in validation['depth'] if r['p']==p and r['order']==5]
  for profile,kind,label,style in [('ideal','centered','Ideal centered','o-'),('trimmed','centered','Low-error centered + 20-bit ADC','s-'),('trimmed','direct','Low-error direct analog','^-')]:
   rr=sorted([r for r in rows if r['profile']==profile],key=lambda r:r['n'])
   ax.semilogy([r['n'] for r in rr],[max(r[f'steady_{kind}_worst_relative_error'],1e-17) for r in rr],style,label=label)
  ax.set(xlabel='Geometric subdivisions n',ylabel='Worst relative root error, last 5 µs',title=f'X = {2 if p==3.7 else 500000:,}; p = {p:g}')
  ax.grid(True,which='both',alpha=.2);ax.legend(fontsize=8)
 fig.savefig(figs/'precision-vs-depth.png',dpi=180);fig.savefig(figs/'precision-vs-depth.svg');plt.close(fig)
 selected=[(i,r) for i,r in enumerate(validation['depth']) if r['X']==500000 and r['n']==6 and r['order']==5]
 fig,axes=plt.subplots(1,2,figsize=(12,4.5),layout='constrained')
 for idx,r in selected:
  d=np.loadtxt(ROOT/'depth'/f'case_{idx:03d}'/'trace.csv',skiprows=1)
  axes[0].plot(d[:,0]*1e6,(d[:,1]+d[:,2])/2,label=r['profile'])
  axes[1].plot(d[:,0]*1e6,d[:,6],label=r['profile'])
  dest=ROOT/'examples'/f'million_p_n6_{r["profile"]}';dest.mkdir(parents=True,exist_ok=True)
  for filename in ['circuit.cir','ngspice.log','trace.csv']:shutil.copy2(ROOT/'depth'/f'case_{idx:03d}'/filename,dest/filename)
 axes[0].axhline(float(selected[0][1]['reference']),color='k',ls=':',lw=1,label='Reference')
 axes[0].set(title='Direct root voltage',xlabel='Time (µs)',ylabel='V (unit scale)')
 axes[1].set(title='Centered core voltage (before digital weight)',xlabel='Time (µs)',ylabel='V')
 for ax in axes:ax.set_xlim(0,8);ax.grid(alpha=.2);ax.legend()
 fig.savefig(figs/'million-transient.png',dpi=180);fig.savefig(figs/'million-transient.svg');plt.close(fig)
 stats={}
 for profile in ['ideal','trimmed','untrimmed']:
  rr=[r for r in main['rows']+stress['rows'] if r['profile']==profile and 'error' not in r]
  stats[profile]=dict(runs=len(rr),direct_under_1ppm=sum(r['steady_direct_worst_relative_error']<=1e-6 for r in rr),centered_under_1ppm=sum(r['steady_centered_worst_relative_error']<=1e-6 for r in rr),centered_under_1ppb=sum(r['steady_centered_worst_relative_error']<=1e-9 for r in rr),electrical_enclosures_all_samples=sum(r['steady_observed_enclosure_all_samples'] for r in rr),worst_centered=max(r['steady_centered_worst_relative_error'] for r in rr))
 (ROOT/'statistics.json').write_text(json.dumps(dict(total_spice_runs=len(allrows),high_precision_checks=validation['high_precision_checks'],profiles=stats),indent=2)+'\n')
 def sci(v):return f'{v:.3e}'
 lines=['# Subdivision géométrique et lecture Padé : preuve et prototype SPICE','',
 '**Résultat : les bornes exactes sont prouvées en Lean ; le prototype mixte fonctionne sur les cas testés, mais aucun avantage de vitesse ou d’énergie sur un calcul numérique n’est démontré.**','',
 f"Étude : {len(allrows)} simulations SPICE (252 cas structurés, 60 essais de profondeur, 128 cas aléatoires, 5 résolutions et 72 comparaisons à précision idéale fixée), {validation['high_precision_checks']} vérifications indépendantes à 100 chiffres. Les simulations aléatoires utilisent 64 couples non entiers reproductibles. Ce n’est pas une preuve électrique sur le continuum des réels.",'',
 '## Garanties Lean','',
 'Le module `LeanMath/Papers/GeometricSubdivision.lean` est compilé avec Lean 4.33.1 et Mathlib v4.33.1. L’audit `validation/geometric_subdivision/Audit.lean` ne trouve que `propext`, `Classical.choice` et `Quot.sound` : aucun `sorryAx` ni axiome ajouté.','',
 '- `midpoint_length` : la moyenne proportionnelle donne le milieu des exposants.',
 '- `interval_spec` : la subdivision conserve θ dans l’intervalle et sa largeur vaut exactement 2⁻ⁿ.',
 '- `constructed_root_bracket` : pour tous réels X ≥ 1, p ≥ 1 et tout entier n, les deux lectures Padé encadrent X^(1/p).',
 '- `pade_width` et `pade_width_bound` : identité exacte de largeur et borne uniforme z⁵/256.',
 '- `gap_independent_of_exponent` : le rapport des rails à profondeur fixée dépend de X et n, pas de p.',
 '- `centered_increment` : identité de la lecture électrique centrée, sans soustraction de deux nombres proches.',
 '- `contact_order_five` : identité polynomiale de contact avec le développement de degré 4.','',
 'Les preuves portent sur les longueurs et l’arithmétique réelles idéales. Les incidences euclidiennes trait par trait, les arrondis binaires, les transistors, la stabilité électrique et l’ordre d’une itération AK/AD ne sont pas formalisés. La borne explicite de largeur est plus informative qu’un simple O(z⁵) ; aucun théorème asymptotique séparé n’est revendiqué.','',
 'Avec Pₜ = 12 + 6(2+t)z + (t+1)(t+2)z², Qₜ = P₋ₜ, Rₜ = Pₜ/Qₜ :','',
 '`L₅ = A Rλ(z)` ; `U₅ = B / R(1−λ)(z)` ; `z = B/A − 1`.','',
 '`U₅/L₅ − 1 = λ(1−λ)(2−λ)(1+λ) z⁵ / (Pλ P(1−λ)) ≤ z⁵/256`.','',
 '## Circuit effectivement simulé','',
 'Le contrôleur numérique fournit p et X en binary64, le poids λ et les décisions de subdivision. Il décompose X par `frexp` et transporte des facteurs d’échelle en puissances de deux. Il ne calcule ni logarithme, ni exponentielle, ni racine cible. Pour comparer, le programme de référence utilise mpmath à 100 chiffres.','',
 'Chaque moyenne possède un condensateur de 20 pF, une transconductance nominale de 100 µS, un courant limité à ±1 mA et une fuite parallèle. Le courant est proportionnel à `2^parité·A·B − M²` : la moyenne apparaît comme équilibre positif du circuit. L’état initial M=1 choisit la branche positive. Les diviseurs utilisent aussi une boucle transconductance/condensateur. Les sommes et produits de la lecture sont des sources comportementales avec résistance de sortie 10 kΩ et capacité de 20 pF.','',
 '**C’est une simulation de macromodèles analogiques**, pas une netlist CMOS issue d’un PDK. Les multiplicateurs, les références, les comparateurs de programmation et les convertisseurs ne sont pas réalisés transistor par transistor. Les capacités et transconductances sont des hypothèses d’étude, pas des mesures de silicium. Les niveaux transitoires, la dynamique, la fuite, les offsets, les gains et un parasite périodique sont simulés ; le bruit thermique, les coins de fabrication, la température, la diaphonie et les saturations de toutes les cellules ne le sont pas.','',
 'La netlist déroule n cellules en cascade. Elle ne simule pas une cellule réutilisée n fois avec sample-and-hold. Le nombre de demi-cercles peut rester indépendant de p à X et tolérance fixés ; le matériel dépend aussi de la résolution et de la plage de p.','',
 'Deux sorties sont comparées : (1) moyenne des bornes électriques, convertie ou non ; (2) lecture centrée `A·(1+λ·c)`, avec `c = 6z(2+z)/Qλ` pour Padé 5. La seconde numérise A et c séparément puis recombine λ et les facteurs binaires numériquement. Le rail unité reste un registre exact. Son résultat n’est donc pas la précision d’une tension unique purement analogique. Pour l’ordre 2 cette lecture est la borne arithmétique ; pour 3 et 5 c’est la lecture Padé inférieure.','',
 '## Hypothèses de défauts','',
 '| Profil | Écart-type gain | Écart-type offset | Fuite | DAC / ADC |',
 '|---|---:|---:|---:|---:|',
 '| ideal | 0 | 0 | 10¹⁵ Ω | idéaux |',
 '| trimmed (hypothétique) | 10 ppm | 2 µV équivalents | 10¹⁰ Ω | 20 bits |',
 '| untrimmed (hypothétique) | 0,1 % | 200 µV équivalents | 10⁸ Ω | 16 bits |','',
 'Les offsets sont appliqués aux équations normalisées des cellules ; leur conversion en tension d’entrée dépend du bloc. « trimmed » désigne une cible résiduelle supposée : aucune procédure de calibration réelle n’est simulée. Un parasite sinusoïdal déterministe à 1 MHz est ajouté aux moyennes : ce n’est pas un modèle de bruit thermique. Les profils non idéaux de la grille principale ont trois tirages fixes ; cela ne suffit pas à estimer un rendement de fabrication.','',
 '## Cas demandé : p = 1 000 000, X = 500 000','',
 f"Référence : `{selected[0][1]['reference']}`.",'',
 'Erreurs maximales sur les 5 dernières µs, profil à faibles erreurs (`trimmed`, graine 271828), Padé 5 :','',
 '| n | Sortie directe : erreur relative racine | Lecture centrée + ADC : erreur relative racine | Erreur relative sur racine − 1 |',
 '|---:|---:|---:|---:|']
 for r in validation['depth']:
  if r['p']==1e6 and r['order']==5 and r['profile']=='trimmed':lines.append(f"| {r['n']} | {sci(r['steady_direct_worst_relative_error'])} | {sci(r['steady_centered_worst_relative_error'])} | {sci(r['steady_centered_worst_excess_error'])} |")
 lines += ['', '![Précision et profondeur](figures/precision-vs-depth.png)','',
 'La lecture centrée bénéficie de la petite pondération à grand p. En revanche, une profondeur accrue rend z plus petit et la soustraction électrique B/A−1 plus sensible aux offsets. Le meilleur n dépend du budget de défauts : il ne suffit pas d’augmenter l’ordre ou la profondeur. Le passage de 5 à 6 subdivisions n’est ici qu’un résultat de ce tirage, pas une règle universelle.','',
 '![Transitoire du cas demandé](figures/million-transient.png)','',
 '## Portée de la campagne','',
 'Les cas structurés incluent p=1, p=1,000001, p≈√2, p=3,7, p=37,5, p=10⁶, p=10⁶+0,125 et p=10⁹ ; X va de 1,000001 à 10¹². Les 64 couples indépendants sont distribués logarithmiquement sur 1≤p≤10⁹ et 1≤X≤10¹². √2 et les autres réels entrent par une représentation binary64, pas avec une précision infinie. Le domaine prouvé reste p≥1, X≥1 ; p<1 et X<1 ne sont pas implémentés dans cette étude.','',
 '| Profil, grille + stress | Essais | Sortie directe ≤1 ppm | Lecture centrée ≤1 ppm | Lecture centrée ≤1 ppb | Encadrement électrique observé sur toute la fenêtre |',
 '|---|---:|---:|---:|---:|---:|']
 for profile,s in stats.items():lines.append(f"| {profile} | {s['runs']} | {s['direct_under_1ppm']} | {s['centered_under_1ppm']} | {s['centered_under_1ppb']} | {s['electrical_enclosures_all_samples']} |")
 lines += ['', 'Comparaison à la même largeur relative idéale cible (10⁻⁶), pour X=500 000 et p=10⁶. La profondeur est choisie par une majoration a priori en arithmétique rationnelle, sans oracle de racine :', '', '| Lecture | n | Blocs (diagnostic inclus) | Erreur centrée idéale | Erreur centrée à faibles défauts |', '|---|---:|---:|---:|---:|']
 for order in [2,3,5]:
  rr=[r for r in accuracy['rows'] if r['X']==500000 and r['p']==1e6 and r['order']==order]
  ri=next(r for r in rr if r['profile']=='ideal');rt=next(r for r in rr if r['profile']=='trimmed')
  lines.append(f"| {order} | {ri['n']} | {ri['cells']} | {sci(ri['steady_centered_worst_relative_error'])} | {sci(rt['steady_centered_worst_relative_error'])} |")
 lines += ['', 'Padé peut réduire le nombre de cellules de moyenne tout en ajoutant des opérations à la lecture finale. Le coût global doit compter les deux. Les 72 essais à cible fixée sont conservés dans `accuracy/summary.json` ; leur garantie de précision idéale ne s’étend pas aux défauts électriques.']
 lines += ['', 'Ces comptes mélangent les ordres 2, 3 et 5 de la grille principale ; le stress indépendant utilise Padé 5. Ils décrivent uniquement les essais effectués. Les bornes électriques peuvent s’inverser ou manquer la racine : l’identité prouvée en Lean ne couvre pas les défauts du circuit. Le fichier `statistics.json` et les rapports JSON conservent les résultats défavorables.','',
 '## Temps, coût et énergie','',
 'Le temps de stabilisation est mesuré à 1 ppm de la valeur électrique finale, sans inclure programmation, acquisition, conversion et recombinaison numérique. Ce seuil peut être peu exigeant pour la petite correction à grand p ; il ne certifie pas sa précision. Les erreurs du tableau sont prises après 25 µs, sur une fenêtre de 5 µs.','',
 '| p ; X | n | Calcul numérique complet Python, médiane |', '|---|---:|---:|']
 for r in validation['cpu']:lines.append(f"| {r['p']:g} ; {r['X']:g} | {r['n']} | {r['median_ns']/1000:.3f} µs |")
 for _,r in selected:
  if r['profile']=='trimmed':lines += ['',f"À n=6, le modèle contient {r['cells']} blocs comportementaux actifs (y compris les sorties de diagnostic) et se stabilise en environ {r['settling_1ppm_to_final_s']*1e6:.2f} µs selon ce critère. Les blocs n’ont pas des coûts transistor équivalents."]
 lines += ['', 'Le calcul numérique de comparaison effectue lui aussi les n moyennes puis les deux lectures Padé, sans oracle de racine. Cette comparaison locale ne démontre aucun gain de vitesse analogique, même avant d’ajouter les conversions. Elle n’est pas une comparaison à un ASIC numérique optimisé.','',
 'Le champ `assumed_bias_energy_J` est seulement `nombre de blocs × 10 µA × 3,3 V × temps de stabilisation`. Les sources dépendantes idéales ne comptabilisent pas leur alimentation : ce champ n’est pas une énergie de puce mesurée et ne permet aucune conclusion de supériorité énergétique. Une étude de puce exige un PDK, des cellules de multiplication/division, des références et ADC/DAC réels, leur calibration et des simulations de coins/température/bruit.','',
 '## Reproduction','',
 'À la racine du dépôt, avec Lean/Lake, ngspice 46 et les bibliothèques de `requirements.txt` :','',
 '```sh','lake build LeanMath.Papers.GeometricSubdivision','lake env lean validation/geometric_subdivision/Audit.lean','python research/geometric_subdivision/spice.py','python research/geometric_subdivision/validate.py','python research/geometric_subdivision/stress.py','python research/geometric_subdivision/accuracy_campaign.py','python research/geometric_subdivision/report.py','python research/geometric_subdivision/check_results.py','```','',
 'Un essai court : `python research/geometric_subdivision/spice.py --quick`. Les deux netlists et traces représentatives sont dans `examples/`. Les traces intégrales restent locales et sont régénérables ; les JSON complets, les scripts et les figures sont conservés.']
 (ROOT/'README.md').write_text('\n'.join(lines)+'\n')
 for folder in [ROOT/'figures',ROOT/'examples']:
  for artifact in folder.rglob('*'):
   if artifact.suffix in {'.svg','.csv','.log'}:
    artifact.write_text('\n'.join(line.rstrip() for line in artifact.read_text().splitlines())+'\n')
 files=[ROOT/'spice.py',ROOT/'validate.py',ROOT/'stress.py',ROOT/'report.py',ROOT/'check_results.py',ROOT/'accuracy_campaign.py',ROOT/'accuracy/summary.json',ROOT/'results/summary.json',ROOT/'validation.json',ROOT/'stress/summary.json',ROOT/'../../LeanMath/Papers/GeometricSubdivision.lean']
 (ROOT/'provenance.json').write_text(json.dumps(dict(ngspice=subprocess.run(['ngspice','--version'],capture_output=True,text=True).stdout,python=sys.version,files={str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}),indent=2)+'\n')
 print(json.dumps(stats,indent=2))
if __name__=='__main__':main()
