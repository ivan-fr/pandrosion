# Formalisation des papiers : résultats et limites

Pour le manuscrit **v14**, consulter la table séparée [V14_COVERAGE.md](V14_COVERAGE.md), qui précise les nouveaux résultats et les obligations encore ouvertes.

**Il ne s'agit pas d'une certification intégrale des trois PDF.** Certains énoncés
imprimés doivent être corrigés. Le projet contient des théorèmes mathématiques
vérifiés par Lean ainsi que des preuves des objections à plusieurs revendications.
Les théorèmes non traités ne sont ni supposés vrais ni remplacés par des `sorry`.

Le tableau [CLAIM_COVERAGE.md](CLAIM_COVERAGE.md) suit les énoncés imprimés un par un.

## Résultats effectivement formalisés

| Source | Résultat | Fichier et portée |
| --- | --- | --- |
| Reciprocal Geometry, §2, théorème 2.1 | Identité géométrique, caractérisation et unicité du point fixe positif, lecture donnant une racine positive | `LeanMath/Papers/Raw.lean`. Pour `p ≥ 1`, `x > 0`, `s > 0`. La caractérisation est `step p x s = s ↔ x*s^p = 1`. |
| Reciprocal Geometry, théorème 4.1 et corollaire 7.1 | Encadrement global et certificat indépendant de la méthode | `LeanMath/Papers/Bracket.lean`. Pour **tout entier** `p ≥ 1`, pas seulement des degrés testés. La racine est représentée par `r > 0` et `r^p = x`. `upper_formula` vérifie que la borne supérieure est exactement la formule imprimée. |
| Reciprocal Geometry, §6.1, proposition 6.1 et théorème 6.2 | Coordonnée de Cayley, imparité, réciprocité des trois corrections, identification de Halley | `LeanMath/Papers/Cayley.lean`. Réciprocité pour tout `R > 0`. Identification de Halley pour tout réel `p > 1`. |
| Reciprocal Geometry, §6.2 et annexe A | Positivité des coefficients, ordre des troncatures, identité du résidu différentiel de degré cinq, factorisation et stricte négativité sur `0 < y < 1` | `LeanMath/Papers/Cayley.lean`. Pour tout **réel** `p > 1`. La dérivée utilisée dans le résidu est également prouvée par `HasDerivAt`. Les étapes analytiques sont désormais établies dans les modules complémentaires ci-dessous. |
| Note de recherche, proposition 1, ingrédients généraux | Majoration par la corde exponentielle et minoration de Jensen | `LeanMath/Papers/Corrections.lean`. Mesures de probabilité générales, y compris continues et supports d'exposants signés. Les deux lemmes généraux explicitent leurs hypothèses d'intégrabilité. |
| Note de recherche, proposition 1, exemple `m=1,n=3,μ=2,h=log 5` | Encadrement corrigé `log 2 ≤ z ≤ log 5/2`, et amélioration stricte de `log 5/3` | `old_optimality_refuted`, dans `Corrections.lean`. Les hypothèses se limitent au support, à la moyenne et au moment ; l'intégrabilité est démontrée automatiquement pour ce support borné. |
| Note de recherche, correction de Reciprocal Geometry 11.7 | Une racine carrée n'est pas une expression rationnelle uniforme dans l'entrée | `no_rational_square_root`, dans `Corrections.lean`. Pour **tout corps** `K`, aucune `f : RatFunc K` ne satisfait `f^2 = X`. |

## Pourquoi les textes ne peuvent pas être déclarés tous corrects tels quels

### Beyond Monomials, théorème 4.2 : optimalité

La phrase affirmant qu'aucune borne utilisant seulement `μ,m,n,h` ne peut être
plus serrée est fausse. Pour toute loi de probabilité portée par `[1,3]`, de
moyenne `2`, dont le moment exponentiel au point `z` vaut `5`, Lean démontre :

```text
log(5)/3 < log(2) ≤ z ≤ log(5)/2.
```

La nouvelle borne inférieure dépend des mêmes données, et elle est strictement
plus grande. L'argument utilise une intégrale générale, pas une expérience sur
des poids particuliers. Le calcul `endpointMGF 1 3 2 (log 2) = 5` est aussi
vérifié. Le fichier `ExampleLaw.lean` réalise cette moyenne et ce moment par la
loi `(δ₁+δ₃)/2` ; les contraintes ne sont donc pas fictives.

Cela réfute l'**optimalité annoncée**, pas les inégalités non optimales. La note
de recherche signalait déjà cette correction. En particulier, le présent travail
ne présente pas cette observation comme une nouvelle découverte.

### Reciprocal Geometry, théorème 11.7 : rationalité

Pour `p=2`, la phase dyadique calcule une racine carrée. Une fonction rationnelle
uniforme donnant cette opération devrait vérifier `f(X)^2=X`. Lean exclut cette
identité par le degré entier d'une fonction rationnelle : le degré d'un carré
non nul est pair, alors que celui de `X` vaut `1`.

La correction est de parler de **fonctions matricielles primaires**, comme le
fait la note, et de réserver la rationalité aux opérations locales pour les
degrés entiers. Il s'agit de rationalité comme fonction de l'entrée, pas de la
possibilité d'interpoler une fonction d'une matrice fixée avec des coefficients
dépendant de cette matrice. La preuve formelle ne réfute pas la convergence
matricielle et ne la démontre pas non plus.

### Reciprocal Geometry, section 8 : trois corrections supplémentaires

Le fichier `RealCorrections.lean` prouve les objections suivantes :

- **Théorème 8.2, cas `0 < p < 1`** : l’affirmation que toutes les troncatures
  dépassent la fonction exacte est fausse. Pour `p = 1/2` et `R = 3`,
  `C₅(p,R) = 7 < 9 = R^(1/p)`. Les coefficients `a₃(1/2)` et `a₅(1/2)`
  ont des signes opposés, contrairement à l’argument imprimé. Les résultats
  déjà prouvés pour `p > 1` restent valides ; le régime inférieur à un doit
  être étudié séparément, sans cette règle uniforme.
- **Théorème 8.3** : remplacer `1 ≤ p < 2` par `1 < p < 2` dans
  l’inégalité stricte. À `p = 1`, le centre vaut exactement `R`.
  `subquadratic_above_root`, dans `BilateralRange.lean`, prouve la version corrigée.
- **Corollaire 8.4 et figure 5** : l’égalité de largeur à `p = 3` est fausse
  pour `C₇`. Pour tout `R > 1`, Lean prouve `G₃(R) = C₃(R) < C₇(R)`, puis
  `log L₃(R) - log C₇(R) < (log L₃(R) - log D₃(R))/2`.
  `WidthComparison.lean` étend maintenant cette inégalité à tout résidu positif
  non unitaire et à tout degré réel `p ≥ 3`. Pour `p = 2`, le rapport est
  strictement supérieur à `1/2`. La classification pour les autres degrés réels
  entre 1 et 3 reste ouverte. Le corollaire et la figure devront être révisés.

## État vérifié au 6 septembre 2026

La compilation intégrale et l’audit des dépendances ont réussi pour **455
théorèmes**. Aucun `sorryAx` ni axiome supplémentaire n’est accepté.

| Modules complémentaires | Résultats vérifiés |
| --- | --- |
| `Comparison`, `CayleyConvergence`, `Family`, `CertifiedConvergence`, `MonotoneIteration` | Comparaison globale et convergence depuis toute valeur positive des corrections de Cayley d’ordres 3, 5 et 7, pour tout réel `p > 1`. |
| `LocalOrder`, `CayleyLocal`, `CayleyCubic`, `CayleyQuintic` | Limites définissant les ordres locaux exacts 3, 5 et 7, avec coefficients strictement positifs. |
| `RawConvergence` | Convergence de l’itération brute pour degré entier `p ≥ 2`, entrée `x > 1` et initialisation positive. |
| `Dyadic` | Borne d’arrondi, contraction logarithmique, récurrence du résidu et entrée en temps fini pour la phase dyadique répétée. |
| `ExtremalBracket`, `ExtremalOptimality` | Existence et unicité de la borne corrigée β, encadrement pour mesures de probabilité générales à support borné et réalisation des deux extrémités lorsque le support est contenu dans l’intervalle. |
| `RealBracket`, `Bilateral` | Encadrement pour degré réel `p > 1`, expression logarithmique du centre, réciprocité, comparaison à la racine pour `p > 2`, exactitude à `p = 2`, identification de Halley à `p = 3` et inégalité du centre sur une cellule explicite. |

### Centre géométrique : ordre local et régime global supplémentaire

`BilateralLocal.lean` prouve la limite de l’erreur logarithmique du centre :

```text
lim[e → 0, e ≠ 0] (e + log Gₚ(exp(-p e))) / e³ = (p-1)²(p-2)/6.
```

Pour `p > 2`, le coefficient est strictement positif ; pour `1 < p < 2`,
il est strictement négatif. Le cas `p = 2` est déjà prouvé exact.
`BilateralRange.lean` prouve également la continuité du centre et la convergence
sans sauvegarde depuis toute initialisation positive pour `2 < p ≤ 3`.

### Raccordement dyadique/Cayley d’ordre sept

`Hybrid.lean` établit l’entrée en temps fini, l’invariance, l’identification de
la suite après entrée avec les itérations locales et le transfert de convergence.
Il explicite les hypothèses sur la méthode locale ; `CayleyHybrid.lean` les
prouve pour Cayley d’ordre sept et conserve son coefficient local exact.

`GuardedRoot.lean` relie ce modèle à la mise à jour sur les estimations positives :

```text
si |log(x / u^p)| ≤ p ε : u ← u C₇,p(x/u^p)
sinon                    : u ← u Qp,s(x/u^p)
```

Pour tout entier `p ≥ 2`, `s ≥ 0`, `ε > 0`, `x > 0` et `u₀ > 0`, cette
itération converge vers `x^(1/p)`. Le test utilise le résidu connu, sans accès
à la racine. Il s’agit d’un théorème en arithmétique réelle exacte ; une
implémentation numérique avec erreurs d’arrondi reste à développer et à mesurer.
Le centre géométrique est désormais couvert séparément par `BilateralHybrid.lean`
et `GuardedCenter.lean`. Pour tout entier `p ≥ 2`, le test est celui de la cellule
`αₚ = 1 + 1/√p` : utiliser le centre lorsque `|log R| ≤ log αₚ`, sinon la
phase dyadique. Le rayon en erreur logarithmique est `log αₚ/p`. La cellule
est invariante, la phase dyadique y entre en temps fini et l’itération converge
vers la racine depuis toute initialisation positive. Le cas `p = 2` est exact
une fois la phase locale activée.

### Beyond Monomials : mesures générales, branches et méthodes globales

Les nouveaux résultats ne supposent pas que la mesure est une somme finie.
`ExponentialFamily.lean` traite une mesure finie non nulle à support borné :
analyticité réelle sur toute la droite, loi inclinée normalisée, identité du
résidu, dérivée égale à la moyenne, dérivée seconde égale à la variance, moyenne
comprise entre les bornes du support, convexité et stricte convexité hors du cas
presque sûrement constant. L’identité entre dérivées et cumulants est prouvée
**pour tout ordre positif**, par translation de la fonction génératrice.

`BranchStructure.lean` exclut trois racines distinctes, prouve la monotonie sur
les branches et l’existence et unicité d’une solution pour tout niveau lorsque
le support est strictement positif. La classification complète pour un support
signé, avec existence du minimum et nombre exact de solutions, reste ouverte.

`BranchConvergence.lean` prouve la convergence des deux membres globaux sur une
branche sélectionnée : correction par l’exposant maximal et correction par la
moyenne. Les hypothèses donnent un point inférieur commun à l’initialisation et
à la racine, avec moyenne strictement positive. La seconde correction est Newton ;
sa première mise à jour est au-dessus de la racine et les suivantes convergent.
Les constantes asymptotiques et les restes de Taylor de ces deux méthodes sont
désormais certifiés dans `NewtonLocal.lean` et `BranchTaylor.lean` (détails ci-dessous).

`Reflection.lean` prouve la réflexion de la fonction génératrice et la parité de
toutes ses dérivées. `MonomialBoundary.lean` prouve le produit réciproque supérieur
ou égal à un et caractérise son égalité à un argument non nul par une loi
presque sûrement constante. La fonction génératrice logarithmique de cette loi
est exactement linéaire.

### Inversion des séries et terminaison sûre

`SeriesReversion.lean` vérifie les six coefficients de l’annexe A par une
composition de polynômes : les coefficients jusqu’au degré six de la composition
sont exactement ceux de `X`. `AnalyticReversion.lean` vérifie aussi la composition
dans l’autre sens et raccorde ces identités à un reste analytique pour toute
loi inclinée fixée. Le coefficient d’erreur de l’itération, dans laquelle les
cumulants varient avec l’itéré, est désormais vérifié dans
`CumulantCoefficient.lean` (voir le complément final ci-dessous).

`SafeBracket.lean` vérifie la dichotomie sur une branche strictement monotone :
intervalle emboîté contenant la racine, largeur divisée par deux à chaque étape,
erreur du milieu bornée par `(b-a)/2^(n+1)` et terminaison à toute tolérance
positive. Ce module constitue une routine de secours certifiée ; il ne valide
pas à lui seul l’algorithme 1 imprimé, dont la sonde de fermeture est inaccessible
après la boucle.

## Raffinements et largeurs : complément vérifié

Cinq modules complètent les comparaisons des sections 7 et 8 :

- `StrictBracket.lean` prouve les deux bornes strictes pour tout réel `p>1`,
  `R>0`, `R≠1`, et place le centre géométrique strictement entre elles.
- `RefinementOrdering.lean` prouve la comparaison centre/Halley sur `R>1` :
  centre inférieur si `p>3`, supérieur si `1<p<3`. La dérivée factorisée
  est vérifiée algébriquement dans Lean.
- `CrossBracket.lean` prouve les chaînes complètes de raffinement pour les
  trois noyaux et tout réel `p≥2`, ainsi que l’inclusion stricte de leurs
  intervalles certifiés dans l’intervalle original, de chaque côté de 1.
- `WidthComparison.lean` définit le rapport de largeur avec la bonne branche
  de chaque côté de 1. Il prouve `0<Γ<1` pour `p≥2`, `Γ<1/2` pour `p≥3`
  et `Γ>1/2` pour `p=2`, pour tout résidu positif non unitaire.
- `WidthLocal.lean` prouve la limite bilatérale `Γ→1/2` pour tout réel `p>1`.
  La preuve établit les équivalents quadratiques des largeurs et utilise
  l’erreur de Cayley d’ordre sept déjà prouvée. Il s’agit d’une limite
  analytique vérifiée, pas d’une estimation numérique.

## Vitesses locales et résidus négatifs : complément vérifié

`NewtonLocal.lean` prouve le coefficient quadratique de Newton pour toute
fonction réelle de classe C² à dérivée non nulle à la racine, puis le spécialise
à la famille exponentielle. Le coefficient est la variance de la loi inclinée
divisée par deux fois son espérance, soit `κ₂/(2κ₁)`. Il est strictement positif
sur une branche croissante non dégénérée. Le facteur linéaire de l’enveloppe
est `1-κ₁/n` et appartient alors strictement à `(0,1)`.

`BranchTaylor.lean` complète ces limites par les restes annoncés dans le
théorème 5.1 : `O(e²)` pour l’enveloppe, `O(e³)` pour Newton. Les preuves
construisent des fonctions analytiques multipliées par ces puissances d’erreur ;
les estimations big-O en découlent formellement. La convergence globale était
déjà vérifiée sur une branche croissante délimitée par un point où la dérivée
est positive. Les hypothèses exactes restent visibles dans les signatures.
Le cas monomial d’une loi de probabilité est exact en un pas pour Newton
et pour l’enveloppe lorsque son paramètre n est l’exposant du monôme.

`NegativeBracket.lean` complète le cas `h<0`, `z<0`, `μ>0` : `z≤h/μ`,
et `h/m≤z` lorsque `m>0`. Il utilise Jensen et la borne inférieure du support.
Aucune optimalité nouvelle n’est affirmée pour ces bornes ; la réfutation de
l’optimalité imprimée pour le cas positif reste valable.

## Réversion analytique des cumulants : complément vérifié

`AnalyticReversion.lean` passe des jets polynomiaux aux fonctions analytiques.
Pour toute fonction h analytique en zéro, avec h(0)=0 et h′(0)≠0, le polynôme
inverse Q de degré six calculé à partir de ses dérivées vérifie
`Q(h(z))-z = z⁷ B(z)` près de zéro, où B est analytique. La preuve utilise la
divisibilité exacte de la composition polynomiale par X⁷ et une différence
divisée polynomiale sans singularité lorsque ses deux arguments coïncident.
Le reste est donc O(z⁷), et l’erreur divisée par z⁷ possède une limite finie.

Cette conclusion est spécialisée aux cumulants d’une loi inclinée générale
à support borné et moyenne non nulle. Le module définit également le noyau
effectif `cumulantStep` et prouve son exactitude en un pas pour une loi monomiale
de probabilité d’exposant non nul.

Cette étape à loi fixée est maintenant complétée par le contrôle à base variable,
la propagation dans le polynôme inverse et le calcul du coefficient explicite,
décrits ci-dessous. La preuve finale ne suppose pas que la loi inclinée reste
fixe pendant l’itération.

## Taylor avec point de base variable : complément vérifié

`MovingTaylor.lean` considère le polynôme de Taylor de degré n basé en x,
évalué à une cible fixe r. Sa dérivée par rapport à x se réduit exactement à
`g⁽ⁿ⁺¹⁾(x)(r-x)ⁿ/n!`, par annulation de tous les autres termes. Ce résultat est
prouvé pour tout entier n, puis utilisé pour obtenir la limite du reste lorsque
x=r+e tend vers r.

Pour n=6, le module identifie ce polynôme au jet construit avec les cumulants
au point r+e et prouve

`[g(r)-g(r+e)-P_{r+e}(-e)] / e⁷ → -κ₇(r)/5040`.

Il en déduit une borne O(e⁷) le long de ce chemin à base variable. Tous les
cumulants d’ordre positif sont également prouvés analytiques en fonction du
point courant. Le noyau effectif `cumulantStep` est analytique au voisinage
d’une racine simple et fixe cette racine.

**Le coefficient -κ₇/5040 ci-dessus est celui du reste du résidu, pas celui
de l’erreur après l’application du noyau inverse.** La propagation à travers
ce polynôme inverse et le coefficient complet sont traités dans le complément
suivant.

## Noyau cumulant : ordre sept et coefficient explicite vérifiés

Le théorème local 5.2 est maintenant formalisé pour le noyau `cumulantStep`,
avec une mesure finie non nulle à support réel borné et une moyenne inclinée
non nulle à la solution. Les cumulants sont recalculés au point courant.

- `CumulantPropagation.lean` prouve l’identité exacte de propagation du reste
  par une différence divisée et sa contribution `-κ₇/(5040κ₁)` au coefficient.
- `PolynomialPaths.lean` contrôle les coefficients variables de la composition
  polynomiale, de degré au plus 36. Les termes de degrés inférieurs à sept
  s’annulent ; la somme finie restante dépend analytiquement du point courant.
- `CumulantOrder.lean` assemble ces deux contributions et prouve la limite de
  l’erreur divisée par e⁷ pour l’itération complète.
- `AnalyticLimitFactor.lean` prouve qu’une fonction analytique possédant une
  telle limite admet un facteur analytique e⁷, puis un reste analytique e⁸.
- `CumulantCoefficient.lean` calcule le coefficient de composition de degré
  sept et vérifie l’expression universelle suivante, sans calcul numérique.

En posant a=κ₁, b=κ₂, c=κ₃, d=κ₄, e=κ₅, f=κ₆, g=κ₇ à la solution :

```text
N₇ = a⁵g - 28a⁴bf - 56a⁴ce - 35a⁴d²
     + 378a³b²e + 1260a³bcd + 280a³c³
     - 3150a²b³d - 6300a²b²c² + 17325ab⁴c - 10395b⁶.
```

Le résultat final est `e⁺ = -N₇ e⁷/(5040κ₁⁶) + O(e⁸)`.
`full_remainder_explicit` certifie le reste O(e⁸), y compris lorsque N₇=0 ;
`exact_order_seven` certifie l’ordre exact sept lorsque N₇≠0. La formule de N₇
est dérivée ici du noyau explicite : le PDF renvoie son développement à une
référence antérieure au lieu de l’imprimer. Cette formalisation fournit donc
une expression autonome à inclure dans la réécriture.

Ce résultat est local. Une variante sauvegardée est maintenant certifiée
ci-dessous ; son acceptation définitive des candidats et les arrondis ne sont
pas couverts par le théorème local.

## Variante de solveur sauvegardé certifiée

Les modules `GuardedBracket.lean` et `GuardedCumulantSolver.lean` assemblent
un intervalle fini, le noyau cumulant, une garde centrale, un secours par le
milieu et un test d’arrêt fondé sur la largeur. Le protocole exact, les
hypothèses d’initialisation et ses limites figurent dans [SOLVER.md](SOLVER.md).

Le candidat est accepté dans la moitié centrale de l’intervalle ; sinon le
milieu est utilisé. La largeur est multipliée par au plus 3/4 à chaque étape.
Lean prouve l’inclusion de la racine, les intervalles emboîtés, la convergence
des milieux et l’arrêt fini à toute tolérance positive. L’intervalle retourné
a une largeur inférieure à 2ε et son milieu une erreur inférieure à ε.

Pour les supports uniformément positifs, l’initialisation est explicite pour
toute cible et ne suppose pas la racine connue. Pour un support signé non
dégénéré, elle est certifiée à partir d’un point a de la branche croissante
avec g′(a)>0 et g(a)≤c, grâce à une borne supérieure par tangente.

Cette variante est un modèle sur les réels exacts. Elle diffère du test de
résidu de l’algorithme 1 imprimé. Son ordre asymptotique sept et l’acceptation
définitive de tous les candidats ne sont pas affirmés : la garde centrale
peut rejeter des candidats proches d’une extrémité. L’initialisation générale
depuis un point arbitraire sur un support signé reste à compléter.

## Travail restant — aucune validation implicite

- Premier papier : caractérisation exacte des degrés pour lesquels le facteur
  dyadique est nul, formules algébriques des degrés dyadiques, classification
  du rapport de largeurs pour les degrés réels non entiers entre 1 et 3.
  Les cas R=1 et les inclusions entre les deux raffinements ne sont pas encore
  regroupés dans les nouveaux théorèmes ; les chaînes strictes et les rapports
  hors R=1 sont vérifiés.
- Extensions complexes et matricielles du premier papier.
- Beyond Monomials : limites de la moyenne aux extrémités du support,
  classification complète des branches signées et assemblage des variantes
  restantes d’encadrement. Les constantes locales des deux membres globaux,
  leurs restes de Taylor et le théorème local d’ordre sept du noyau de cumulants
  sont désormais vérifiés.
- Solveur : initialisation depuis un point arbitraire sur un support signé,
  réflexion automatique, acceptation définitive permettant de conserver
  l’ordre sept, et implémentation numérique avec contrôle des arrondis.
  La variante à garde centrale et ses deux initialisations sont certifiées.
- Note : optimalité avec support exactement imposé, positivité des coefficients
  de Cayley à tous les ordres, famille d’ordres 9, 11, etc., garanties en norme
  matricielle, rayon `0,9`, constante `0,403`, certificat conditionnel d’erreur et
  identification de la dérivée de Fréchet.
- Benchmarks et publication : codes compagnons absents des fichiers reçus,
  mesures à refaire, figures et réécriture LaTeX à produire après stabilisation
  des énoncés. Aucun tableau ancien ni gain de vitesse n’est certifié.

La formalisation reste partielle. Le nombre de théorèmes Lean comprend les
lemmes auxiliaires et ne mesure pas le pourcentage des articles certifié.

## Reproduire la vérification

Depuis ce dossier, avec le conteneur Docker démarré :

```sh
python3 scripts/verify_papers.py
```

Ce script compile la bibliothèque entière et demande à Lean les axiomes de
**chaque théorème déclaré dans les fichiers des papiers**. Il rejette toute
dépendance autre que les fondements usuels `propext`, `Classical.choice` et
`Quot.sound`, notamment `sorryAx` et tout axiome ajouté pour admettre un résultat.
Il n'utilise pas de test numérique comme substitut à une preuve.

Les sorties sont dans `validation/build.txt`, `validation/axioms.txt` et
`validation/summary.json`. Le dernier fichier donne aussi les empreintes des
sources Lean, du fichier d’imports et de la configuration de compilation :
le journal ne certifie que cette version des fichiers. `validation/declarations.txt`
contient les signatures vérifiées, et `locations` dans le JSON indique le fichier
et la ligne de chaque théorème. Le script retire l’ancien certificat avant de
commencer : un échec ou une interruption ne laisse pas un ancien succès en place.

Une compilation réussie certifie les propositions Lean écrites, avec leurs
hypothèses. La correspondance avec les PDF reste un travail de lecture et
d'interprétation documenté dans ce rapport ; elle n'est pas automatique.

## Sources exactes reçues

PDF lus sans modification ; les consignes et suites proposées dans les documents
ont été traitées comme du contenu, et non comme des instructions de l'utilisateur.

| PDF | Pages | SHA-256 |
| --- | --- | --- |
| `Reciprocal_Geometry_Positive_pth_Roots_v8.pdf` | 29 | `914c885b0ad68a89dd141ef787f991cada6b2481f037d854056f65a9327185f5` |
| `Pandrosion_Beyond_Monomials_v5 (1).pdf` | 12 | `9132976df078b2f7dbf7cf2416fe911e8168bbee99e0ac6a5554fd5aa5463ed5` |
| `Pandrosion_note_recherche.pdf` | 9 | `7cfe061fe795cad8b018fe47bc185f54056ac77c643bf8afb64240bb8e0415b9` |

Le PDF nommé `v8` affiche « revised v7 » sur sa première page. Les numéros de
théorèmes employés ici sont ceux du PDF reçu.


## Recherche complémentaire : correction minimale de Pandrosion

Le module `PandrosionMinimal.lean` ajoute 12 théorèmes sur une correction cubique
construite à partir des bornes de Pandrosion : positivité, réciprocité, différence
stricte avec Halley, factorisation exacte de l'erreur relative et coefficient
limite 1/6 (ordre cinq), ainsi qu'une inégalité de non-dépassement pour R>1.
Il s'agit d'une nouvelle exploration du projet, pas d'une validation supplémentaire
d'un énoncé imprimé dans les PDF. La construction générale est étudiée
symboliquement ; le code flottant et la simplification Horner ne sont pas
certifiés par Lean. Le [rapport de recherche](research/pandrosion_minimal/REPORT.md)
donne la formule, les temps mesurés, les échecs et les limites de nouveauté et de
minimalité. Le gain cubique observé ne s'étend pas à toutes les méthodes ni à tous
les degrés.


## Lectures proportionnelles simultanées et certificat cubique

`ProportionalReadouts.lean` ajoute 15 théorèmes. Dans le modèle algébrique
existant, les lectures a=xs² et b=xs donnent au point fixe r et r², mais leurs
rapports sont redondants : (a,b/a,x/b)=(xs²,1/s,1/s). Leurs moyennes harmonique
et arithmétique fournissent les facteurs H=3R/(2R+1), A=(R+2)/3. Lean vérifie
D≤H≤racine cubique de R≤A≤L ainsi que log(A/H)=log(L/D)/2 pour tout R>0.
Un intervalle positif [l,h] pour r fournit aussi [x/h,x/l] pour r². La fusion
arithmétique est exactement Newton ; aucune nouvelle accélération n'est
revendiquée. Le résultat améliore les bornes D,L de base, sans affirmer dominer
tous les certificats raffinés du projet. Voir le
[rapport et les mesures](research/proportional_readouts/REPORT.md).
La correspondance avec la vidéo fournie reste non vérifiée ; les preuves
concernent le modèle du PDF, en arithmétique réelle.


## Limite du résidu croisé

`CrossResidualObstruction.lean` ajoute quatre théorèmes : faux positif explicite
pour x=2, compagnon x/u pour tout u>0, invariance du produit sous mises à jour
réciproques, et équivalence avec le résidu ordinaire sous la condition
w=u^(p−1). Un produit uw=x ne certifie pas à lui seul les deux moyennes.
La [révision des propositions](research/proportional_readouts/PROPOSAL_REVIEW.md)
distingue ce résultat des pistes sur les cumulants et la réflexion ; elle
contient un texte de perspective corrigé, sans promesse de gain non mesuré.


## Banc numérique : évaluation structurée des moments

Le [rapport de comparaison](research/moment_evaluation/REPORT.md) étudie une
implémentation C++ de référence du noyau cumulant-7 de Beyond Monomials :
accumulation directe, table de puissances d'exposants et Horner étendu. Le test
compare les moments, cumulants et solutions à un oracle de 100 chiffres ; il
sépare préparation et résolution. Ce code numérique n'est pas certifié par Lean
et n'est pas une modification du code compagnon original, non retrouvé dans
les emplacements inspectés. Le certificat de 448 théorèmes reste inchangé.


## Couplage des puissances complémentaires

`CoupledPowers.lean` ajoute sept identités : renversement normalisé, lecture
complémentaire, préservation de cohérence, conservation du défaut, mise à jour
et rapport des résidus, équation biaisée à un faux point fixe du résidu croisé.
Le [rapport](research/reciprocal_coupling/REPORT.md) compare six implémentations
C++ conservant C7,p, y compris la sortie finale X/u. Les contrôles flottants,
les mesures et les extensions matricielles ne sont pas certifiés par ces
identités. Le fragment LaTeX corrige les promesses de gratuité du couplage.

## Systèmes posynomiaux multivariés et capture du candidat rapide

Trois modules ajoutent 32 déclarations de théorèmes :

- `MultivariateGuard.lean` (10) : borne de dérivée donnant un pas contractant,
  existence/unicité par Banach, bornes résidu/erreur, sauvegarde radiale,
  convergence géométrique, acceptation définitive pour une borne locale d'ordre
  entier strictement supérieur à un, et transfert local résidu/erreur.
- `PosynomialSystem.lean` (17) : système à coefficients positifs et exposants réels
  finis, loi inclinée normalisée, dérivée de chaque log-partition, jacobien de
  moyennes, appartenance à l'enveloppe convexe des choix de lignes, certificat de
  contraction par exposant, dominance diagonale suffisante, existence/unicité
  pour toute cible logarithmique sous ce certificat.
- `LogThompson.lean` (5) : transport logarithmique/exponentiel sur l'orthant positif,
  distance de Thompson pondérée et transfert d'une contraction vers une solution.

La [note mathématique](research/multivariate_convergence/README.md) donne les
formules de réversion d'ordre cinq avec contractions mixtes, les conditions
correctes pour les poids communs et les M-matrices, et une extension sur papier
à l'enveloppe rectangulaire uniformément inversible via Newton amorti.

La preuve Lean d'acceptation suppose une borne locale sur le candidat ; la
réversion cubique fait l'objet de l'étape distincte ci-dessous. Les P-matrices, la globalisation
Newton sous cette hypothèse et le raccord des poids au certificat de support
ne sont pas formalisés. Les contractions hybrides portent sur la distance à la
solution, pas sur tous les couples de points. L'audit actualisé est dans
`validation/summary.json` ; les anciens décomptes dans les sections historiques
et les PDF restent des décomptes de leurs révisions respectives.

## Enveloppe compacte, M-matrices et réversion cubique

Quatre modules ajoutent 24 déclarations de théorèmes :

- `CompactJacobian.lean` (4) : famille compacte d'opérateurs injectifs donnant une
  borne uniforme strictement positive sur ||Av||/||v|| ; compacité d'une enveloppe
  convexe finie ; borne des différences sous représentation sécante explicite.
- `CompactPosynomial.lean` (7) : compacité de l'enveloppe rectangulaire de supports
  finis, passage matrices/opérateurs, identification au jacobien et borne uniforme
  sous det A≠0 sur toute l'enveloppe. La spécialisation utilise la norme sup.
- `MMatrixSign.lean` (7) : principe du minimum et équivalence exacte, pour une
  Z-matrice réelle, entre l'existence de w>0 avec Aw>0 et l'inversibilité avec
  inverse composante par composante non négatif.
- `CubicReversion.lean` (6) : contraction directionnelle d'un tenseur d'ordre trois,
  reste de Taylor vectoriel le long d'une courbe C³, correction effective de degré
  deux, constante d'erreur cubique et raccord à des données de courbe explicites.

La borne de Taylor utilisée est M3||h||³/2, non optimale. Le module cubique prouve
une estimation de la correction à partir d'un reste, et non seulement une implication
supposant l'ordre du candidat. Les identités de dérivation des courbes posynomiales,
les bornes locales uniformes et l'instanciation automatique de la capture restent
à raccorder. L'ordre cinq n'est pas formalisé.

Restent également ouverts dans Lean : la représentation intégrale des sécantes,
la surjectivité globale par ouverture/fermeture et la globalisation Newton amorti.
La positivité existentielle de σ est prouvée, mais aucune valeur numérique de σ
n'est calculée. Voir les sections 7 et 8 de la
[note multivariée](research/multivariate_convergence/README.md).


## Raccordement global et cubique — audit de 550 théorèmes

Cette étape remplace les anciens statuts « à raccorder » concernant les sécantes,
la surjectivité et la spécialisation cubique. Les cinq nouveaux modules ajoutent
39 déclarations : le corpus complet contient **550 théorèmes**, compilés et audités
par `scripts/verify_papers.py`. Les seules dépendances axiomatiques admises sont
`propext`, `Classical.choice` et `Quot.sound` ; ce nombre comprend le travail scalaire.

- `PosynomialDifferential.lean` : régularité des fonctions log-partition, identification
  de leur dérivée à la jacobienne, dérivées secondes et troisièmes effectives,
  bornes sur les boules compactes et jacobienne comme équivalence linéaire continue.
- `GlobalPosynomial.lean` : représentation effective des sécantes dans l'enveloppe
  rectangulaire par le théorème des accroissements finis appliqué séparément à
  chaque ligne ; bornes globales inférieure et supérieure ; injectivité, surjectivité
  par ouverture/fermeture et unicité pour toute cible logarithmique ou positive.
  L'hypothèse porte sur **toutes** les matrices de l'enveloppe. Aucune hypothèse
  supplémentaire de coercivité n'est nécessaire après la borne globale obtenue.
- `PosynomialCubic.lean` : dérivées de la courbe segment, reste uniforme de Taylor,
  véritable candidat inverse-Taylor cubique, erreur et résidu cubiques uniformes
  près de la racine, puis acceptation définitive le long d'une suite convergente.
- `DampedNewton.lean` : amortissement explicite, décroissance du résidu sous un
  certificat de reste de Taylor, taux géométrique sur le sous-niveau initial et
  convergence ; sauvegarde par comparaison des résidus.
- `GuardedPosynomial.lean` : convergence de l'orbite sauvegardée et acceptation
  définitive du candidat cubique effectif, sous un certificat de décroissance du
  pas de secours. L'erreur satisfait ensuite une majoration cubique uniforme.

**Portée exacte.** Le certificat quantitatif de Taylor du pas amorti reste une
hypothèse explicite ; sa construction numérique automatique à partir des supports
n'est pas formalisée. Les constantes σ et les bornes compactes sont existentielles.
La spécialisation posynomiale emploie la norme sup ; les constantes euclidiennes
sur papier doivent être converties. La contraction obtenue concerne la distance
à la solution dans la métrique du résidu, pas toutes les paires de points.
L'ordre cinq, le test fini des mineurs pour les P-matrices, l'arithmétique flottante
et les comparaisons de performance restent hors de cette certification.

Le manuscrit autonome est dans `research/multivariate_convergence/manuscript/`.
Les PDF sources précédents ne sont pas modifiés. Le détail reproductible de
l'audit et les empreintes des sources sont dans `validation/summary.json`.
