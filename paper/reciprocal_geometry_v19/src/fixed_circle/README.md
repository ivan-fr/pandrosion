# Padé inverse et cercle fixe : racines p-ièmes

Étude du 17 septembre 2026. Preview : `../pandrosion_geometry/fixed_circle_report.html`.

## Résultat

La piste fonctionne : **ordre local cinq pour tout entier p≥3**, **2p+2 droites mobiles** sur une représentation affine admissible, et un seul cercle préparé. Le cas cubique demandé utilise bien huit droites. Pour p fixé, le cercle est indépendant de X et de s ; le centre U(β) adapte le dispositif à X. La préparation, les supports, les centres fixes et l’inversion finale pour lire la racine directe sont exclus du coût. Ce compte décrit le protocole, pas un minimum démontré.

On construit la racine réciproque a=X^(−1/p), pour X>0, puis on lit 1/a pour obtenir X^(1/p). Le cas p=2 est exact en un pas algébrique : on peut préparer directement la racine par la construction usuelle de moyenne proportionnelle au cercle ; le protocole à huit droites et sa généralisation ci-dessous concernent p≥3.

## 1. Modèle inverse et branche stable

Poser A=(p+1)(p+2), B=p²−4, C=(p−1)(p−2),

N(v)=Cv²−2Bv+A, D(v)=Av²−2Bv+C, R(v)=N(v)/D(v).

Les lettres A,B,C dans ces formules désignent des coefficients ; les sommets du rectangle seront notés A₀,B₀,C₀.

Pour t=Xs^p, résoudre N(v)−tD(v)=0 sur la branche qui passe par v=1 lorsque t=1, puis prendre s⁺=sv. Avec

Δ=(42p²−24)t−3(p²−4)(1+t²),

une évaluation stable de cette même branche est

- t≤1 : v=(A−tC)/(B(1−t)+√Δ) ;
- t>1 : v=(√Δ−B(1−t))/(tA−C).

La seconde expression évite la singularité amovible 0/0 à t=A/C dans la première. Pour p>2, ses dénominateurs sont strictement positifs sur les deux demi-domaines indiqués. Pour p=2, l’équation devient 12(1−tv²)=0 : la branche positive est v=1/√t.

## 2. Domaine réel et choix de l’intersection

Pour p>2, Δ>0 exactement entre

τ±=[7p²−4 ± 4p√(3(p²−1))]/(p²−4), avec τ−τ+=1.

Pour p=3, τ±=(59±24√6)/5 ≈ 0,0424492346 et 23,5575507654. Quand p→∞, les bornes tendent vers **7±4√3**, et non exactement 1/14 et 14.

La branche cherchée est celle où R′(v)<0. Elle est caractérisée par

v−<v<v+, avec v±=[p²+2 ± √(12(p²−1))]/(p²−4).

En effet,

N′D−ND′=12p[(p²−4)(v²+1)−2(p²+2)v].

Cela fournit un choix géométrique fixe : sur Γ, retenir le point dont le paramètre de pinceau appartient à cet arc central. Ce critère ne demande pas de connaître la racine cherchée. La preview teste ce signe à partir du point d’intersection, sans placer le point final à partir de la formule.

**La positivité seule ne sélectionne pas la bonne intersection.** Par exemple p=3,t=0,05 donne v≈3,1182831128 et v≈6,3817168872, toutes deux positives. Seule la première appartient à la branche centrale.

Aux bornes Δ=0, la droite est tangente et la carte inverse n’est plus régulière. Le domaine réel ne doit pas être confondu avec une preuve de contraction sur tout cet intervalle : aucune telle affirmation n’est utilisée ici.

## 3. Preuve de l’ordre cinq pour p général

On a N(1)=D(1)=12 et, pour p>2, N(v),D(v)>0 pour tout v réel, grâce aux identités

C N(v)=(Cv−B)²+3(p²−4),
A D(v)=(Av−B)²+3(p²−4).

L’identité centrale est

pND+v(N′D−ND′)=pAC(v−1)^4.

Écrire v=1+u et paramétrer l’erreur logarithmique d’entrée et celle de sortie par

e(u)=log R(1+u)/p,
e⁺(u)=e(u)+log(1+u).

Alors e(0)=0, e′(0)=−1 et

(d/du)e⁺(u)=AC u⁴/[(1+u)N(1+u)D(1+u)].

Par intégration locale, e⁺(u)/u⁵→AC/720. Comme e(u)/u→−1,

**e⁺/e⁵ → −(p²−1)(p²−4)/720.**

Cette constante est non nulle pour p≥3. L’inverse local existe puisque e′(0)≠0 : il s’agit bien de l’ordre de l’itération, pas seulement d’un contact formel. Pour p=3 la constante vaut −1/18. La réciprocité R(1/v)=1/R(v) rend la carte logarithmique locale impaire ; l’expansion est e⁺=−AC e⁵/720+O(e⁷). Le terme asymptotique et le passage par la limite sont distingués : Lean certifie la limite paramétrée, pas cette dernière notation O(e⁷).

En particulier, il existe un voisinage de la racine où l’itération converge et alterne de côté. La contraction sur tout le domaine Δ>0, ainsi qu’une entrée globale certifiée dans ce voisinage, ne sont pas établies dans ce module.

## 4. Construction pour tout p≥3

Fixer O=(0,4), A₀=(2,4), B₀=(2,0), C₀=(0,0), et les rails

R₀(q)=(2,4(1−q)), L₀(q)=(0,4(1−q)), U(f)=(2f/(f−1),4).

La droite U(f)R₀(q) coupe le rail gauche en L₀(fq) ; la droite U(1/s)L₀(q) coupe le rail droit en R₀(sq).

### Paramètres fixes lorsque p≠4

Poser L=p³+12p²+39p−26 et

k=(p−2)(p²−4p+13)/L, ρ=1/2,

h=2−72p(p+4)/[(p−1)L],
j=24p(p−2)(p+4)/[(p−1)L],
zₓ=2−24p(p+4)(p−2)/[(p−4)L],
zᵧ=24p(p²+2p−26)/[(p−4)L].

Préparer M=(h,j), le cercle Γ de centre M passant par B₀, et Z=(zₓ,zᵧ). Pour p≥3,p≠4, tous ces nombres sont rationnels ; L>0. Le cercle est non dégénéré puisque j>0.

### Représentation spéciale de p=4

L’expression précédente envoie Z à l’infini à p=4. Prendre à la place

ρ=1/3, k=145/2389,
M=(13502/7167,3328/2389), Z=(−214/2389,2432/2389).

Tout reste rationnel et le coût mobile reste dix droites.

### Chaîne mobile

Préparer les centres U(ρ), U(1/2) si nécessaire, et U(β), où

β=kX·2^(p−3)/ρ.

1. Tracer C₀P, P=R₀(s), pour obtenir V=U(1/s) sur OA₀.
2. Effectuer p−1 paires de droites. Pour la paire i, projeter le point du rail droit par U(fᵢ) vers le rail gauche, puis revenir au rail droit par V. Choisir f₁=ρ, fᵢ=1/2 pour 2≤i≤p−2, et fₚ₋₁=β. Conserver le premier point gauche L₁=L₀(ρs).
3. La sortie de la chaîne est T=R₀(kXs^p). Coût : 1+2(p−1)=2p−1 droites.
4. Tracer ZT ; retenir G sur l’arc central de Γ.
5. Tracer B₀G ; son intersection avec OA₀ est U(ρ/v).
6. Tracer U(ρ/v)L₁ ; son intersection avec A₀B₀ est P⁺=R₀(sv).

Le total est donc **2p+2 droites**. Les intersections des deux rails et du cercle ne sont pas comptées comme des traces supplémentaires.

Pour p=3,X=2, on retrouve exactement k=5/113, β=20/113, M=(−152/113,126/113), Z=(478/113,396/113), T=R₀((10/113)s³). Le rayon est 126√10/113.

### Certificat géométrique

Poser d=(2v,4(ρ−v)), n=d·d et b=(B₀−M)·d. Le second point de Γ sur la droite de direction d passant par B₀ est

G=B₀−2b d/n.

L’appartenance au cercle est une identité rationnelle. Après multiplication par n, l’incidence Z,T,G s’écrit

I=(2−zₓ)(−2b dᵧ−zᵧn)−(4(1−kt)−zᵧ)((2−zₓ)n−2b dₓ).

Pour les paramètres généraux ci-dessus,

I=−384p(p−2)(p+4)(p²−4p+13)/[(p−4)(p−1)L²] · [N(v)−tD(v)].

Pour p=4, le facteur est −7720960/51365889. Pour p=3, il vaut 10080/12769. Ainsi le modèle inverse implique exactement l’alignement Z,T,G. La projection finale sur les rails donne ensuite sv.

### Hypothèses affines

Il faut s≠1 pour V fini ; β≠1 pour le dernier centre fixe fini ; v≠ρ pour U fini ; et G≠B₀ pour tracer B₀G. Les intersections effectivement utilisées doivent être propres et distinctes. Certaines de ces exclusions ne concernent pas le voisinage de la racine, mais elles restent importantes pour un protocole global. La preview signale aussi les configurations trop mal conditionnées pour ses calculs en double précision.

Un faible nombre de traits ne garantit ni compacité uniforme, ni stabilité physique. Les centres et les échelles peuvent devenir défavorables pour certains paramètres. La variante par chaînes d’addition et les changements automatiques de représentation restent à développer.

## 5. Vérifications et benchmark

`verify.py` vérifie symboliquement les identités générales, puis construit **162 figures indépendantes** à 250 chiffres (p=3,4,5,6,7,8,12,20,32 ; X∈{1,3 ; 2 ; 5} ; six entrées par couple). Les points sont calculés par intersections de droites et de cercle ; le résultat est ensuite comparé à la formule. Écart maximal observé : 4,18×10⁻²⁴³. Les données exactes du calcul sont dans `results.json`.

Pour p=3,X=2,s₀=3/4 :

| Pas | Erreur relative absolue | Droites cumulées |
|---:|---:|---:|
| 0 | 5,5059×10⁻² | 0 |
| 1 | 3,240836×10⁻⁸ | 8 |
| 2 | 1,986154×10⁻³⁹ | 16 |
| 3 | 1,717085×10⁻¹⁹⁵ | 24 |

Les seuils 10⁻⁶,10⁻¹²,10⁻³⁰,10⁻⁶⁰ demandent respectivement 1,2,2,3 pas. La preview utilise la précision ordinaire du navigateur, pas 250 chiffres ; elle signale son plancher et ne revendique pas les erreurs du benchmark haute précision.

## 6. Formalisation Lean et portée

**Compilation réussie et 28 théorèmes audités**, sans `sorryAx` ni axiome ajouté : seulement `propext`, `Classical.choice` et `Quot.sound`. Les journaux `lake_build.log` et `lean_axioms.log` conservent les résultats. Les avertissements de compilation sont des avertissements de style des tactiques, sans échec de preuve.

`LeanMath/Papers/RectangleFixedCircle.lean` contient les identités de discriminant, les deux branches quadratiques (et leurs spécialisations avec racine carrée), la positivité de N,D, la réciprocité, le certificat de dérivée, les incidences du cercle et du projecteur, les certificats géométriques pour p général et pour p=4, et la **limite analytique d’ordre cinq en erreur logarithmique**.

Le théorème `logarithmic_order_five` est paramétré par v=1+u. Le lien avec le paramètre d’entrée t utilise l’inversibilité locale e′(0)=−1, décrite plus haut ; le module ne fournit pas un théorème de convergence de la suite itérée de la formule radicale. La chaîne et les projections entre rails réutilisent les résultats de `RectanglePencils.lean`. Le compte des traits, le choix opérationnel de l’arc, la preview et les scripts numériques ne sont pas certifiés par le noyau Lean.

## 7. Reproduction

Depuis la racine du dépôt :

```sh
lake build LeanMath.Papers.RectangleFixedCircle
lake env lean validation/rectangle_fixed_circle/Audit.lean
.venv-audit/bin/python research/pandrosion_fixed_circle/verify.py
node research/pandrosion_fixed_circle/check_preview.cjs
```

Sur la machine de cette étude, les commandes Lake ont été lancées avec le Git du runtime Codex dans PATH, car le Git Apple est bloqué par la licence Xcode. Aucun réglage global n’a été modifié.

Le script Python demande SymPy et mpmath. La vérification navigateur demande Playwright et Chrome ; son chemin de dépendances peut être adapté à la machine.

## 8. Limites des affirmations historiques et de maximalité

Le modèle inverse Padé et les procédés nomographiques s’inscrivent dans des traditions anciennes. Voir Maurice d’Ocagne, *Esquisse d’ensemble de la nomographie* (1925), [texte primaire Numdam](https://www.numdam.org/item/MSM_1925__4__1_0.pdf). Cette référence ne constitue pas une preuve d’antériorité ou de nouveauté du diagramme précis.

**Aucun plafond général à l’ordre cinq n’est démontré ici.** Une traversée de cercle ajoute une extension quadratique, mais les coefficients peuvent dépendre d’évaluations rationnelles plus riches. Le simple fait qu’un autre modèle soit cubique ne suffit pas à exclure toute réalisation constructible ou tout ordre supérieur. Les deux traversées emboîtées d’ordre sept ou neuf ne font pas partie des résultats établis.
