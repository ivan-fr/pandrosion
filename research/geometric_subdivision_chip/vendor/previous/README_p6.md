# Pandrosion analogique P6 — la chaîne généraliste de V30 en un seul passage, sans mémoire, pour tout p

21 septembre 2026. Suite de P5 (racine cubique fixe) et du circuit SPICE de V30 (`output/github/pandrosion-v23/research/analog_fast_ad/`, papier `paper/pandrosion_analog_v30/`). Rien n'est modifié dans V30 : ses modules sont importés tels quels (`v30_bridge.py`) pour la préparation numérique c,Y (Node, `prepare.mjs`), le planning d'exponentiation binaire, les profils d'erreurs, l'étalonnage électrique des cellules, l'ADC et le générateur des 64 cas de validation.

**Ce qui change : la même chaîne centrée (état q=p(u−1), étages carré/produit exacts, correction AD d'ordre 3) est exécutée en un seul passage.** Plus de condensateur d'état, plus de mémoire candidate, plus d'interrupteurs, plus de reset ni d'horloge. L'entrée de la cellule de lecture est une tension programmée q₀ (CNA, quantifiée comme les coefficients) ; la correction AD est appliquée une fois ; la lecture est le nœud candidat après établissement, converti par le même modèle d'ADC, décodé par 1/[c(1+q/p)]. La plage programmable reste 3≤p≤10⁶ et X binaire64 positif, comme V30.

![Résultats](p6_results.png)

## 1. Pourquoi un seul passage suffit, et l'amorce sans oracle

V30 itère six fois. Ses propres traces montrent qu'à p=10⁶ le premier cycle donne déjà la précision finale, et qu'à p=3 le deuxième suffit. Deux amorces sont testées :

- `zero` : q₀=0, le départ de V30 (u=1). Un passage donne alors une seule correction AD : 7,9×10⁻³ à p=3, mais 4,5×10⁻¹⁰ à p=10⁶ où la préparation numérique est déjà à 2,5×10⁻⁷.
- `ad1` : q₀=p·(C_p(Y)−1) avec C_p(Y)=(p+1+(p−1)Y)/(p−1+(p+1)Y), c'est-à-dire **le premier pas AD évalué numériquement par le contrôleur**. C'est de l'arithmétique rationnelle, sans racine, logarithme ni exponentielle, dans l'esprit de la préparation V30 (`verify_p6.py` vérifie l'identité avec le pas AD exact). Le passage analogique effectue le second pas. Erreur mathématique résultante à p=3 : 3,3×10⁻⁷, décroissante avec p.

Avec `zero`, aucun mode ne passe 1 ppm à bas degré. Tous les résultats ci-dessous utilisent `ad1` sauf mention.

## 2. Jeu de développement (`campaign_dev.py`, 69 simulations)

Cas V30 : (3, 2), (3, 5×10⁵), (32, 5×10⁵), (983039, 5×10⁵), (10⁶, 5×10⁵). Profils V30 `untrimmed` (offsets 25 µV, gain 0,1 %, 50 kΩ, coefficients 16 bits, ADC 18 bits, bruit 5 µV) et `trim_target` (hypothèses serrées, pas un résultat), à 25 et 85 °C. Mode **précision** : coefficients et ADC 24 bits, étalonnage électrique des cellules par `calibrate_cells.calibrate` (grille 81 points, bruit de mesure 0,1 µV, jamais de racine) et étalonnage de l'ADC, comme la révision de précision de V30 mais sans mémoire, donc sans compensation de fuite ni moyenne de 16 lectures. τ=1 µs par étage (filtres 10 Ω/100 nF de V30).

| p, X | untrimmed, 25 °C | trim_target | précision, 25 °C | précision, 85 °C |
|---|---:|---:|---:|---:|
| 3, 2 | 4,6×10⁻⁴ | 7,6×10⁻⁶ | 1,2×10⁻⁸ | 1,7×10⁻⁷ |
| 3, 500 000 | 4,2×10⁻⁴ | 6,8×10⁻⁶ | 4,0×10⁻⁸ | 1,0×10⁻⁷ |
| 32, 500 000 | 3,3×10⁻⁵ | 5,2×10⁻⁷ | 1,7×10⁻⁸ | 1,0×10⁻⁸ |
| 983 039, 500 000 | 5,0×10⁻⁹ | 6,7×10⁻¹¹ | 7,3×10⁻¹² | 6,9×10⁻¹² |
| 1 000 000, 500 000 | 2,1×10⁻⁹ | 3,5×10⁻¹¹ | 8,0×10⁻¹² | 7,3×10⁻¹² |

Ce sont des lectures uniques en fin de fenêtre ; à bas degré elles fluctuent avec les nœuds de bruit (5 µV tous les 10 µs) entre 10⁻⁸ et quelques 10⁻⁶ selon l'instant. L'exemple demandé **p=10⁶, X=500 000** donne 8,0×10⁻¹² en mode précision et 4,5×10⁻¹⁰ non étalonné avec q₀=0, contre 1,88×10⁻⁹ pour V30 non étalonné : même modèle d'erreurs, un passage au lieu de six cycles.

**Dynamique sans bruit** (mode précision, `dynamics_noise_free`) : l'état s'établit à 1 µV en 20 µs pour 2 étages (p=3), 26 µs pour 5 (p=32), 56 µs pour 25 (p=10⁶), 74 µs pour 37 (p=983039), soit environ 17 µs + 1,5 µs par étage à τ=1 µs. Le temps est proportionnel à τ : à τ=10 ns, tout est divisé par 100 (`tau_scaling`). Les gardes (dénominateur ≥ 0,25 V, écrêtage ±2 V) ne sont jamais activées : dénominateur minimal 2,0, pic d'étage 0,66 V.

## 3. Validation tenue à l'écart (`campaign_validate.py`, 128 simulations)

Mêmes 64 couples (p, X) que `validate_revised.py` de V30 (douze degrés × quatre X, plus seize tirages aléatoires avec la même graine), mêmes températures −20/25/85 °C, mêmes signes et graines de bruit, étalonnage refait par cas. Chaîne jusqu'à 37 étages.

| Mesure | Un passage | V30 (mode précision, 24 ms) |
|---|---:|---:|
| Cas améliorés par l'étalonnage | 63/64 | 64/64 |
| Lecture unique finale ≤ 1 ppm | **58/64**, pire 2,8×10⁻⁶ (p=3, X=0,037) | 64/64, pire 0,279 ppm |
| Non étalonné, pire | 3,8×10⁻⁴ | 4,0×10⁻⁴ |

Les six échecs à 1 ppm sont tous à p≤7, où l'erreur de racine vaut l'erreur d'état divisée par p+q : un nœud de bruit de 5 µV suffit. V30 les absorbe par la moyenne de 16 lectures sur 20 itérations de 1,2 ms.

**Politiques de lecture.** Les instants figés sur le jeu de développement (lecture unique à 15 µs pour 100 ppm, 19 µs pour 10 ppm) n'ont passé que 49/64 et 44/64 cas : le jeu de développement, hérité de V30, ne contient pas de degrés intermédiaires (10 à 20 étages) dont la chaîne s'établit plus tard. Le résultat conservé est donc la **frontière a posteriori** sur les 64 cas, l'instant le plus précoce à partir duquel tous les cas restent sous la cible jusqu'à la fin de la fenêtre (220 µs) :

| Cible | Lecture unique | Moyenne de 16 lectures espacées de 10 µs |
|---:|---:|---:|
| 100 ppm | 22 µs | 165 µs |
| 10 ppm | 30 µs | 171 µs |
| 1 ppm | jamais (6 cas) | **178 µs** |

Comparaison avec les politiques figées de V30 : 2,385 ms pour 10 ppm et 4,785 ms pour 1 ppm. Le passage unique est donc environ 80 fois plus rapide à 10 ppm et 27 fois à 1 ppm, à modèle d'étage identique, **mais ces instants n'ont pas été figés avant validation** ; une validation propre demande un nouveau jeu de développement incluant des degrés intermédiaires, puis 64 nouveaux cas. Le temps exclut, comme chez V30, la préparation numérique, la programmation des coefficients, la latence physique de l'ADC et le décodage.

## 4. Ce qui est établi et ce qui ne l'est pas

Établi au niveau du modèle : la chaîne généraliste de V30 n'a pas besoin de mémoire ni d'horloge ; un CNA d'amorce et un passage combinatoire suffisent pour tout p de 3 à 10⁶, avec la même précision que V30 hors bruit, et une lecture 27 à 80 fois plus rapide. La sortie de l'amorce `ad1` est du calcul numérique bon marché, mais elle doit être comptée : à p=3 elle fait déjà l'essentiel du travail, à p=10⁶ c'est la préparation V30 qui le fait, et six pas AD numériques coûtent 0,12 µs sur le même hôte (`benchmark_results.json`). **Aucun avantage de vitesse ou d'énergie sur le numérique n'est établi**, conclusion inchangée depuis V30.

Non établi : une chaîne tout transistor stable au-delà de p=3 (§7, niveau T2), donc la vitesse en nanosecondes de T1 pour un degré programmable, comportement des CNA de coefficients à 24 bits, bruit réel, dérive après étalonnage, layout, silicium. La fuite, l'injection de charge et les interrupteurs de V30 disparaissent avec les mémoires : c'est un gain réel de l'architecture, non une hypothèse favorable ajoutée. Aucune preuve Lean nouvelle ; les six identités de `AnalogFastAD.lean` couvrent l'arithmétique, pas ce circuit.

## 6. Politiques de lecture figées, puis 64 nouveaux cas (`campaign_policy.py`, 96 simulations)

Le jeu de développement est élargi à seize degrés couvrant 2 à 37 étages (3, 5, 7, 15, 31, 63, 127, 255, 1023, 4095, 16383, 65535, 262143, 524287, 983039, 10⁶) × X∈{2, 5×10⁵}, à 25/85 °C, mode précision, amorce `ad1`. Pour chaque cible et chaque politique, l'instant de lecture figé est le plus tardif des instants « à partir duquel le cas reste sous la cible ». Puis 64 nouveaux cas, jamais vus : seize autres degrés (4, 6, 9, 17, 33, 100, 129, 511, 1000, 2049, 8191, 40000, 131071, 300000, 700000, 999999) × X∈{0,5 ; 3,7 ; 10⁻¹⁵⁰ ; 10¹⁵⁰}, températures −20/25/85 °C, nouvelles graines de bruit, étalonnage refait par cas.

| Cible | Politique figée | Cas limitant (développement) | Validation : cas passés | Pire erreur |
|---:|---|---|---:|---:|
| 100 ppm | lecture unique à **24 µs** | p=1023 | **64/64** | 3,7×10⁻⁵ |
| 10 ppm | lecture unique à **32 µs** | p=4095 | **64/64** | 3,4×10⁻⁶ |
| 1 ppm | lecture unique | p=3 : jamais | non figée | — |
| 1 ppm | moyenne de 16 lectures à **180 µs** | p=4095 | **64/64** | 0,38 ppm |

Ces trois politiques sont figées avant validation et passent tous les cas. Comparées aux politiques figées de V30 (2,385 ms pour 10 ppm, 4,785 ms pour 1 ppm), la version sans mémoire lit 75 fois plus tôt à 10 ppm et 27 fois plus tôt à 1 ppm, à modèle d'étage identique et avec les mêmes exclusions (préparation, programmation, latence physique de l'ADC, décodage). Une lecture unique ne peut pas garantir 1 ppm à p=3 avec le bruit de 5 µV du modèle ; la moyenne de 16 lectures espacées de 10 µs y parvient.

## 7. Étages centrés en cellules translinéaires à transistors

Les étages de V30 sont transposés en mode courant avec les boucles translinéaires de P5 (niveau T1 : boucles à transistors bipolaires, copies de courant et poids programmés idéaux). Représentation positive v_n=1+d_n∈(0,3 ; 1], e_n=1−v_n≥0 par Kirchhoff ; étage carré v_{2n}=v_n+w·e_n² ; étage produit v_{n+1}=v_n−(v_n−v_q)/(n+1)+w'·e_n·e_q ; résidu t=Y·v_p. Amorce `ad1` par CNA de courant ; étalonnage affine du courant de sortie à Y=1 et 2 ; Y=X∈[1,2].

**Première itération** (`translinear_chain.py`, 204 simulations, p=3, 7, 32) : correction en deux produits soustraits, 545 ppm après étalonnage à p=3, 60 ppm à p=32, établissement à 10⁻⁴ en 11 à 12 ns sur l'échelon montant à cause de boucles qui partaient de courant nul (Y=1, q₀=0) et devaient sortir du blocage.

**Seconde itération** (`translinear_chain2.py`, `loop_trims.py`, `tl_chain_campaign2.py`, 874 simulations) :

- correction à une seule division, identité exacte vérifiée par `verify_p6.py` : (1+q⁺)·D = (3−1/p) − |q|(1+1/p) − (1−1/p)(1+|q|)·t, avec D=(1−1/p)+(1+1/p)t, soit deux boucles de moins ;
- courant de maintien : les boucles carré et produit reçoivent e+0,1 au lieu de e, les termes en trop sont retranchés par Kirchhoff, plus aucune boucle ne passe par zéro ;
- **trims électriques par type de boucle**, transposition du protocole de cellules de V30 : chaque boucle est simulée isolée avec des courants connus (25 à 54 points), ajustement affine sortie = k·idéal + o, correction par un rapport programmable 1/k et un courant de polarisation constant, jamais de racine ;
- poids programmés soit idéaux, soit quantifiés sur 16 bits avec 0,1 % d'erreur de gain alternée (CNA de courant), degrés jusqu'à p=1023 (18 étages, 126 jonctions).

| p | Jonctions | Sans trims, étalonné | **Avec trims, étalonné** | Poids CNA 16 bits | Échelon 1→2, 10⁻³ / 10⁻⁴ | 2→1, 10⁻⁴ | Dépassement (fraction du saut) | 0 / 85 °C, réglages gelés | Mismatch ±1 %, ré-étalonné |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 3 | 30 | 250 ppm | **130 ppm** | 120 ppm | 2,85 / 3,56 ns | 3,48 ns | 3,8 % | 4,7×10⁻⁴ / 1,1×10⁻³ | 130 ppm |
| 7 | 42 | 130 ppm | **55 ppm** | 54 ppm | 2,97 / 3,64 ns | 3,79 ns | 5,3 % | 2,5×10⁻⁴ / 6,0×10⁻⁴ | 55 ppm |
| 32 | 48 | 29 ppm | **11 ppm** | 12 ppm | 2,99 / 3,86 ns | 4,04 ns | 6,1 % | 6,1×10⁻⁵ / 1,5×10⁻⁴ | 11 ppm |
| 127 | 90 | 7,4 ppm | **2,9 ppm** | 3,4 ppm | 2,99 / 3,89 ns | 4,06 ns | 6,3 % | 1,6×10⁻⁵ / 3,7×10⁻⁵ | 2,9 ppm |
| 1023 | 126 | 0,92 ppm | **0,36 ppm** | 0,43 ppm | 2,99 / 3,90 ns | 4,07 ns | 6,3 % | 2,0×10⁻⁶ / 4,6×10⁻⁶ | 0,35 ppm |

Trois faits ressortent. Le temps d'établissement ne dépend pas du nombre d'étages : les boucles en courant n'ont que des retards de quelques dizaines de picosecondes, et la chaîne à 18 étages s'établit comme celle à 2 (3,9 ns à 10⁻⁴, front d'entrée de 1 ns compris ; 5,3 ns avec un front de 3 ns, dépassement alors ≤ 1,3 %). La précision de racine s'améliore avec p comme l'erreur d'état divisée par p+q, conformément à l'équation d'erreur de V30 : la chaîne transistor passe sous le ppm à p=1023 et resterait limitée à 130 ppm à p=3, où le résidu vient des non-linéarités des boucles (Ikf, résistance d'émetteur, Early) que ni le trim affine ni l'étalonnage deux points ne retirent. Le dépassement de vingt fois annoncé pour la première itération était pour partie un artefact de mesure : sur un échelon montant de Y, le courant de sortie descend, et le maximum mesuré était la valeur initiale ; avec la définition classique (fraction du saut) et le courant de maintien, il vaut 4 à 9 %.

La dérive thermique reste le point faible à bas degré (β(T) et Early ; les boucles idéales sont indépendantes de T) : un ré-étalonnage par température, comme dans V30, s'impose. Le mismatch alterné de ±1 % est absorbé par le ré-étalonnage, mais les trims par type de boucle ne sont pas des trims par instance ; un vrai circuit les ferait par instance comme V30.

### Niveau T2 de la chaîne : tout transistor (`translinear_chain3.py`, `tl_chain_campaign3.py`)

Chaque copie de courant devient un miroir bipolaire à transistor auxiliaire ; restent idéaux les courants de polarisation I₀, les deux CNA d'entrée, les courants de trim, les rails +4/−2,5 V, les tensions de cascode et de clamp. Quatre défauts ont dû être corrigés pour obtenir un circuit qui fonctionne, et chacun est une leçon de conception du mode courant :

1. **Tension de collecteur des sorties de miroir.** Sans cascode, une sortie dont le collecteur n'est pas à la tension de la diode d'entrée souffre d'un effet Early de 3 à 6 % par copie. Des cascodes sélectifs (uniquement là où la tension diffère) et un rail positif porté de 2,5 à 4 V (marge des cascodes PNP vers les nœuds d'injection à 1,6 V) ramènent les gains de copie mesurés à 0,05 % (NPN simple), 0,2 % (NPN cascodé), 0,2 % (PNP simple), 1,2 % (PNP cascodé, β=100), tous pré-compensés par le rapport de miroir.
2. **Nœuds de différence.** L'étage produit écrit v_{n+1}=v_n−(v_n−v_q)/(n+1)+… demandait un nœud portant une petite différence de deux copies ; il est réécrit sans soustraction, v_{n+1}=n/(n+1)·v_n+1/(n+1)·v_q+w'e_n e_q, identité exacte.
3. **Effondrement des nœuds de somme.** Quand, transitoirement, les puits d'un nœud de Kirchhoff dépassent ses sources, le nœud s'effondre vers le rail, les transistors de puits saturent et le circuit entre dans un cycle de relaxation de ~100 ns. Des diodes de clamp vers une référence (référence à 0,4 V sous le point nominal) l'évitent ; placées trop haut elles conduisent au repos et faussent 2 % des copies.
4. **Le numérateur de la correction** N′=(3−1/p)−|q|(1+1/p)−(1−1/p)(1+|q|)t est une différence de termes trois fois plus grands que le résultat : toute erreur de copie y est amplifiée par 3 à 4.

| Configuration | Transistors | Résultat |
|---|---:|---|
| p=3, sans trims de boucle, étalonnage 2 points | 151 | **587 ppm** sur Y∈{1,1 ; 1,35 ; 1,6 ; 1,9}, erreur brute 1,1 %, stable (dérive 1,7×10⁻⁶ sur 10 ns) |
| p=3, avec trims de boucle (nœuds de ratio ajoutés) | 179 | **instable** : dérive de 97 % sur les 10 dernières ns, échelon non établi en 110 ns |
| p=7 | 218 à 262 | **instable** (dérive de 5 à 14) |
| p=32 | 244 | **point de fonctionnement faux et oscillation** : l'analyse OP converge vers 0,006·I₀ pour 0,597 attendu, le transitoire oscille (0,19·I₀ en moyenne, excursion de 7,8 fois) ; le frontal à cinq carrés seul et le bloc de correction seul sont stables et à 2 % près, la chaîne jointe converge vers un état où les sorties de boucles sont incompatibles avec leurs entrées ; non résolu |

Le niveau T2 de la chaîne n'est donc **pas un circuit fonctionnel au-delà de p=3**. Les briques sont individuellement correctes (nœud de somme 0,2 %, boucle isolée 2 %), l'assemblage de 150 à 300 transistors possède des équilibres multiples ou des cycles limites que ni le pas d'intégration ni la méthode ne changent. Le résultat T1 (copies idéales) doit se lire ainsi : il suppose des copies exactes à 10⁻⁴ ; les miroirs réels de ce niveau les donnent à 10⁻³ avant trim, et leur assemblage n'est pas encore stable. Une variante à miroirs simples (`style='plain'`) a servi de contrôle de topologie ; elle n'est pas validée.

**Limite structurelle du mode courant** (figure `p6_transistor.png`, panneau d) : le plus petit poids programmé vaut n/(2p)=2^−(1+log₂p). Rapports de miroirs jusqu'à 2⁻⁶ (p≤32), CNA de courant 16 bits jusqu'à p≈32 000 (simulé ici jusqu'à p=1023), 24 bits comme V30 jusqu'à 10⁶. Au-delà de quelques dizaines de milliers, les poids deviennent des CNA de précision dont la vitesse n'est plus celle des boucles ; la version comportementale des §2–6 reste la référence pour les grands degrés, où par ailleurs la précision de racine est la moins exigeante.

![Politiques et transistors](p6_transistor.png)

## 8. Reproduction et fichiers

ngspice 46, Node (pour `prepare.mjs` de V30), Python avec numpy, mpmath, matplotlib. `bash run_all.sh` ou `campaign_dev.py`, `campaign_validate.py`, `campaign_policy.py`, `tl_chain_campaign.py`, `tl_chain_campaign2.py`, `tl_chain_campaign3.py`, `make_report.py`, `make_report2.py`, `verify_p6.py`. Les netlists `dev_*.cir` sont autonomes (`ngspice -b`, sortie `wave.txt`), avec `.log` et `.csv` décimés.

- `single_pass.py` : générateur de la chaîne sans mémoire (mêmes expressions de cellules que `spice.py` de V30) et mesure.
- `policies.py` : lectures unique et moyennée sur les trajectoires enregistrées.
- `dev_results.json` (69 essais), `validation_results.json` (64 cas appariés, 128 essais), `derived.json`, `p6_results.svg/png`.
- `policy_results.json` (32 cas de développement, 64 nouveaux cas), `tl_chain_results.json` (première itération), `tl_chain2_results.json` (seconde, trims et ajustements de boucles inclus), `tlc_p*`, `tlc2_p*` et `tlc3_p*` (netlists DC à Y=2 et échelons 1→2), `tl_chain3_results.json` (niveau T2), `p6_transistor.svg/png`.
- `VALIDATION.json` : quatorze contrôles indépendants (huit reruns autonomes de netlists, pas temporel divisé par quatre, identité du générateur de cas avec V30, algèbre de l'amorce, identité de la correction à une division, cohérence des résumés et recomptage des politiques figées), tous passés.
- `SHA256SUMS`.
