# Pandrosion analogique P5 — racine cubique d'ordre 3 en un seul passage, du modèle V30 au niveau transistor

21 septembre 2026. Suite de P0–P4 (`research/pandrosion_analog_p*`) et du circuit SPICE du papier V30 (`output/github/pandrosion-v23/research/analog_fast_ad/`, netlist `p3_ideal.cir`, générateur `spice.py`). Ces dossiers sont conservés sans modification.

**Question posée : la puce analogique AD d'ordre 3 (Halley équivalente) peut-elle calculer une seule racine, ici ∛m pour m∈[1,2], aussi vite qu'un calcul numérique, avec une bonne précision ?**

**Réponse au niveau des modèles simulés : oui pour la latence, avec une précision de 11 à 13 bits après étalonnage deux points.** Le cœur transistor s'établit à 10⁻⁴ en 2,4 ns (copies de courant idéales) ou 6,4 ns (tout transistor) après un front d'entrée de 1 ns, contre 14,3 ns par racine pour la bibliothèque JavaScript sur le même Apple M5 (temps amorti, `benchmark_results.json` du dépôt) et 1,55 ns par élément pour NumPy vectorisé. Le circuit V30 mettait 2,905 ms (six cycles) ou 2,385 ms (politique rapide). **Ce sont des résultats de simulation avec des modèles génériques, sans PDK, sans layout, sans bruit, et sans convertisseurs d'entrée/sortie : ce n'est pas une puce mesurée.** Un calcul numérique garde 53 bits ; le circuit n'en garde que 11 à 13.

![Résultats](p5_results.png)

## 1. D'où vient le temps du circuit V30

Le SPICE p=3 de V30 réalise la figure AD (support mobile κ=[p+1+(p−1)t]/2) en coordonnées centrées q=p(u−1) : lecture q → étage carré d₀=q+q²/6 → étage produit d₁=d₀+(q−d₀)/3+(2/9)d₀q → t=Y(1+d₁) → q⁺=q+2(1+q/3)(1−t)/(1+t+(t−1)/3). Quatre étages à τ=1 µs, deux mémoires de 10 nF, une période de 500 µs, six cycles, lecture à 405 µs de chaque cycle.

La netlist relancée localement (0,13 s de calcul) donne l'erreur d'état par cycle à partir de q₀=0 : 1,9×10⁻² après le cycle 1, 9,8×10⁻⁷ après le cycle 2, 3,9×10⁻⁹ dès le cycle 3 (plancher du modèle). **Plus de 99,9 % du temps est de l'attente d'horloge et d'acquisition, pas de l'arithmétique.** L'ordre cubique rend l'itération inutile dès que l'amorce est à environ 1 % de la racine.

## 2. Géométrie : amorçage par une corde, puis un seul support AD

Au lieu de partir du point fixe s₀=1 (ou q₀=0), on part d'un point de la corde : une fonction affine de m. `oneshot_math.py` (mpmath, 60 chiffres, 4 001 points) donne l'erreur relative maximale sur [1,2] :

| Amorce | Erreur de l'amorce | Après un pas AD | Bits | Après deux pas |
|---|---:|---:|---:|---:|
| s₀=1 (P0–P4, V30) | 2,06×10⁻¹ | 7,87×10⁻³ | 7,0 | 3,29×10⁻⁷ |
| y₀=(3+m)/4, ratios de miroirs 3:1 | 1,72×10⁻² | 3,49×10⁻⁶ | 18,1 | 2,84×10⁻¹⁷ |
| y₀ minimax affine | 7,44×10⁻³ | 2,72×10⁻⁷ | 21,8 | 1,34×10⁻²⁰ |
| s₀ minimax affine (forme AD, utilisée pour la chaîne V30) | 1,52×10⁻² | 2,26×10⁻⁶ | 18,8 | 7,74×10⁻¹⁸ |

La constante cubique mesurée de Halley pour y³=m vaut 0,6657 (théorie 2/3) ; la conjugaison AD/Halley y=1/s est vérifiée à 3×10⁻⁶¹ sur l'amorce retenue. Un seul pas suffit donc bien au-delà de toute précision analogique : **le circuit devient combinatoire, sans mémoire, sans horloge, sans reset.** Sa latence est la somme des retards des cellules. Ce sont des contrôles numériques, pas de nouveaux théorèmes Lean.

## 3. Étape 2 — la chaîne V30 en un seul passage (`simulate_ff.py`, 30 simulations)

Mêmes macros d'étage que V30 (source B écrêtée ±2 V, filtre 10 Ω/C, 2 pF de port, 50 kΩ de charge en stress), même profil de stress (offsets 25 µV, gain produit 0,1 %). Différences : amorce q₀=0,5834−0,6189·Y au lieu de la mémoire, correction AD appliquée une fois, Y devient un signal (un produit de plus). τ est un paramètre d'étude.

| τ par étage | Profil | Erreur finale, Y : 1→2 | Établissement à 10⁻³ | à 10⁻⁴ | à 10⁻⁵ |
|---|---|---:|---:|---:|---:|
| 1 µs (filtres V30) | idéal | 2,26×10⁻⁶ | 10,9 µs | 13,9 µs | 17,0 µs |
| 1 µs | stress V30 | 5,76×10⁻⁴ | 12,1 µs | non atteint | non atteint |
| 1 ns | idéal | 2,26×10⁻⁶ | 11,1 ns | 14,1 ns | 17,3 ns |

Le temps est proportionnel à τ (modèle comportemental). À modèle d'étage identique, le passage de 2 905 µs à 13,9 µs est un gain d'environ 200 fois dû à l'architecture seule. Sur le profil de stress, un étalonnage affine à Y=1 et 2 laisse au plus 6,6×10⁻⁵ sur Y=1,1 ; 1,5 ; 1,9 (`derived.json`), ce qui est cohérent avec les 2,1×10⁻⁴ non étalonnés de V30 à p=3. Cinq échelons différents sont simulés par configuration ; le dénominateur reste supérieur à 2 (garde 0,25 V jamais activée).

## 4. Étape 3 — réalisation translinéaire en mode courant (`translinear.py`)

Pour aller à la vitesse d'une puce, l'arithmétique passe en **mode courant translinéaire** (transistors bipolaires) : une unité = I₀ = 100 µA, l'entrée est I_m = m·I₀. Les sommes N et D de la figure AD deviennent des nœuds de Kirchhoff, α=1/2 devient un rapport de miroir, les produits et quotients deviennent des boucles à jonctions montantes/descendantes (type B de Gilbert).

Forme réciproque (Halley, conjuguée de AD) : amorce y₀=(3I₀+I_m)/4 ; boucle à 6 jonctions y₀³/I₀² ; N=y₃/2+I_m, D=y₃+I_m/2 ; boucle à 4 jonctions y₁=y₀N/D. Forme d'état AD (s→m^(−1/3), puis 1/s) : 8+4+4 jonctions. Témoin : racine translinéaire directe, boucle à 6 jonctions I_m·I₀·I₀=I_out³ avec recopie de la sortie (boucle de rétroaction de gain 2, stable dans ces essais).

Hypothèses de transistor, **génériques et non issues d'une fonderie** : NPN Is=2×10⁻¹⁷ A, β=400, Vaf=100 V, Ikf=50 mA, Rb=40 Ω, Re=1,5 Ω, Tf=25 ps, Cje=15 fF, Cjc=8 fF ; PNP β=100, Vaf=60 V, Tf=60 ps. Transistors auxiliaires de compensation des courants de base sur chaque diode, polarisés à 0,2·I₀. Rails ±2,5 V (T1) ou +4/−2,5 V (T2). Front d'entrée nominal 1 ns.

Trois contributions à l'erreur ont été isolées par ablation (`I0=100 µA`) : la forte injection (Ikf) domine le résidu après étalonnage (2,5×10⁻⁴ à Ikf=8 mA contre 2,3×10⁻⁶ à Ikf infini), puis la résistance d'émetteur, puis l'effet Early. Le choix Ikf=50 mA correspond à un émetteur plus large ; le compromis courant/précision/vitesse est mesuré au §5.

### Niveau T1 : boucles à transistors, copies de courant idéales (`simulate_tl.py`, 260 simulations)

Étalonnage affine à m=1 et m=2 (réglage de banc, comme P2–P4), validation sur 39 points intérieurs et sur 1,1 ; 1,35 ; 1,6 ; 1,9.

| Chaîne | Jonctions + auxiliaires | Erreur brute max. | Après étalonnage, 39 points | Échelon 1→2, 10⁻³ / 10⁻⁴ | Échelon 2→1, 10⁻⁴ |
|---|---:|---:|---:|---:|---:|
| Un pas AD, forme 1/s (Halley) | 10 + 5 | 0,42 % | **46 ppm** | 1,93 / **2,40 ns** | 2,52 ns |
| Un pas AD, forme s (état de Pandrosion) | 16 + 8 | 0,83 % | 142 ppm | 4,89 / 9,21 ns | 2,46 ns |
| Racine translinéaire directe (témoin) | 6 + 3 | 0,52 % | 189 ppm | 1,39 / 1,65 ns | 1,87 ns |

La forme s présente une résonance peu amortie (figure b) ; à 30 µA et avec une polarisation auxiliaire fixe de 20 µA elle oscillait franchement (période ~100 ns, indépendante de l'intégrateur), ce qui a conduit à polariser les auxiliaires proportionnellement à I₀. Le témoin direct est plus petit et plus rapide ; il n'est pas moins précis de façon décisive. **La supériorité matérielle de la construction AD sur la racine translinéaire directe n'est pas démontrée**, dans la continuité des conclusions P0–P4 ; l'apport de cette étape est l'architecture en un passage, valable pour les trois chaînes.

Sensibilités (forme 1/s, étalonnage gelé à 27 °C sauf mention) : température 0 °C : 6,9×10⁻⁴ ; 85 °C : 1,6×10⁻³ (β(T) et Early ; les boucles translinéaires idéales sont indépendantes de T) ; alimentation ±0,2 V : 47 ppm ; mismatch déterministe de Is ±0,3 % / ±1 % alterné sur les jonctions, ré-étalonné : 36 / 12 ppm ; front d'entrée 0,1 ns : 1,90 ns mais 37 % de dépassement ; 2 ns : 3,02 ns.

### Niveau T2 : tout transistor, miroirs BJT (`simulate_t2.py`, 102 simulations)

Chaque copie de courant est un miroir à auxiliaire et cascode (NPN pour les puits, PNP pour les sources) : 55 transistors pour la forme 1/s. Restent idéaux : la source d'entrée, les courants de polarisation I₀, les rails et les deux tensions de cascode.

| Mesure | T2 |
|---|---:|
| Erreur brute max. sur la grille | 0,12 % |
| Après étalonnage, 39 points / points inédits | 530 ppm / 230, 510, 480, 160 ppm |
| Échelon 1→2 (front 1 ns), 10⁻² / 10⁻³ / 10⁻⁴ | 3,98 / 4,85 / **6,43 ns**, dépassement 20 % |
| Échelon 2→1 ; 1→1,5 ; 1,9→1,1 à 10⁻⁴ | 11,1 ; 6,5 ; 9,1 ns |
| Front d'entrée 0,1 ns | 32 ns, dépassement 198 % |
| Front d'entrée 2 ns, 1→2 / 2→1 | 7,3 / 11,1 ns |
| Température 0 / 85 °C, étalonnage gelé | 1,9×10⁻³ / 2,1×10⁻³ |
| Mismatch Is ±0,3 % / ±1 % (55 jonctions), ré-étalonné | 340 / 70 ppm |
| Alimentation 3,8 / 4,2 V, étalonnage gelé | 570 / 1 220 ppm |
| β=100 / 200 (ré-étalonné) | 435 / 483 ppm |

Le front de 0,1 ns révèle un défaut de conception identifié : le nœud d'entrée du miroir PNP qui recopie y³ est momentanément privé de courant, passe en blocage profond et se rétablit lentement. Un front d'entrée d'au moins 0,5 ns l'évite ; un courant de maintien sur les entrées de miroirs serait la correction de circuit, non simulée ici. La sensibilité à l'alimentation vient des tensions de cascode fixées par rapport aux rails ; une polarisation par diodes la réduirait, non simulée non plus.

## 5. Courant, vitesse et précision (forme 1/s, T1)

| I₀ | Après étalonnage | Établissement 10⁻³ / 10⁻⁴ |
|---:|---:|---:|
| 10 µA | 81 ppm | 4,24 / 5,30 ns |
| 30 µA | 53 ppm | 2,49 / 3,04 ns |
| 100 µA | 46 ppm | 1,93 / 2,40 ns |
| 300 µA | 330 ppm | 2,07 / 2,98 ns |

Au-delà de 100 µA la forte injection dégrade la précision sans gain de vitesse. Aucune consommation n'est déduite : les sources de polarisation et les rails sont idéaux.

## 6. Comparaison avec le numérique, définitions explicites

| Réalisation | Temps | Ce qui est mesuré |
|---|---:|---|
| V30, six cycles | 2 905 µs | temps de schéma imposé, lecture d'état |
| V30, politique 2 itérations | 2 385 µs | idem, mode précision |
| V30, deuxième cycle | 905 µs | état à 10⁻⁶ (rerun local) |
| Un passage, étages V30 τ=1 µs | 13,9 µs | racine à 10⁻⁴ après échelon |
| T1 transistor | 2,4 ns | idem, front d'entrée 1 ns inclus |
| T2 tout transistor | 6,4 ns | idem |
| JavaScript exp(log X/3), Apple M5 | 14,3 ns | temps amorti par appel, dépôt |
| NumPy cbrt float64, Apple M5 | 1,55 ns | débit vectorisé par élément (`bench_digital.py`) |
| Python `math.cbrt` | 16 ns | par appel, interpréteur inclus |

Les colonnes ne mesurent pas la même chose. Le cœur analogique exclut toute conversion : une entrée numérique demanderait un CNA et une lecture numérique un CAN, dont les latences dépassent souvent le cœur lui-même. Sur une entrée déjà analogique (capteur), le cœur donne une racine analogique en quelques nanosecondes, ce qu'aucun des chiffres numériques ci-dessus n'inclut non plus (acquisition). **Latence comparable pour une seule racine ; précision inférieure de 40 bits ; énergie et surface non mesurées.**

## 7. Ce qui n'est pas établi

Pas de modèle fondeur, pas de layout ni de parasites, pas de bruit thermique ou 1/f, pas de Monte-Carlo (mismatch déterministe alterné), pas de dérive après étalonnage, pas de convertisseurs, pas de séquencement d'alimentation, pas de mesure sur banc. Les deux anomalies de circuit (blocage d'entrée de miroir, résonance de la forme s) sont documentées, non corrigées. Le théorème de convergence exacte couvre la carte mathématique, pas ces circuits ; aucune nouvelle preuve Lean n'est ajoutée. Aucune nouveauté brevetable ni supériorité AD/Halley/translinéaire directe n'est revendiquée.

## 8. Reproduction et fichiers

ngspice (version locale 46), Python avec numpy, mpmath, matplotlib. `bash run_all.sh` ou, dans l'ordre : `oneshot_math.py`, `simulate_ff.py`, `simulate_tl.py`, `simulate_t2.py`, `bench_digital.py`, `make_report.py`, `verify_p5.py`. Les netlists `*.cir` sont autonomes (`ngspice -b fichier.cir` dans un dossier de travail, sortie `waveform.txt`) ; les `.log` et `.csv` (décimés) correspondent.

- `math_results.json` : amorces, erreurs après un et deux pas, constante cubique, conjugaison.
- `ff_results.json`, `ff_tau*.cir/.csv` : chaîne V30 en un passage.
- `tl_results.json`, `tl_*_dc_m2.cir`, `tl_*_step_1to2.cir/.csv` : niveau T1, trois chaînes.
- `t2_results.json`, `t2_halley_*.cir/.csv` : niveau T2.
- `bench_digital.json`, `derived.json`, `p5_results.svg/png`.
- `VALIDATION.json` : sept contrôles indépendants (reruns autonomes des netlists conservées, pas temporel 0,5 ps contre 2 ps sur l'établissement T1, grille mathématique distincte), tous passés.
- `SHA256SUMS` : empreintes des fichiers livrés.
