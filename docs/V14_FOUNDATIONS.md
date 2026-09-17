# Concordance des fondations avec la v14

Cette revue porte sur les sources `02_foundations.tex`, `03_cayley_enclosures.tex` et la partie mathématique de `04_coupled_legacy.tex` extraites de la v14. Elle précise les conclusions exportées dans Lean et leurs hypothèses. Les obligations complémentaires recensées par cette revue sont désormais fermées. Une limite du quotient donne une constante dominante, mais ne suffit pas à elle seule à prouver le reste en grand O imprimé.

## Correspondances examinées

Les noms ci-dessous sont dans l’espace `LeanMath.Papers`. Les emplacements exacts et signatures sont conservés dans `validation/summary.json` et `validation/declarations.txt`.

| Passage | Preuves existantes et portée | État de la concordance |
|---|---|---|
| Chaînes proportionnelles : renversement et complément | `CoupledPowers.normalized_reversal`, `complementary_readout`, pour `r>0`, `j≤p`; `ProportionalReadouts.readout_dependence`, `repeated_ratios`, `ratio_product` pour les lectures cubiques. | Identités principales vérifiées; illustrations géométriques et chiffres des figures exclus de ce contrôle. |
| Modèle brut : pont, point fixe et lecture | `Raw.bridge`, `fixed_iff`, `fixed_point_unique`, `readout_is_positive_root`; `Raw.global_raw_convergence` pour `p≥2`, `X>1`, `s₀>0`, avec convergence de la lecture visible. | Domaine correct : ne pas étendre cet argument monotone au cas `0<X<1`. Les encadrements sans franchissement sont établis dans la preuve `converge_to_fixed_point`; le théorème final exporte les deux limites. |
| Encadrement bilatéral pour degrés réels | `RealBracket.certified_bracket`, `upper_formula`; `RealBracket.lower_strict`, `upper_strict` dans `StrictBracket.lean`. | Bornes et stricte séparation vérifiées pour `p>1`, résidu positif non unitaire. Certaines signatures paramètrent le résidu par `q^p`; cette paramétrisation couvre les résidus positifs. |
| Moyennes pondérées générales | `V14WeightedMeans.harmonic_formula`, `harmonic_le_root`, `root_le_arithmetic`, `lower_mean`, `upper_mean`, `logarithmic_width`. | **Vérifié pour tout réel `p>1`, `R>0`** : `H≤R^(1/p)≤A`, `D=R/A^(p−1)`, `L=R/H^(p−1)` et `log(L/D)=(p−1)log(A/H)`. |
| Centre : réciprocité, degrés 2 et 3 | `RealBracket.center_reciprocal`, `square_root_exact`, `cube_root_halley`; `RealCorrections.center_three_eq_C₃`. | **Vérifié, y compris l’unicité** : `V14WeightedMeans.reciprocal_blend_iff` établit que la réciprocité du mélange `D^(1−θ)L^θ` équivaut à `θ=1/2`; `blend_half` l’identifie au centre. |
| Centre : position et cellule | `RealBracket.center_below_root`, `subquadratic_above_root`, `center_above_one_on_cell`; `RealBracket.Local.negative_cell_step`, `positive_cell_step`, `cell_invariant`, `cell_convergence`. | Position et convergence dans la cellule vérifiées. Les inégalités strictes concernent `R>1`, pas son extrémité `R=1`. |
| Centre : constante cubique et reste | `RealBracket.Local.exact_cubic_limit`, `coefficient_pos`; **`V14LegacyRemainders.center_remainder`**. | **Reste `O(e⁵)` désormais vérifié pour tout réel `p>2`**, avec coefficient `(p-2)(p-1)²/6`. |
| Centre à l’infini | `V14CenterInfinity.center_factorization`, `asymptotic_ratio`, `center_tends_zero`, `eventually_residual_increases`. | **Équivalent vérifié pour tout réel `p>1`** : le quotient de `G_p(R)` par `(p−1)^((p−1)/2) R^((3−p)/2)` tend vers 1. Pour `p>3`, le centre tend vers zéro et la mise à jour sans garde augmente le résidu pour tout `R` assez grand. Ce résultat concerne le centre, distinct du Padé diagonal globalement convergent. |
| Entrée dyadique | `Dyadic.log_error_linear`, `dyadic_strict_bound`, `residual_recurrence`, `finite_entry`. | **Complété dans `V14DyadicChoices`** : `dyadic_bound` pour tout entier à distance au plus `1/2`, `nearest_positive`, `squareRoots_eq`, `nested_evaluation`, `integer_radical_residual` et `orbit_entry`. La borne par plafond vaut pour une cellule logarithmique fermée de rayon positif, lorsque l’erreur initiale la dépasse. La positivité de toute l’orbite est déduite de celle du départ. Les racines carrées sont exactes, sans modèle d’arrondi. |
| Cayley : formules, ordre global et convergence | `Cayley.chi_inv`, `unchi_chi`, `halley_formula`, `coefficients_pos`, `truncations_ordered`; `Cayley.family_identification`, `family_above`, `family_below`, `family_global_convergence` dans `Family.lean`. | Les trois corrections sont traitées pour tout réel `p>1`. Les défauts polynomiaux et leur signe sont vérifiés dans `Cayley.lean` et `Comparison.lean`. La récurrence à tous les ordres et le raccordement analytique près de zéro sont vérifiés dans `V14SeriesRecurrence.paper_recurrence_indexed` et `paper_hasSum`; `paper_low_coefficients` retrouve les coefficients imprimés. |
| Ordres locaux exacts de Cayley | `Cayley.Cubic.exact_order`, `Cayley.Quintic.exact_order`, `Cayley.exact_order_seven` et positivité de leurs coefficients; **`V14LegacyRemainders.cubic_remainder`, `quintic_remainder`, `septic_remainder`**. | **Développements complets imprimés vérifiés**, avec restes `O(e⁵)`, `O(e⁷)`, `O(e⁹)`. **Le transfert général à l’erreur ordinaire est maintenant prouvé** dans `V14OrdinaryError.transfer_remainder` et `update_remainder`, avec continuité en zéro, constante dominante et identité du changement de variable explicites. |
| Comparaisons d’extrémités | `RealBracket.lower_lt_halley` dans `CrossBracket.lean`; `RealBracket.center_lt_halley` dans `RefinementOrdering.lean`; `RealCorrections.center_three_eq_C₃`; `refined_interval_above`, `refined_interval_below`. | Seuils `p≥2`, `p>3` et cas `p=3` respectés; intervalles améliorés vérifiés. |
| Largeurs relatives | `RealBracket.widthRatio_mem_unit`, `widthRatio_lt_half`, `widthRatio_square_gt_half`, `upperRatio_inverse`; `WidthLocal.lean`, notamment `width_ratio_limit`. | Classifications et limite bilatérale `1/2` vérifiées. **Les deux restes explicites `O(t³)` sont maintenant prouvés** par `V14WidthRemainders.bilateral_width_remainder` et `upper_endpoint_remainder`, pour les véritables extrémités et tout réel `p>1`. |
| Certificat cubique emboîté | `ProportionalReadouts.harmonic_le_root`, `root_le_arithmetic`, `lower_improvement`, `upper_improvement`, `nested_bounds`, `width_ratio_square`, `logarithmic_width_half`, `arithmetic_is_newton`, `squared_root_certificate`. | Identités, améliorations et demi-largeur vérifiées. **Assemblage complété pour tout `R>0`** : `V14CubicEnclosure.nested_enclosure`, `exact_half_width`, `intersection_above` et `intersection_below` utilisent les extrémités réelles du manuscrit et la racine `R^(1/3)`. |
| Puissances couplées : invariance | `CoupledPowers.coherence_preserved`, `defect_preserved`, `pair_residual_update`, `residual_ratio_is_defect`, `biased_fixed_equation`. | Proposition d’invariance vérifiée. **Complétée par `V14CoupledOutputs.log_defect_nat`, `product_fixed_bias_nat`, `reciprocal_relative_error` et `powered_output_remainder`** : identité logarithmique, biais en puissance réelle, erreur réciproque exacte et reste quadratique de la sortie puissance. Les hypothèses de positivité sont explicites. |

## Compte des multiplications vérifié

[V14BinaryPowerCount.lean](LeanMath/Papers/V14BinaryPowerCount.lean) définit un évaluateur binaire avec compteur explicite. `run_value` prouve que sa première sortie vaut `x^n`; `multiplication_count` établit, pour tout `n>0`, que la seconde vaut `Nat.log 2 n + population n - 1`. La population est le nombre de bits vrais dans la représentation binaire canonique `Nat.bits`. Le premier bit initialise l’accumulateur sans multiplication, puis chaque bit déclenche un carré et éventuellement une multiplication par `x`.

`examples` vérifie les comptes `5 contre 3` pour `p=8`, et `15 contre 8` pour `p=256`. Il s’agit d’un compte exact des multiplications de cet algorithme, pas d’une preuve du temps machine ou du code C++ archivé.

## Sorties couplées : complément vérifié

[V14CoupledOutputs.lean](LeanMath/Papers/V14CoupledOutputs.lean) prouve, pour les entrées positives,

- `log(u/r) = -(log(R×)+log(η))/p`, avec `r=X^(1/p)` et `η=w/u^(p-1)` ;
- si `R×=1`, alors `u/r=η^(-1/p)` ;
- pour `u=r(1+δ)`, `δ>-1`, l’erreur relative de `X/u` est exactement `-δ/(1+δ)` ;
- pour tout entier `n≥0`, l’erreur relative de `u^n` est `nδ+O(δ²)`. Le choix `n=p-1` donne la formule du manuscrit.

La preuve du reste quadratique utilise une identité polynomiale pour tous les exposants naturels, y compris zéro et un. Ces résultats concernent les opérations exactes ; ils ne majorent pas l’arrondi de leur évaluation flottante.

## Transfert vers l’erreur ordinaire vérifié

[V14OrdinaryError.lean](LeanMath/Papers/V14OrdinaryError.lean) prouve le résultat général suivant : si `r>0`, `m≥1`, `f` est continue en zéro, `f(0)=0` et `f(e)/e^m → κ`, alors, avec `e=log((r+d)/r)`,

`r(exp(f(e))−1) = κ r^(1−m) d^m + o(d^m)`.

Le théorème `update_remainder` l’exprime directement pour `U(r+d)−r`, sous l’identité logarithmique de l’update près de la racine et sa positivité. Le coefficient transféré reste strictement positif si `κ>0`. Aucun supplément d’analyticité n’est requis pour ce transfert.

## Récurrence générale de la série vérifiée

[V14SeriesRecurrence.lean](LeanMath/Papers/V14SeriesRecurrence.lean) définit `oddCoefficient p n = a_(2n+1)` à partir de la série formelle exacte, puis prouve :

- l’équation différentielle formelle `(1−y²) F′ = (1/p)(1−F²)` ;
- `a₁=1/p` et, pour tout entier `n≥1`, `(2n+1)a_(2n+1) = (2n−1)a_(2n−1) − (1/p) Σ_(k=0)^(n−1) a_(2k+1)a_(2(n−1−k)+1)` ;
- la convergence de la série impaire vers `tanh(artanh(y)/p)` dans un voisinage de zéro ;
- les expressions imprimées de `a₃` et `a₅`, pour `p≠0`.

La récurrence découle des séries binomiales et de leurs dérivées formelles; elle n’est pas une hypothèse ajoutée. Le résultat analytique exporté est local : il ne prétend pas établir ici le rayon maximal de convergence.

## État des obligations recensées

La récurrence ferme la dernière obligation mathématique complémentaire de cette concordance. Il ne reste aucun point ouvert dans cette liste. Ce constat porte sur les énoncés et compléments recensés, et ne constitue pas une vérification automatique de chaque phrase ou donnée du PDF.

Les mesures de temps, sorties de corpus et illustrations numériques demeurent des données expérimentales. Cette concordance n’est pas une vérification de l’exécutable C++ ni de son arithmétique flottante.
