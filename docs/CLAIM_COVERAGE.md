# Correspondance avec les énoncés des PDF

Ce tableau suit les énoncés des fichiers reçus, dont les empreintes figurent dans
`FORMALIZATION.md`. Il ne remplace pas les signatures Lean enregistrées dans
`validation/declarations.txt`. « Partiel » signifie que des parties de l’énoncé
ou des conclusions annoncées ne sont pas encore prouvées. Aucun résultat ouvert
n’est admis comme axiome.

## Reciprocal Geometry

| Énoncé | État | Certificat ou limite |
| --- | --- | --- |
| 2.1 — point fixe et lecture | Vérifié | `Raw.lean` |
| 2.2 — convergence brute | Vérifié | `RawConvergence.lean`, sous les hypothèses `x > 1`, degré entier ≥ 2 |
| 4.1 — encadrement | Vérifié | `Bracket.lean` ; extension réelle dans `RealBracket.lean` |
| 5.1 — phase dyadique | Partiel | Contraction, arrondi et entrée finie vérifiés ; caractérisation « facteur nul ssi puissance de deux » ouverte |
| 5.2 — côté de la racine, centre | Vérifié | `Bilateral.lean`, exactitude à 2 incluse |
| 5.3 — cellule du centre | Partiel | Cellule `1 < R ≤ 1+1/√p` vérifiée ; formule de la cellule maximale ouverte |
| 5.4 — globalité à 2 et 3 | Vérifié | `Bilateral.lean`, `BilateralRange.lean`, `BilateralHybrid.lean` |
| 5.5 — couplage dyadique/centre | Vérifié | `BilateralHybrid.lean`, `GuardedCenter.lean`, cellule du papier et degrés entiers ≥ 2 |
| 6.1 — identification de Halley | Vérifié | `Cayley.lean` |
| 6.2 — réciprocité | Vérifié | `Cayley.lean`, `Family.lean` |
| 6.3 — comparaison Cayley | Vérifié | `Comparison.lean`, `Family.lean`, degrés réels > 1 |
| §6 — ordres exacts 3, 5, 7 | Vérifié | `CayleyCubic.lean`, `CayleyQuintic.lean`, `CayleyLocal.lean` |
| 6.5 — convergence Cayley | Vérifié | `CayleyConvergence.lean`, `Family.lean` |
| 7.1 — certificat indépendant | Vérifié | `Bracket.lean` |
| 7.2 — raffinement complet | Vérifié hors R=1 | `CrossBracket.lean` : chaînes strictes pour les trois noyaux, extension à tout réel p≥2 |
| 7.3 — intervalle strictement raffiné | Vérifié hors R=1 | `CrossBracket.lean` : racine contenue et inclusion stricte des intervalles |
| 7.4 — raffinement bilatéral | Vérifié | `StrictBracket.lean` : centre strictement intérieur ; côté de la racine dans `Bilateral.lean`, identité de demi-largeur dans `RealBracket.lean` |
| 7.5 — centre à p=3 | Vérifié | `Bilateral.lean`, `RealCorrections.lean` |
| 7.6 — ordre des deux raffinements | Comparaison principale vérifiée | `RefinementOrdering.lean` : centre < Halley si p>3 et R>1, ordre inverse si 1<p<3 ; égalité à 3 et réciprocités déjà vérifiées ; chaîne réciproque complète non regroupée en un théorème |
| 7.7 — comparaison des largeurs | Rapports vérifiés | `WidthComparison.lean` : pour tout R>0 non unitaire, Γ<1/2 si p≥3, Γ>1/2 si p=2 ; 0<Γ<1 pour p≥2 ; formulation équivalente en inclusions entre raffinements non regroupée |
| 7.8 — loi locale de demi-largeur | Vérifié | `WidthLocal.width_ratio_limit` : limite bilatérale Γ→1/2 pour tout réel p>1 |
| 8.1 — degrés réels | Vérifié pour p>1 | `RealBracket.lean` ; cas p=1 exact séparément dans `RealCorrections.lean` |
| 8.2 — Cayley réel | Corrigé / partiel | Régime p>1 vérifié ; contre-exemple formel à la comparaison uniforme pour 0<p<1 |
| 8.3 — dichotomie réelle | Version corrigée vérifiée | Remplacer 1≤p<2 par 1<p<2 ; `BilateralRange.lean` et `RefinementOrdering.lean` donnent les comparaisons avec la racine et Halley |
| 8.4 — largeurs réelles | Réfuté tel qu’imprimé / partiel | `WidthComparison.lean` remplace l’égalité à p=3 par Γ<1/2 pour tout résidu positif non unitaire ; classification des autres degrés réels entre 1 et 3 ouverte |
| 8.5 — degrés dyadiques algébriques | Ouvert | Formules de racines carrées imbriquées non formalisées |
| 11.1–11.6 — théorie complexe | Ouvert | Les preuves scalaires réelles ne certifient pas ces résultats |
| 11.7 — matrices | Corrigé / ouvert | Rationalité uniforme réfutée dans `Corrections.lean` ; convergence matricielle non formalisée |
| 11.8 — préservation de structure | Ouvert | Non formalisé |
| Annexe A — résidu polynomial de P5 | Vérifié | `Cayley.lean`, factorisation et signe pour p>1 |

## Beyond Monomials

| Énoncé | État | Certificat ou limite |
| --- | --- | --- |
| 2.1 — famille exponentielle | Partiel | Analyticité, cumulants à tous les ordres, variance, convexité et monotonie stricte vérifiés pour mesures générales bornées ; limites de la moyenne restantes |
| 2.2 — structure des branches | Partiel | Unicité/existence en support positif, monotonie des branches et absence de trois racines vérifiées ; classification complète du support signé restante |
| 3.1 — identité du résidu | Vérifié | `ExponentialFamily.lean`, mesure finie arbitraire ; test de côté sur branche choisie dans `BranchStructure.lean` |
| 4.1 — pente sécante | Ouvert | La convexité est vérifiée, mais l’énoncé complet avec prolongement et limites n’est pas livré |
| 4.2 — enveloppe « optimale » | Encadrements corrigés vérifiés | Optimalité imprimée réfutée ; borne β améliorée pour h>0 dans `ExtremalBracket.lean` ; z≤h/μ et, si m>0, h/m≤z pour h<0 dans `NegativeBracket.lean` |
| 4.3–4.4 — conséquences d’encadrement | Partiel | Les encadrements de base et la borne corrigée sont vérifiés ; toutes les formulations imprimées ne le sont pas |
| 5.1 — deux membres globaux | Vérifié sur la branche croissante non dégénérée | `BranchConvergence.lean` : convergence globale sous les hypothèses de branche déclarées ; `NewtonLocal.lean` : coefficients et positivité ; `BranchTaylor.lean` : restes O(e²) et O(e³). Cas monomial normalisé exact en un pas également vérifié |
| 5.2 — ordre sept cumulant | Vérifié pour le noyau défini, à moyenne non nulle | `CumulantCoefficient.lean` : coefficient universel explicite, limite normalisée, reste O(e⁸) et ordre exact sept si N₇≠0 ; cumulants recalculés à chaque itéré. Cas monomial exact dans `AnalyticReversion.lean` |
| 6.1 — réciprocité et monômes | Vérifié | `MonomialBoundary.lean`, produit ≥1 et cas d’égalité |
| 6.2 — réflexion | Identités vérifiées | `Reflection.lean`, fonction génératrice et dérivées de tous ordres |
| 7.1 et algorithme 1 | Variante certifiée / énoncé imprimé partiel | `GuardedBracket.lean` et `GuardedCumulantSolver.lean` : noyau, garde centrale, secours, initialisation, convergence et arrêt certifiés. Cette variante ne prouve pas l’acceptation définitive ni l’ordre sept de l’algorithme imprimé ; voir `SOLVER.md` |
| 9.1 — cas monomial | Vérifié pour les noyaux définis et les lois de probabilité | Fonction génératrice logarithmique linéaire ; Newton, enveloppe à n=p et noyau cumulant de degré six exacts en un pas pour p≠0 ; famille de tous les ordres non assemblée |
| Annexe A — coefficients de réversion | Vérifié | `SeriesReversion.lean` et `AnalyticReversion.lean` : composition dans les deux sens égale à X jusqu’au degré six ; raccordement analytique à loi fixée |

## Note de recherche

| Énoncé | État | Certificat ou limite |
| --- | --- | --- |
| Proposition 1 — borne β | Vérifié pour support contenu | Existence/unicité, encadrement et extrémités atteintes ; optimalité limite à support exactement imposé restante |
| Lemme 2 — coefficients à tous les ordres | Ouvert | Les coefficients nécessaires aux ordres 3, 5 et 7 sont vérifiés ; cela ne prouve pas la famille entière |
| Théorème 3 — tous les ordres impairs | Partiel | Ordres 3, 5 et 7 vérifiés ; ordres 9 et suivants non formalisés |
| Théorème 4 — contraction en norme | Ouvert | Non formalisé ; aucun transfert implicite des preuves réelles aux matrices |
| §5 — rayon 0,9 et constante 0,403 | Ouvert | La constante rationnelle et les restes analytiques ne sont pas certifiés dans ce dépôt |
| Proposition 5 — erreur matricielle | Ouvert | Non formalisé |
| Proposition 6 — dérivée de Fréchet | Ouvert | Non formalisé |

## Expériences et publication

Les trois PDF contiennent des mesures et des figures qui ne sont pas certifiées
par ce dépôt. Les scripts compagnons n’étaient pas joints. Il faut de nouvelles
expériences avec un protocole explicite avant de republier les tableaux, les
figures de performance ou les temps de calcul. Les énoncés corrigés devront être
reportés dans les sources LaTeX ; aucun PDF original n’a été modifié ici.

## Extension multivariée — 6 septembre 2026

| Énoncé | Statut | Hypothèses et limites |
|---|---|---|
| Loi inclinée et jacobien de moyennes | Vérifié | Coefficients strictement positifs, supports finis ; une loi par ligne |
| Enveloppe convexe des matrices de choix de lignes | Vérifié | Enveloppe extérieure, pas une égalité avec les jacobiennes réalisables |
| Contraction globale du pas de secours | Vérifié | Certificat de norme opérateur sur chaque exposant ; dominance diagonale suffisante |
| Existence et unicité pour toute cible logarithmique | Vérifié | Banach sous le certificat de contraction |
| Sauvegarde et convergence géométrique | Vérifié | Bornes globales résidu/erreur ; contraction vers la solution |
| Acceptation définitive | Vérifié conditionnellement | Borne locale du résidu du candidat d'ordre entier p>1 explicitement supposée |
| Transport en distance de Thompson pondérée | Vérifié | Poids fixes strictement positifs ; certificat pondéré à fournir séparément |
| Réversion tensorielle d'ordre cinq | Preuve sur papier | Formules et contractions mixtes dans la note ; reste non formalisé |
| Extension par enveloppe uniformément inversible / P-matrices | Preuve sur papier | Globalisation Newton amorti ; métrique du résidu, facteur dépendant du sous-niveau initial |
| Performance et arithmétique flottante | Non étudié | Aucun gain de coût mesuré ni certificat numérique ajouté |

Voir [la note et sa portée formelle](research/multivariate_convergence/README.md).

## Étape suivante : enveloppe compacte, signes et ordre trois

| Énoncé | Statut | Hypothèses et limites |
|---|---|---|
| Borne uniforme σ>0 sur famille compacte | Vérifié | Opérateurs injectifs, espace réel de dimension finie non nulle ; preuve sur la sphère unité |
| Compacité et borne pour l'enveloppe posynomiale | Vérifié | Supports finis ; det A≠0 supposé pour toute l'enveloppe ; norme sup dans la spécialisation |
| Borne globale des différences | Vérifié conditionnellement | Représentation par matrices sécantes dans l'enveloppe explicitement supposée |
| Critère de M-matrice | Vérifié | Hors-diagonale non positive : ∃w>0, Aw>0 ssi inversible et inverse non négatif |
| Reste vectoriel de Taylor d'ordre trois | Vérifié | Courbe C³ sur [0,1], borne sur sa troisième dérivée ; constante non optimale 1/2 |
| Correction inverse-Taylor cubique | Vérifié | Correction effective et erreur explicite à partir du reste et de bornes opérateur |
| Spécialisation automatique du noyau cubique aux posynomiales | À raccorder | Dérivées de courbe, uniformité locale des bornes et instanciation de la capture |
| Surjectivité globale et Newton amorti sous enveloppe inversible | Preuve sur papier | Chaîne complète non formalisée ; la compacité et la borne uniforme sont désormais vérifiées |
| Réversion d'ordre cinq | Preuve sur papier | Aucun transfert implicite de la preuve cubique à l'ordre cinq |


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
