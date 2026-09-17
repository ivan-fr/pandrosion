# V17 — From Proportional Rectangles to Sampled Analog Root Computation

Article de recherche autonome en anglais, 17 septembre 2026, auteur : Ivan Besevic. Les versions antérieures ne sont pas remplacées.

## Livrables

- `Pandrosion_Geometry_Analog_V17.pdf` : article compilé depuis LaTeX.
- `main.tex`, `references.bib`, `build.sh` : sources et compilation.
- `figures/` : sept figures en PDF vectoriel, avec aperçus PNG.
- `data/` : benchmarks numériques et SPICE, résultats antérieurs utilisés, tableaux LaTeX.
- `formal/` : 18 modules Lean locaux nécessaires, versions verrouillées, audit de 88 théorèmes et log de reconstruction.
- `analog_p2/`, `analog_p3/`, `analog_p4/` : scripts, netlists, résultats et notes des étapes analogiques citées.
- `scripts/` : reproduction des figures, tableaux, coûts géométriques et mesures de temps.

## Portée

La construction et la dynamique exactes concernent p entier ≥2. Les circuits simulés concernent p=3 et une entrée normalisée m∈[1,2]. Les modèles de composants sont simplifiés et ne sont ni des macromodèles fabricants ni un PDK. Aucune fabrication, mesure sur silicium, performance énergétique ou priorité historique n'est revendiquée.

L'audit Lean frais confirme l'absence de `sorryAx` et d'axiomes personnalisés dans les dépendances des 88 déclarations contrôlées. Il ne certifie pas le manuscrit entier, les coûts, les scripts ou les circuits.

## Compiler le papier

Depuis ce dossier :

```sh
bash build.sh
```

Le script utilise Tectonic s'il est disponible, sinon latexmk. Les figures et données déjà fournies suffisent à compiler le PDF. Les données de timing peuvent changer à chaque nouvelle mesure ; les fichiers livrés conservent les mesures de rédaction.

## Reproduire les expériences

Python avec numpy, matplotlib et mpmath, ainsi que ngspice accessible dans PATH :

```sh
python scripts/benchmark.py
python scripts/geometric_cost.py
python scripts/bench_spice.py
python scripts/tables.py
python scripts/figures.py
```

Le microbenchmark Python comporte neuf rounds mélangés, 100 résolutions par combinaison degré/méthode, à 140 chiffres de travail. Le test d'arrêt des itérations utilise une référence préalablement calculée ; la routine `mpmath.root` calcule à pleine précision. Les timings ne comparent pas des implémentations optimisées en langage compilé.

Les 14 chronométrages ngspice mesurent le temps hôte (lancement, résolution, écriture), distinct des 650 µs de temps simulé.

Pour la suite P4 :

```sh
cd analog_p4
python simulate_p4.py
python verify_p4.py
```

40 essais principaux plus 5 contrôles : 3 RC et 2 raffinements du pas temporel. Les anciens `.cir` doivent être exécutés dans des répertoires séparés, car ils écrivent `waveform.txt`. P2/P3 ont leurs propres README de reproduction. Les publications et figures de ces étapes conservent leur langue française ; l'article fournit les figures en anglais.

Après de nouveaux essais, les tableaux analogiques du manuscrit, actuellement fixés aux résultats livrés, doivent être relus et mis à jour si les modèles changent. Le script `tables.py` actualise automatiquement les deux tableaux de timing seulement.

## Reproduire l'audit Lean

Installer elan/Lean, puis depuis `formal/` :

```sh
lake exe cache get
lake build LeanMath
lake env lean Audit.lean
```

Le fichier `lean-toolchain` verrouille Lean 4.33.1 ; `lake-manifest.json` verrouille mathlib et ses dépendances. La source snapshot contient uniquement la fermeture transitive locale nécessaire au certificat. `audit_summary.json` donne les empreintes et la portée.

## Contrôle documentaire

`CHECKS.json` décrit les vérifications finales. `SHA256SUMS` permet de vérifier les fichiers livrés. Les sources des données, les hypothèses et les limites figurent dans le texte. Le papier est préparé comme préprint ; il n'a pas été soumis ni publié automatiquement.
