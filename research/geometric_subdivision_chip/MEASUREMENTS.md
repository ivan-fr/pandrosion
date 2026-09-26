# Mesures comparatives exécutées

Même couple (p, X). V30 et P6 : macromodèles calibrés, pas des circuits transistor. Nouvelle chaîne : modèle BJT générique, n=6, sans correction des moyennes. Les niveaux de fidélité diffèrent ; ce tableau ne classe pas les énergies.

| p | X | V30, 4,785 ms (ppm) | P6, 180 µs / 16 lectures (ppm) | Nouvelle chaîne BJT (ppm) |
|---:|---:|---:|---:|---:|
| 3 | 2 | 0.212547 | 1.33263 | 14032.3 |
| 3 | 500000 | 0.354259 | 1.28431 | 9430.51 |
| 7 | 2 | 0.0764635 | 0.602881 | 12508.6 |
| 7 | 500000 | 0.120273 | 0.404266 | 12863.3 |
| 32 | 2 | 0.0169137 | 0.135866 | 6045.64 |
| 32 | 500000 | 0.0204397 | 0.089267 | 7613.66 |
| 1e+06 | 2 | 1.239e-06 | 0.00933493 | 8836.09 |
| 1e+06 | 500000 | 1.16245e-06 | 0.00343597 | 8448.21 |

Les huit paires sont un contrôle commun, pas un nouvel échantillonnage représentatif. Les étalonnages électriques et ADC sont recalculés une fois par p à 25 °C, puis partagés entre les deux macromodèles. Les deux échecs P6 à 1 ppm de ce protocole sont conservés. Les performances des campagnes P6 historiques à 64 cas restent des résultats de leurs propres protocoles.

## Profondeur, X=2 et p=3,7

| n | Erreur mathématique | Erreur BJT |
|---:|---:|---:|
| 1 | 9.732351e-06 | 0.01005463 |
| 2 | 6.955815e-08 | 0.0004053391 |
| 4 | 2.39498e-10 | 0.0008257901 |
| 6 | 2.194054e-13 | 0.009855879 |

Les balayages n=1 et n=2 à X=500000 sortent de la plage visée des courants intermédiaires ; ils sont des diagnostics de saturation, pas des candidats retenus.

## Sources numériques

- [Campagne transistor](results/transistor.json) : 118 essais, dont quatre délais de solveur au démarrage.
- [Calibration mesurée](results/calibration.json) : références rationnelles ; gains et offsets gelés.
- [V30/P6](results/comparison.json) : sorties, trajectoires et coefficients de calibration.
- [Primitives communes](results/matched.json) : 32 simulations, charge et erreurs identiques par primitive. Le profil « ideal » signifie gain/offset nuls ; les pertes résistives restent présentes.
- [Contrôles P5/P6 à transistors](results/controls.json) : 12 simulations. Modèles et I₀ alignés, terminaisons de sortie historiques conservées.
- [Bruit petit signal](results/noise.json), [interfaces](results/interface.json), [démarrages avec rampes](results/ramped.json), [contrôles](results/checks.json).
