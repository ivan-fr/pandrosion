# Relecture intégrale de la V19

Le manuscrit conserve 18 pages, huit figures et le tableau comparatif des sept méthodes en première page.

## Corrections de fond et de précision

- Initialisation dyadique : la quantité affichée est désormais explicitement une borne sur le rayon de Cayley, avec L fixé dans l'estimation asymptotique. La récurrence constructive et son état initial sont donnés.
- Stéréographie : les coordonnées homogènes sont non nulles; une droite affine omet le pôle Nord, tandis que sa complétion l'inclut. Les hypothèses sur les droites et cercles et la réciproque des équations de lieu sont précisées.
- Erreurs numériques : les valeurs non signées des tableaux sont désignées comme erreurs relatives absolues. Les constantes d'erreur locales gardent leur signe.
- Cercle fixe : la branche peut être marquée pendant la préparation par ses extrémités et G(1). Les coordonnées rationnelles des centres sont distinguées des marqueurs de branche, qui peuvent exiger des racines carrées.
- Convergence : le déplacement de AK vers le point fixe et la positivité de la limite de l'arc décentré sont explicités. Les conclusions locales et globales restent séparées.

## Rédaction et progression

Le résumé est raccourci. L'introduction annonce le parcours : quatre corrections dans le rectangle, remplacement des parallèles par les pinceaux, inversion quadratique au cercle fixe, puis représentation sur la sphère. Les transitions expliquent le rôle de chaque nouvelle construction. L'anglicisme « report » est remplacé dans la prose par « correction ». Les notations distinguent la hauteur H des fonctions d'erreur, le polynôme de préparation Lambda_p de la borne L_p, et le centre M de la correction rationnelle P. Les abréviations A/B/C des figures sont expliquées. La bibliographie ne contient plus que les neuf entrées citées, sans doublon Launay.

## Vérifications réalisées

- Identités symboliques générales des quatre corrections rationnelles : dérivées, contacts de Padé et constantes d'ordre; convention directe [2/1] et réciproque [1/2].
- Identités du modèle quadratique inverse et coefficient cubique du centre bilatéral.
- Nouvelle exécution de 162 constructions au cercle fixe à 250 chiffres.
- Nouvelle exécution de 108 configurations pour chacune des quatre corrections du rectangle, soit 432 constructions à 160 chiffres.
- Nouvelle exécution des 75 configurations sphériques régulières et des trois cas à l'infini.
- Nouvelle exécution des audits Lean : 149 déclarations géométriques et algébriques, plus 11 résultats de contexte; seuls propext, Classical.choice et Quot.sound apparaissent, sans sorryAx.
- Reconstruction du PDF, contrôle des renvois et inspection visuelle des 18 pages et des huit figures. Tableau complet vérifié en page 1.
- Contrôle des sources locales de la distribution, des empreintes et de l'intégrité de l'archive.

Les nouveaux contrôles algébriques reproductibles sont dans `src/review/check_math.py`; leurs résultats figurent dans `data/review_math_checks.json`. Les journaux sont dans `verification/`.

## Portée

La relecture n'a pas révélé de contradiction supplémentaire dans les résultats examinés. Elle ne constitue pas une preuve d'absence absolue d'erreur ni une revue d'antériorité exhaustive. Le manuscrit conserve ses limites explicites : la convergence globale de l'arc décentré est une preuve analytique écrite, soutenue par dix certificats algébriques Lean; la convergence du cercle fixe n'est démontrée que localement. Les coûts concernent les protocoles décrits et non leur optimalité.
