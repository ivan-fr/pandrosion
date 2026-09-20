# V24 → V25 : faciliter la première lecture

Cette révision répond aux quatre remarques éditoriales sans ajouter de méthode ni modifier une preuve Lean.

| Remarque | Modification |
|---|---|
| Trois pages de positionnement avant la première construction | L'exemple du cercle à huit joins devient la section 2, avec la notation nécessaire donnée sur place. La section 3 explique les rails et la section 4 développe la preuve. Le positionnement général vient après les coûts, en section 7 ; l'ancienne section 2.3 devient l'annexe F. |
| Conclusion trop brève et questions ouvertes absentes | Conclusion autonome en deux paragraphes, suivie de quatre questions précises : borne inférieure du coût, conditionnement et charts, équivalences dans les familles algébriques, formalisation des calculateurs complets. L'expérience électrique proposée reste une question distincte. La contraction sur toute la branche, désormais prouvée, n'est pas présentée comme ouverte. |
| Coût initial ambigu dans l'ancien tableau 3 | La légende du tableau de précision/coût (désormais tableau 2) précise que les trois premières lignes cumulent les coûts par étape, puissance incluse, sans charge initiale distincte ; les deux contrôleurs incluent 12 joins pour le cache résiduel initial. Préparation fixe et inversion finale sont exclues partout. Aucune valeur n'est modifiée. |
| Capitales bibliographiques perdues | Protection BibTeX de Halley, Euler, Book III et Padé ; contrôle du texte effectivement produit dans le PDF. |

Le résumé, les 11 figures, les énoncés et preuves mathématiques restent conservés. Le théorème principal garde son numéro 4.3 ; le théorème de l'arc reste 5.1. La proposition de switching passe de 7.1 à 8.1, avec les guides mis à jour. Les arguments d'équivalence de la v24 sont conservés intégralement en annexe F et dans POSITIONING.md.

Le correctif CI précédent ajoute trois tentatives limitées au téléchargement du cache mathlib. Son exécution complète au commit `61b169908b1e48a3c66637d5568a8fbae89aef69` est passée, y compris Lean et tous les audits : [run 35500502121](https://github.com/ivan-fr/pandrosion/actions/runs/35500502121). Les échecs réseau initiaux ne provenaient pas d'une preuve.
