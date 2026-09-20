# V22 → V23 : réponse aux recommandations

La révision traite les quatre obstacles du rapport de lecture. Elle vise un manuscrit plus solide et plus clair, sans s'attribuer une note de 95/100 ni garantir une décision éditoriale.

| Recommandation | Modification concrète |
|---|---|
| Faire ressortir le théorème principal | Résumé et introduction centrés sur trois résultats : cercle inverse d'ordre cinq, arc décentré global d'ordre cinq, réalisations et coût explicite. Les deux dynamiques sont opposées dès le début : alternance pour le cercle, monotonie pour l'arc. |
| Positionner l'originalité construction par construction | Nouvelle section dédiée et tableau d'attribution. AK, AD, projectif et Padé rationnel sont explicitement identifiés aux formules classiques. Les deux équations quadratiques sont exposées et la comparaison avec Shafer est délimitée. Les méthodes antérieures à cercle osculateur sont intégrées. Un registre des sources distingue texte intégral, formules consultées, résumé éditeur et références bibliographiques. |
| Alléger l'argument analogique | Retrait de l'analogique du titre secondaire, du résumé et de la conclusion principale. Les détails de puissance binaire et le prototype comportemental restent en annexe, avec leur provenance et leurs limites. Aucune performance du cercle électronique n'est inventée. |
| Remplacer la preuve technique par degré | Nouvelle preuve uniforme utilisant x=(v−1)/(v+1), y=3px/[3+(p²−1)x²], y>px/2 et la convexité stricte de artanh. Elle donne directement la contraction sur toute la branche et l'inégalité aux extrémités pour tout réel p>2. Plus de tableau p=3,…,9 ni de borne 3.46p−1≤r≤3.47p dans la preuve principale. |
| Renforcer la lecture comparative | Les trois coefficients d'ordre cinq sont donnés dans la même variable d'erreur. Une vérification symbolique indépendante les retrouve par séries exactes, établissant la non-identité avec le Padé rationnel nommé. |

## Théorème 4.3 formalisé en Lean

La preuve uniforme étend le paramètre du théorème scalaire à tous les réels p>2 et montre que chaque étape du cercle traverse la racine sur la branche sélectionnée. Le résultat est désormais démontré dans le texte et formalisé en Lean. Les 25 contrôles symboliques, 240 cas de branche et 72 trajectoires à 400 chiffres servent de vérification complémentaire.

Trois nouveaux modules formalisent l'inégalité uniforme, l'alternance, l'existence et l'unicité de la branche inverse, sa continuité, les bornes explicites de la bande, la convergence de toute orbite et l'ordre cinq dans la variable d'erreur réellement itérée. Le lien avec la mise à jour multiplicative et la racine X^(−1/p) est également vérifié. Un audit couvre leurs 69 déclarations, sans `sorry` ni axiome supplémentaire. Le module antérieur à degré entier conserve ses 33 déclarations auditées ; le contrôleur à porte résiduelle conserve son audit indépendant de 41 déclarations. Le [tableau de correspondance](LEAN_THEOREM_4_3.md) donne les noms exacts.

## Conservation du contenu

Les cinq dessins Pandrosion (MA, AK, AD, projectif et décentré), le cercle fixe, le pli inverse, le graphe de contraction, le contrôleur, la puissance binaire et le circuit sont conservés. Le tableau précision/coût inclut désormais les 12 joins d'initialisation directement dans les totaux des deux contrôleurs, au lieu de demander au lecteur de les ajouter. Les campagnes de reproduction restent accessibles. Les fichiers de la v22 et les modifications préexistantes du site restent préservés.

## Limites de la cible 95+

Une recherche ciblée permet d'identifier les relations exactes avec les références consultées ; elle ne prouve pas une priorité universelle. La note finale dépend d'une évaluation extérieure. V23 retire les ambiguïtés évitables et apporte une preuve plus courte, tout en conservant la distinction entre théorèmes écrits, Lean, contrôles numériques et résultats électriques.
