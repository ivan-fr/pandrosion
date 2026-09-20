# V23 → V24 : réponse au dernier rapport

La v24 traite le dernier point substantiel du rapport : le statut de l'arc décentré sous changement de coordonnées. Elle ne rajoute aucune méthode, ne modifie pas le résumé, et conserve les preuves et constructions de la v23.

| Demande du rapport | Réponse concrète |
|---|---|
| Préciser « distinct à homographie/conjugaison près » | Nouvelle section 2.3 distinguant identité, transformations homographiques et conjugaison analytique locale. Le complément [POSITIONING.md](POSITIONING.md) donne les démonstrations et leurs domaines. |
| Ne pas surinterpréter les coefficients d'erreur | Leur différence établit seulement la non-identité dans la même variable. Par Böttcher, arc et Padé rationnel sont bien conjugués analytiquement près de la racine pour tout réel p>2. |
| Examiner une normalisation quadratique précise | Le polynôme primitif de l'arc a un contact exactement six avec t^(−1/p), alors que le type diagonal (2,2,2) de Hermite–Padé/Shafer impose au moins huit. La convention est vérifiée dans le rapport original Cabay–Labahn de 1989. |
| Examiner les homographies | L'arc est non rationnel dans t pour tout réel p>2. Pour les degrés entiers p≥3, le solveur complet est non rationnel en x, ce qui exclut sa conjugaison homographique avec un solveur rationnel. La restriction aux entiers est explicite. |
| Conserver une contribution robuste | L'objet revendiqué reste la réalisation géométrique, la branche, la convergence et le coût du protocole. Ni nouvelle classe de conjugaison locale ni priorité historique universelle ne sont revendiquées. |
| Maintenir la traçabilité | 18 nouveaux contrôles symboliques et 10 exemples entiers de régression, ajoutés au vérificateur et à CI. Deux références primaires et le registre d'accès complètent le positionnement. |

Les 69 déclarations Lean du théorème 4.3 et leur audit restent inchangés. Les nouveaux arguments de positionnement sont écrits et contrôlés algébriquement ; ils ne sont pas présentés comme formalisés en Lean. La preuve globale de l'arc et le switching branch-driven conservent leurs limites explicites de formalisation.

La v23 reste archivée. Aucune note de 95/100 ni décision de publication n'est garantie : le rapport appelle encore une expertise spécialisée de la littérature des méthodes algébriques.
