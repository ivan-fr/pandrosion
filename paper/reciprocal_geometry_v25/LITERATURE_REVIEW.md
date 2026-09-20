# V25 (sources retained from V24): construction-specific literature review

Reviewed on 20 September 2026. This is a bounded comparison, not a proof of historical priority. No absence claim is inferred from a title, abstract, inaccessible full text or unsuccessful search.

## Sources and actual access

| Source | Material consulted | Supported use in V25 |
|---|---|---|
| [Traub, 1961](https://doi.org/10.1145/366573.366606) | Original paper, pp. 276–278, [CMU archive scan](https://iiif.library.cmu.edu/file/Traub_box00027_fld00008_bdl0001_doc0001/Traub_box00027_fld00008_bdl0001_doc0001.pdf). | High-order iteration and rational approximation of Euler's formula are classical. The historical introduction explicitly corrects earlier misattributions of root iterations. |
| [Gander, 1985](https://doi.org/10.2307/2322644) | Original article, pp. 131–134, [scan](https://scee86bccd27a6ab2.jimcontent.com/download/version/1644234825/module/14376416278/name/On%20Halley%27s%20Iteration%20Method.pdf); publisher metadata cross-checked. | Rational Halley and radical Euler arise from quadratic approximation; the radical uses the exact quadratic root. No claim that solving a quadratic is new. |
| [Scavo–Thoo, 1995](https://doi.org/10.2307/2975033) | Bibliographic record and cross-references in the primary Melman/Amat literature. The full paper was not obtained during this revision. | General prior geometric treatment of Halley only; no theorem-by-theorem exclusion claim. |
| [Melman, 1997](https://epubs.siam.org/doi/10.1137/S0036144595301140) | SIAM publisher abstract, metadata and references. Full text not obtained. | Prior connection between geometric interpretation and global convergence for Euler and Halley. No transferred hypotheses or new global theorem attributed from the abstract. |
| [Amat–Busquier–Gutiérrez, 2003](https://www.sciencedirect.com/science/article/pii/S0377042703004205) | Publisher abstract and metadata. | Prior geometric constructions of scalar iterative methods. |
| [Kanwar–Singh–Bakshi, 2008](https://link.springer.com/article/10.1007/s11075-007-9149-4) | Springer publisher abstract and metadata. | The authors explicitly include osculating-circle and ellipse methods in their quadratic/cubic families. V24 does not infer absence of a particular construction from the abstract. |
| [Laszkiewicz–Ziętak, 2009](https://onlinelibrary.wiley.com/doi/abs/10.1002/nla.656) | Publisher metadata, plus [authors' GAMM presentation](https://cs.pwr.edu.pl/zietak/talks/GAMM_2009.pdf), especially PDF page 11. | Exact printed formulas h11, h12 and h22 identify centered AD, projective AD and the rational fifth-order comparator after x=s/a, t=x^p. |
| [Karp–Lin, 2011](https://arxiv.org/abs/1102.3957) | [Full author preprint](https://arxiv.org/pdf/1102.3957), equations (1.1)–(1.2), formula preceding Theorem 2.4 and convergence discussion. | Rational Padé convergence is prior work. The fourth-power differential defect is a classical Padé feature; its explicit polynomial specialization in V24 is verified algebraically. Karp–Lin's rational-iteration convergence hypotheses are not asserted to prove V24's inverse-branch theorem. |
| [Shafer, 1974](https://epubs.siam.org/doi/10.1137/0711037) | SIAM publisher abstract, metadata and references. Full text not obtained. | Quadratic approximation as an alternative to rational Padé with square-root evaluation is classical. V24 derives its own implicit quadratic equations; The diagonal (2,2,2) contact convention is now checked against Cabay–Labahn's full primary report, not attributed to an unread portion of Shafer. |
| [Pakdemirli, 2025](https://avesis.mcbu.edu.tr/yayin/3d95199c-1515-4b22-a182-0e86fa457b82/non-divergent-circular-arc-root-algorithm) | Author's institutional publication record and abstract; the paper's accessible text was also located. | A recent tangent-circle root algorithm uses local curvature. V24 compares that construction mechanism with a prepared fixed circle and a fixed-center, residual-radius arc. No broad priority exclusion or benchmark against CARA is claimed. |
| [Cabay–Labahn, 1989](https://cs.uwaterloo.ca/research/tr/1989/CS-89-09.pdf) | Full institutional scan downloaded; title and printed pages 1–2 visually inspected (PDF pages 4–6). Equations (1.4)–(1.6) give the contact convention and page 2 relates quadratic forms to Shafer. | Type (2,2,2) requires implicit residual order at least eight. Our exact substitution has order six; irreducibility and primitivity exclude an alternative polynomial with those degree bounds for this branch. No exclusion of all quadratic families. |
| [Buff–Epstein–Koch, 2011](https://arxiv.org/abs/1104.2981) | [Full author PDF](https://people.math.harvard.edu/~kochs/bottcher.pdf), Introduction, page 1, classical one-variable theorem. | An analytic superattracting germ is locally conjugate to its leading monomial. Applying this classical result to our maps proves local analytic equivalence of arc and rational Padé; the reality and sign arguments are written out in POSITIONING.md. No global or cost-preserving conjugacy is inferred. |

Historical geometry, Pappus, software and companion references are retained from V22; they are not represented as newly verified full-text literature reviews. No new publication date was substituted for the original journal year merely because a publisher digitized the article later.

## Exact comparisons made here

1. For x=s/a and t=x^p, the three rational baselines are the printed h11, h12 and h22. The projective correction is [1/2] in the reciprocal-state variable, and [2/1] after inversion to the direct-root state.
2. The circle solves `(gamma-t*alpha)*v^2 + 2*beta*(t-1)*v + (alpha-t*gamma)=0`. Approximating the inverse relation and then inverting it is different from directly evaluating h22.
3. The arc correction eliminates to `(p-1)^2*S(t)*(v-1)^2 - 12*p*(t*v-1)^2 = 0`. This squared equation does not preserve branch signs and is singular at t=1. The positive-radical formula defines the map.
4. The order-five coefficients in the common error e=log(s/a) differ. The uniform verifier derives their series with exact rational coefficients; it does not merely evaluate the displayed coefficient formulas.
5. The arc is nonrational in the correction variable for every real p>2. For integer p≥3, the complete state map is nonrational too, which excludes Möbius conjugacy to a rational map. These are proved algebraic distinctions, not inferred from unequal error constants.
6. The primitive arc quadratic has residual contact six with t^(−1/p), excluding the specific diagonal quadratic type (2,2,2) normalization requiring eight. General homographic classification against nonrational methods remains open.
7. Local analytic conjugacy does exist between arc and rational Padé for every real p>2, by Böttcher coordinates and a real scaling. This does not identify finite construction protocols or global domains.
8. The explicit circle protocol, selected branch and mobile work are the constructive object under evaluation. A fixed-circle existence theorem does not specify that protocol or prove it optimal.

## Search boundary

Searches included the exact works named in the reading report (Gander, Scavo–Thoo, Shafer, Traub and Padé root iterations), then geometric nonlinear iteration, osculating circles, fifth-order radical/irrational corrections, inverse Padé root solvers and recent circular-arc root algorithms. V24 additionally checked quadratic Hermite–Padé contact conventions and the classical local conjugacy theorem. The mathematical exclusions are limited to the stated coordinate classes; generic searches for radical methods were not used to claim absence. Primary papers, author/institutional sources and publishers were used for the manuscript claims. Generic search hits were used only to locate those sources.

The review establishes explicit relationships and nonidentity with the named rational baseline. It does **not** establish that no equivalent algebraic or geometric realization exists elsewhere. No 95/100 score or reviewer acceptance is claimed.

## V25 editorial treatment

The access record and substantive comparisons above are retained from V24; no new literature search is claimed. The general comparison is now Section 7 and the technical equivalence argument is Appendix F. Proper names and Book III are protected against BibTeX sentence-case conversion.
