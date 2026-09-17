# Pandrosion report supports and the decentered AD arc

The V19 supplement retains four actual rectangle constructions: AK (order 2), centered-arc AD (order 3), projective AD (order 4), and decentered-arc AD (order 5). The projective name [2/1] uses the direct state z=1/s; its reciprocal-state correction is [1/2].

`verify.py` constructs the triangle chain, support and final point by intersections. It checks 108 configurations for each of the four methods, at 160 digits, and exact symbolic certificates for the decentered-arc method. It also produces the common-start accuracy table at 280 digits. `figures.py` draws the actual geometry, including the distant center and a report-detail inset for the decentered arc. Run both with the packages from the root requirements file.

For t=Xs^p, set q²=((p-2)(t²+1)+(10p+4)t)/(12p), g=(p-1)q. The update is s(1+g)/(t+g). The paper proves global monotone convergence for every real p>2 and every positive start, and exact local logarithmic coefficient (p-2)(p²-1)(3p+1)/1440. It is 1/18 at p=3, 13/48 at p=4, 4/5 at p=5, and 11/3 at p=7. This is a different map from the inverse-Padé fixed-circle method.

For geometric preparation (integer p≥3), use beta=(p-1)sqrt((p-2)/(12p)), alpha=(5p+2)/(p-2), d=W/beta and delta=(H/X)sqrt(alpha²-1). Prepare G=(W,H+H alpha/X), F=(W-d+delta,H-H/(X beta)) and the vertical x=W-d. The arc with center F and radius EG has lower intersection D with that vertical. Draw AD and use the common parallel report. The radius is a constructed length. No unknown root is used to locate any point.

The support costs one mobile arc and one join, exactly as centered AD; this excludes the triangle chain, report parallels and fixed preparation. With identical expansion of each parallel into two joins and three arcs, the generic first-step total is 10p+9 traces and a reused-horizontal subsequent step costs 10p+4. Centered and decentered AD have different fixed setups. These are stated protocol counts, not geometric optimality or timing claims.

`LeanMath/Papers/RectangleDecenteredArc.lean` supplies ten compiled algebraic certificates, included in the 149-declaration combined geometry audit. The full written analytic proof of global convergence is not yet a Lean theorem. See CLAIM_COVERAGE.md in the paper package for exact boundaries.
