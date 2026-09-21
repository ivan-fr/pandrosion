# Binary-power rectangle constructions (post-V20)

This experiment adds four ways to construct the **existing** AK, AD, projective
AD [2/1], and decentered-arc AD maps. It does not introduce new root iterations
or modify the frozen V20 paper or its formal snapshot. Their local orders remain
2, 3, 4, and 5. The gallery has seven V20 protocols and four experimental modes.

## A multiplication by incidences

For W,H>0, use A=(W,H), B=(W,0), the right encoding R(q)=(W,H(1−q)),
the top encoding X(q)=(W+Hq,H), and the fixed unit U×=(W+H,H).
This is the original Lean specialization λ=H. The historical browser uses U×=(3W,H), so at W=2,H=4 both give U×=(6,4); see the parameterized construction below.

1. Copy R(q) onto the top rail using the parallel to U×B through R(q).
   Its intersection with y=H is X(q).
2. Join U× to R(b). Draw its parallel through X(a).
3. Its intersection with x=W is R(ab).

The join has slope b. The parallel has equation y−H=b(x−W−Ha),
so at x=W its ordinate is H(1−ab). This is the similar-triangle multiplication.
The engine obtains each point by homogeneous cross products, not by inserting
`Math.pow` into its coordinates. A scalar power is used only after construction
as an independent readout check.

A multiplication costs one join J and one parallel P. Copying an accumulator
onto the top rail costs one additional P when it will be squared again.
A parallel is a macro, **not an elementary trace**: the gallery retains the
V20 convention P=2J+3C.

## Binary telescope and costs

Start with P=R(s), copy it to X(s), and read the bits of p after its leading 1.
For each bit, square the accumulator; for bit 1, additionally multiply by s
using the retained X(s). Copy the result to the top only if another bit remains.
The final right-rail point E is R(s^p).

For L=floor(log2 p) and h=popcount(p), the number of multiplications is
m=L+h−1. The telescope uses m J and m+L P, including the initial copy.
The unchanged correction support and report add:

| Mode | Additional J | Additional P | Additional C |
|---|---:|---:|---:|
| AKfast | 1 | 2 | 0 |
| ADfast | 2 | 2 | 1 |
| projectiveFast | 3 | 2 | 0 |
| arcFast | 2 | 2 | 1 |

For p=3,5,13,32,1024 the multiplication counts are 2,3,5,5,10.
At p=1024 there are ten squarings, versus 1023 multiplication stages in
the native telescope. Construction objects and incidence operations grow as
O(log p). The original linear protocols retain the degree limit 32;
binary modes accept safe integers from 3 to 1,000,000. These are browser
limits, not mathematical restrictions. The adaptive scoring includes pairwise
comparisons of objects and is consequently O((log p)^2) per binary candidate.

## Spread-fan binary powering

The simple gallery now defaults to **Spread** for the four fast modes. The
explicit **Classic** option keeps the historical single fan and cached upper
copies. The API default remains classic for existing callers and archived
previews: pass `'spread'` as the eighth argument of `construct` to opt in.
The historical browser center is `(3W,H)`, i.e. λ=2W; the original Lean
specialization uses λ=H. Both are instances of the same incidence theorem.

For a prepared offset λ>0, use

```
U_lambda = (W + lambda, H)
X_lambda(a) = (W + lambda*a, H)
R(a) = (W, H*(1-a))
```

Copy R(a) along the parallel to B U_lambda onto the upper rail. Join U_lambda
to R(b), and draw its parallel through the copy. The final right-rail meet is
R(ab): the join's slope is Hb/λ, and the horizontal displacement −λa gives the
vertical displacement −Hab. This works for every λ≠0 when H≠0. `fastCopy` and
`fastMultiply` compute cross products and rail meets; `fastTopPoint` describes
the specification only and is never used to construct a product.

For p≤32, the prepared ratios λ/H are 0.4, 1.2 and 3.5. Higher degrees use
0.4, 0.7, 1.2, 2 and 3.5. Each multiplication constructs all candidate routes
from its already available rail inputs. A deterministic score considers:

- bounding-box width and height, normalized by H;
- the minimum nonzero angle and distinct-point separation inside the module;
- center distance and the number of near-coincidences or small-angle pairs;
- angular separation from earlier multiplication lines, with extra weight on
  the preceding line and a penalty for immediately reusing its bank.

No root oracle participates in this decision. The UI says **“Spread routing:
best among N prepared fan banks.”** The score is a finite engineering heuristic,
not a theorem of optimality or conditioning. Banks can open successive angles,
but cannot guarantee separated marks or avoid every small angle, particularly
near a fixed point or when powers approach the upper rail.

Spread uses one fresh copy per multiplication, so m multiplications cost
**m J + 2m P**, plus the unchanged correction in the table above. This differs
from classic's cached-copy cost m J + (m+L) P. Prepared centers, transfer lines
and certified initialization are setup costs and excluded from both mobile
counts. The gallery's counters count the actual incidences for each layout.
There are still exactly **25 geometric multiplications at p=1,000,000**, versus
999999 linear stages. Routing and its history comparisons take O((log p)^2)
time with a fixed number of banks; the constructed output has O(log p) objects.

`RectangleFastPower.lean` additionally proves `copyLambda_unique`,
`multiplierLambda_transverse`, `joinLambda_distinct`, `geometricMulLambda_R`
and `geometricMulLambda_invariant`. `geometricPowerLambda_eq` allows an arbitrary
nonzero fan at each node of the binary recursion and proves that its final
point is R(s^p). This exact statement covers any finite routing choice. The
existing support-substitution theorems then identify the same four scalar
maps, with the same residual t=Xs^p and the existing convergence results.
The separate audit now checks 31 declarations; the frozen paper audits and
archives are untouched. Neither the JS implementation nor its score is itself
verified by Lean.

## Paper-oriented modular construction

Choose **Full construction**, **Current module**, or **Paper modules** above
the drawing. Full shows the complete route. Current hides other multiplication
strokes in both drawing panes. Paper gives the selected module a full-width
plane and numbered instructions. Previous/next controls and a module selector
navigate each multiplication and then the AK/AD/projective/arc correction
E → P+. Large-degree automatic preparation starts in Current module; Full
remains available explicitly. The two rails and all mathematical coordinates
are retained, and each frame uses one common scale for its x and y axes.
Instructions include the fan ratio and input/copy/output coordinates in units
of H so that differently framed pages can be transferred at a consistent
physical scale. Parallels retain the documented ruler-and-compass macro P=2J+3C.

**Paper demo · 10th root of 2000** uses Fast AK with the original X=2000 and
s=7/16 from `findInitialState`'s certified interval comparisons. It does not
use a numerical root to choose s. The four modules implement
`s → s² → s⁴ → s⁵ → s¹⁰`, followed by the existing AK correction. Its genuinely
narrow rectangle keeps the prepared K finite and within the overview;
`adaptRectangle` considers W=Hp/max(p,X) as an additional AK candidate.
The preset does not calibrate the state to 1, which would make every power
point coincide. Normal gallery initialization continues to use its existing
calibration and manual-iteration workflow.

The expandable paper measurements refer to the displayed full construction
or selected module. They report the bounding box, minimum nonzero line angle,
minimum separation, maximum center distance from the origin, and a count of
small-angle/near-point pairs. Lengths are divided by H. In the floating-point
readability measurement, separations ≤10⁻¹² H and angles ≤10⁻⁹ degrees are treated
as aliases/intentional parallels, not physical resolution certificates. The
A nonzero sub-resolution gap suppresses the paper-size recommendation: the display cannot decide whether it is a true separation or roundoff at an exact alias. The
near-point threshold is 0.02 H and the small-angle threshold is 10 degrees.
The instructions explicitly explain coincident roles such as s=1.

The paper-size heuristic targets 10 mm between distinct points and 10 degrees
between nonparallel lines. It tries A4, A3, then A2 in either orientation with
10 mm margins. If separation would require a larger sheet it says **Beyond
A2**. If the angle target fails it says that magnification cannot fix it.
Uniform scaling changes neither angles nor normalized ratios. W/H changes
the rectangle's aspect, while λ/H controls the fan geometry; they are separate
choices. **Physical precision depends on ruler, compass, line width and
transfer error.** There is no theorem of physical accuracy or guaranteed
number of decimal places.

Tests cover 490 parameterized incidence products, 140 spread/classic comparisons,
the certified p=10 preset, scale-invariant routing, 36 additional initialized
spread orbits, all four million-degree supports, module navigation, mobile
layout and the nine historical previews. Browser artifacts include
`paper-p10-x2000-full.png`, `paper-p10-x2000-module.png`,
`paper-p10-x2000-paper.png`, and `paper-million-current-module.png`.

## Finite construction versus conditioning

For H≠0, U× and R(b) are distinct regardless of b. Their join has vertical
coefficient −H, so its parallel meets x=W uniquely at a finite point.
The copying line meets y=H uniquely because its horizontal coefficient is H.
Thus the binary telescope has no exact incidence degeneracy, including when
a or b equals 1. Repeated points with different names are intentional aliases.

For p≥3,X,s>0, the reused rectangle supports are also finite in exact arithmetic:
M and E have different abscissas; AK is nonhorizontal; the projective projector
has height above H while E is below H; AD and the decentered D have abscissa
strictly less than W. The report denominator is positive for each scalar map.
For the decentered arc, α=(5p+2)/(p−2)>0 and
(t+α)^2−(α²−1)=t²+2αt+1>0, which proves a transverse intersection.
The separate [native incidence audit](NATIVE_NONDEGENERACY.md) now formalizes
these support and branch-existence assertions in
`RectangleNativeNondegeneracy.lean`, and composes them with the binary stage.
Its machine-readable table records every step and exceptional equation.

Finite exact coordinates need not be small or distinguishable in floating point.
The browser computes the circle height as sqrt(r−d)*sqrt(r+d), avoiding the
subtraction of two squared large quantities. It rejects an unresolved gap rather
than clamping a negative discriminant to zero. Geometric E and the final readout
are independently checked. A valid projective point at infinity is retained;
a zero cross product, coincident join points, a non-real circle intersection,
or an unidentified circle branch remains a failure.

## Dyadic normalization

The V20 button keeps X′=c^p X, s′=s/c, c=2^k, preserving t=Xs^p.
For the reciprocal-root state, s_original=c*s_normalized. For the direct root,
root_original=root_normalized/c. These are different readout conventions.

The new button **Renormalisation adaptative optimale** searches k=0 and ±10
neighbors of the V20 exponent and the exponent placing s near 1. Candidates
are deduplicated, generated in log space, and rejected if their actual geometry
cannot be constructed reliably. Among the successful candidates, it minimizes
an explicit score of affine extent, small nonzero point separation, small
nonzero angles, circle transversality, warnings, and independent discrepancy.
Intentional exact parallelisms and aliases are not penalized as degeneracies.
The angular component is a conservative all-line comparison, not a theorem
about the condition number of the full algorithm.

The UI reports c, k, valid/tested candidates, score, discrepancy and selection
reason. The raw k=0 candidate is included when constructible, so the selected
score cannot exceed its score. **Optimal means only among the tested dyadic
scales for this heuristic score.** It is not a global geometric optimum.
When direct construction fails, the UI tries this search before reporting
unavailability. Explicit button use also permits improving an already valid
construction.

Log-space residual and reciprocal-root calculations avoid overflowing an
intermediate X*s^p. They do not provide arbitrary precision. At very large p,
one dyadic step changes log X by p log 2; there may be no representable helpful
scale. Tiny encoded powers can also be lost in 1−y/H. Such cases are reported
as numerical-conditioning failures, not as geometric impossibility.

## Stereographic continuation

`needsStereographicView` checks required point coordinates and circle extent
(default affine threshold 10,000). Infinite points and near-pole coordinates
trigger automatic sphere display; a later manual view choice is respected.
The original homogeneous directions remain distinct in the incidence engine,
even though all points at infinity map to the north pole N. No intersection
is computed on the sphere. The nine historical demos remain unchanged.

## Formal scope and reproducibility

`LeanMath/Papers/RectangleFastPower.lean` proves:

- copying incidence and uniqueness, multiplication incidence and unique readout;
- noncoincidence of the join endpoints and transverse right-rail intersection;
- a halving recursion `binaryPower s p = s^p`;
- a recursive construction by actual rail meets, with final readout s^p;
- the recursive multiplication count, its bound 2*floor(log2 p), and exactly
  k multiplications for p=2^k;
- equality of the four fast scalar maps with their existing supports;
- global convergence for fast AK, AD, and projective AD by reusing existing
  convergence theorems. No new analytic convergence theorem for the arc is claimed.

The exact popcount formula is explained above and tested against the JS
construction; Lean certifies the recursive count and logarithmic bound instead.
The geometric recursion specifies the same intersections; the browser additionally
caches top-rail copies. Floating-point accuracy, adaptive scoring and UI behavior
are tested, not proved in Lean. This module has its **own audit** in
`validation/rectangle_fast_power/Audit.lean`; it does not change V20's 149+11 count.

```sh
npm ci
npm run test:geometry
python3 -m http.server 8765 --directory docs  # keep running in another terminal
npm run test:browser                        # install Playwright Chromium first
lake build LeanMath.Papers.RectangleFastPower
python3 scripts/audit_fast_power.py
```

The geometry matrix covers 864 configurations, plus high degrees through
1,000,000, the count examples, X from 1e−200 to 1e200 with degree-3 adaptive
normalization, invariance, raw-score dominance, infinity and true-degeneracy
regressions. Browser tests cover all eleven methods, sphere/manual return,
large degree, adaptive metadata, dark/light views, 360px layout and nine archives.

The additional native audit has 56 classification rows, exact symbolic cross-checks,
and 72 browser-engine regressions at s=1 (including X=1 and X=p).
