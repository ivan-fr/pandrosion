# Binary-power rectangle constructions (post-V20)

This experiment adds four ways to construct the **existing** AK, AD, projective
AD [2/1], and decentered-arc AD maps. It does not introduce new root iterations
or modify the frozen V20 paper or its formal snapshot. Their local orders remain
2, 3, 4, and 5. The gallery has seven V20 protocols and four experimental modes.

## A multiplication by incidences

For W,H>0, use A=(W,H), B=(W,0), the right encoding R(q)=(W,H(1−q)),
the top encoding X(q)=(W+Hq,H), and the fixed unit U×=(W+H,H).
The gallery uses W=2,H=4, hence U×=(6,4).

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
