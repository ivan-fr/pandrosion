# Certified preparation and adaptable rectangles (post-V20)

The default gallery takes the **original p and X** and prepares the construction
automatically. It does not run an iterative solver: **one click on “Une itération”
applies one geometric step**. Original X remains unchanged in its input field.
The displayed approximation is the direct root in the original units, 1/(c*u).
The working target, reciprocal state, calibration certificates, manual controls,
and independent reference calculation are inside the closed advanced panel.

The four binary variants are available in this simple view. Advanced exploration
retains all eleven methods and nine historical demos. Width and height controls
apply to the four rectangle methods and their binary variants. The three other
V20 protocols retain their original 2×4 preparation.

## Exact initialization

The original narrow theorem remains: for every real X>0 and integer p≥3, midpoint
comparisons find a positive dyadic rational c with 1≤X*c^p≤2, without a root oracle.
The new default accepts the **wider band 1/4≤X*c^p≤4**. The narrow [1,2] option
remains available in manual exploration.

The search brackets residual level 3/2 using powers of two, then bisects. The
formal model starts from [0,2^m]; the runtime can use a tighter positive bracket.
`wide_first_acceptance` proves existence of the first wide-band midpoint for
any valid bracket. `wide_dyadic_initialization` proves that this first accepted
point is a positive dyadic rational. Termination follows from the stronger narrow
termination theorem: a search reaching [1,2] must already have reached [1/4,4].
The proof does not assume that every earlier candidate is in the narrow band.

Set Y*=X*c^p and u₀=1. Then

    Y* * u^p = X * (c*u)^p,
    update(X,c*u) = c * update(Y*,u).

Lean proves this exact conjugacy for all four correction maps and all iterates.
The original reciprocal state is s=c*u; the direct-root approximation is 1/s.
Preparation selects a new starting state, rather than merely rescaling an
arbitrary old state. Its comparisons and arithmetic preparation are separate
from the mobile join/parallel/arc count.

## Rectangle dimensions and geometric guarantees

The reference rectangle has W=2,H=4. The incidence engine now accepts positive
W,H for AK, AD, projective AD and decentered-arc AD, including binary variants.
It **rebuilds their Euclidean supports and circles** from these parameters.
Nonuniformly stretching a rendered circle would produce an ellipse and is not
used. The AD radius is H*u^p; the decentered arc uses the actual distance EG in
the newly prepared rectangle. Readout is 1−P.y/H.

At u₀=1 all powers equal 1. Repeated points C/B are therefore mathematically
coincident and remain so under changes of dimensions. For Y* in the wide band,
Lean establishes the initial bounds

    −3H ≤ M.y ≤ 3H/4,
    −W/3 ≤ K.x ≤ W          (p≥3).

`wide_adaptive_orbit_geometry` supplies native, binary and actual support/circle/
projection certificates at every exact iterate, even if positive W and H are
chosen anew at each step. `rectangle_power_readout_invariant` establishes that
changing rectangle dimensions preserves the geometric binary-power readout.
The existing support/readout results are parameterized by W,H.

This proves existence and the listed bounds, not a uniform condition number or
that every support remains inside the rectangle. The full analytic convergence
of decentered AD is not newly proved here.

## Layout and magnification

Automatic preparation tests W/H in {1/4,1/2,1,2,4,8,16}, together with the current
ratio, and retains a constructible candidate balancing the bounding box of the
actual points and circles for the overview. H=4 is the default reference height.
Manual exploration allows both dimensions to be changed and the selection to
be rerun. This is a finite layout heuristic, not a global optimization theorem.

Both planar panels use equal horizontal and vertical scales. The second panel
can zoom into P and P⁺ when their separation is small, independently of the
overview; “Rectangle entier” restores the complete rectangle. The magnification
is bounded and cannot separate exactly coincident points. Stereographic display
is centered/scaled consistently with the selected rectangle.

## Browser certificates and precision limits

The interval engine decodes binary64 inputs as exact integer mantissas times
powers of two. Products use outward-rounded BigInt mantissas of about 128 bits
and separately stored exponents. Powers require O(log p) multiplication stages,
without allocating p-sized integers or overflowing binary64 exponentiation.
A candidate is accepted only if its whole residual interval lies in the selected
band. Midpoint refinement is capped at 80 attempts; unresolved comparisons fail
explicitly. Binary modes support p through 1,000,000; native displays retain p≤32.

The browser uses rounded target Y and separately certifies

    |Y−Y*| ≤ 2^-48,       1/4 ≤ Y ≤ 4.

For u≥0, `wide_calibration_residual_error` proves

    |X*(c*u)^p−Y*u^p| ≤ 4 * 2^-48 * (Y*u^p).

The narrow version retains its smaller factor one. Exact conjugacy is not
attributed to the rounded browser parameter. Common interval-product, acceptance
and outward-rounding lemmas are formalized, but the JavaScript/IEEE decoder is
not extracted from Lean or formally verified end to end.

Every user-triggered proposed step uses the actual geometric readout. It must
strictly improve the certified absolute residual error |Y*u^p−1|, and both states
must stay in the runtime guard band [1/8,4] (or [1/4,2] for narrow preparation).
Otherwise the current state is retained and the limitation reported. These are
runtime safeguards, **not invariant-band theorems**. In particular AK from Y=4,
u=1,p=1,000,000 reaches a residual near 0.199149, outside the initial [1/4,4].
A failed calibrated incidence does not silently restart or recalibrate the orbit.

## Example and validation

For p=1,000,000 and X=500,000, wide preparation selects

    c = 0.9999866485595703,
    Y ≈ 0.7951963739618497,
    u₀ = 1.

The visible X stays 500,000. No iteration occurs until the user clicks.

The initialization module now has **34 audited declarations**: the previous 26
plus eight wide-band and dimension results. Only propext, Classical.choice and
Quot.sound are allowed by the independent audit. The V20 paper/snapshot and its
149+11 audit remain unchanged.

Validation includes 600 narrow trajectories, 600 wide trajectories with selected
rectangles, 800 dimension/method cases checking scalar readout and genuine circle
incidence, 28 full-integer reference powers, and 80 independent 100-digit interval
and rounding checks. Browser tests check unchanged original X, no background
iteration, exactly one step per click, all four automatic methods, manual controls,
all eleven legacy/fast modes, nine archives and 360px layouts.

```sh
npm run test:initialization
npm run test:layout
python3 scripts/check_initialization.py
lake build LeanMath.Papers.RectangleInitialization
python3 scripts/audit_initialization.py
```
