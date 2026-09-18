# Certified initialization and calibration (post-V20)

The gallery's **Initialiser et calibrer** button chooses a new start from p and X.
It is different from renormalizing an existing state. It is available for the
four original rectangle methods and their four binary variants. The V20 paper,
its snapshot and its audit counts are unchanged.

## The exact theorem

For every real X>0 and integer p≥3, a finite midpoint search finds a **positive
dyadic rational c** such that

    1 ≤ X*c^p ≤ 2.

Define Y*=X*c^p and work in the calibrated chart with initial state u₀=1.
The original state is s=c*u. The exact identity

    Y* * u^p = X * (c*u)^p

preserves the residual, and each of the four correction maps satisfies

    update(X,c*u) = c * update(Y*,u).

This conjugacy is proved for every iterate. Choosing c requires comparisons,
powers and midpoints, not evaluation of a p-th root. The operation is a **new
initialization**, which replaces the user's previous state. It does not purport
to repair an arbitrary existing residual while preserving that state.

The scale c is a dyadic rational (an integer divided by a power of two), not
necessarily a single power of two. This is why it can calibrate a millionth-root
problem without multiplying X by the unusably large factor 2^1,000,000.
The existing V20 renormalization and adaptive dyadic-scale buttons are retained.

## Construction and termination

Bracket the interior residual target 3/2 between two positive power-of-two states
(or use the formal initial bracket [0,2^m]). Compare the midpoint's residual to
3/2 and retain the corresponding half. Accept as soon as the midpoint residual
is certified to lie in [1,2]. All such midpoint states are dyadic.

The Lean proof establishes bracket preservation, width division by 2 at each
step, and the bound

    X*(u^p−l^p) ≤ X*(u−l)*p*B^(p−1)       (0≤l≤u≤B).

Eventually this residual width is less than 1/2. Since the bracket contains the
residual level 3/2, its midpoint then lies strictly between residuals 1 and 2.
A power-of-two initial upper bound exists by the Archimedean property. This
proves finite termination of the ideal real-arithmetic search for every X>0.
It does not assert a fixed iteration cap for arbitrary real arithmetic.

The scale can be prepared using repeated halving, joins/parallels for products,
and comparisons. The current UI implements this preparation arithmetically and
reports its comparison count; it does not animate or charge its entire
ruler-and-compass construction to the mobile J/P/C count. Moving geometry still
comes from the existing homogeneous incidence engine.

## Why the calibrated start helps

At u₀=1, every power in either telescope equals 1: Lj=C, Bj=B, E=B.
These repeated named points are harmless: the native non-degeneracy certificates
already cover them. The multiplier unit and right point remain distinct.
Lean also proves, for 1≤Y*≤2, the initial bounds

    0 ≤ M.y ≤ H/2,
    W/3 ≤ K.x ≤ W        (AK, p≥3).

More generally, the exact calibrated target is bounded independently of p,
and all four correction preparations and reports exist by the native audit.
All subsequent exact scalar iterates remain positive. The new theorem
`calibrated_orbit_geometry` therefore supplies both native and binary telescope
certificates and the actual support/circle/projection certificate at **every
exact iteration**, including decentered AD. This is a geometric existence
statement, not a new proof of the arc's analytic convergence.

These results do **not** assert a uniform condition number. Some support points
approach each other as p grows. Neither all display errors nor every future
floating-point intersection are proved bounded. Full uniform coordinate bounds
for every support are not claimed by this module.

## Browser certificates and rounding

`docs/initialization.js` decodes each positive binary64 input exactly as an integer
mantissa times 2^e. It computes powers with integer interval multiplication,
rounding the lower endpoint down and the upper endpoint up to approximately
128 significant bits (plus a possible carry bit). Exponents are stored separately:
X*c^p can be compared to 1 and 2 without overflowing or underflowing a JavaScript
number. Multiplication uses O(log p) stages; it does not allocate p-sized integers.

A state is accepted only when the **entire** resulting residual interval lies
in [1,2]. Every binary64 candidate is itself an exact dyadic rational. Bracketing
uses powers of two; midpoint refinement is capped at 80 attempts. Unresolved
comparisons or representability failure produce an error rather than a guessed
certificate. The gallery supports integer p from 3 through 1,000,000 in fast
modes; native linear modes retain their p≤32 display limit.

The target supplied to the floating-point geometry is a rounded value Y of Y*.
The preparation separately verifies with integer intervals that

    |Y − Y*| ≤ 2^-48,       1 ≤ Y ≤ 2.

This is an explicit approximation, not an assertion of exact conjugacy for the
rounded browser parameter. Lean proves that, for nonnegative u, this error implies

    |X*(c*u)^p − Y*u^p| ≤ 2^-48 * (Y*u^p).

The common interval-product, acceptance, and outward integer-rounding lemmas are
formalized. The JavaScript IEEE decoder and complete runtime are not extracted
from Lean or formally verified end to end. Tests compare interval certificates
with independent full-integer powers and 100-digit arithmetic.

## Iteration guard

After initialization, each proposed geometric readout is checked with the same
interval engine. Both the current and proposed residual must remain in [1/4,2].
A new point is accepted only if the upper bound on its absolute residual error
is below the lower bound on the previous absolute residual error, relative to
the represented calibrated target Y. Otherwise the UI keeps the current state
and reports a numerical precision stop. It never substitutes the independent
scalar correction for a failed geometric point.

This check is a runtime safeguard, **not a theorem that all exact maps preserve
[1/4,2]**. If an incidence fails numerically, the calibrated workflow reports
that limitation instead of silently recalibrating or reinitializing the orbit.
Manual parameter edits clear the initialization certificate. The conversion
back to original units remains visible: reciprocal state s=c*u, direct-root
readout divided by c (composed with any previously active scale).

## Millionth-root example

For p=1,000,000 and X=500,000, the current search takes 22 comparisons and finds

    c = 0.9999871253967285
    Y ≈ 1.28104637891846
    u₀ = 1.

The four fast constructions then iterate in this moderate chart. The initially
entered s can be unusable (for example 0.75): initialization explicitly replaces
it. Merely rescaling that old state would preserve its extreme residual.

## Formal coverage and tests

`LeanMath/Papers/RectangleInitialization.lean` has its own 26-declaration audit:
`validation/rectangle_initialization/Audit.lean`. The principal exports are
`GeometricInitializationTheorem`, `positive_dyadic_initialization`,
`bisection_terminates`, `update_calibration`, `orbit_calibration`,
`calibrated_orbit_geometry`, and `calibration_residual_error`.

The new tests cover:

- 600 native/fast trajectories, including degrees through 1,000,000 and targets
  from the smallest positive subnormal to the largest finite binary64 value;
- 1,727 accepted, strictly improving steps, followed by a precision stop;
- 28 independent full-integer reference powers and 40 independent 100-digit
  checks of residual enclosures and calibration error;
- recovery in the browser from p=1,000,000, X=500,000, s=0.75, iteration and
  precision stopping, and the expanded 360px layout.

```sh
npm run test:initialization
python3 scripts/check_initialization.py
lake build LeanMath.Papers.RectangleInitialization
python3 scripts/audit_initialization.py
```

The older geometry matrix, browser/archive tests and independent Lean audits
remain in CI. No initialization or floating-point claim is attributed to V20.
