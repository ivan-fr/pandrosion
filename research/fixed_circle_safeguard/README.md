# A geometric safeguard for the fixed-circle inverse

The fixed-circle inverse can be placed inside a **globally convergent geometric algorithm**. A polynomial residual test accepts a sufficiently improving circle step; centered AD / Halley supplies every other step. This does not enlarge the real domain of the unguarded quadratic model. It is a different, counted hybrid protocol.

For every integer `p≥3`, every `X>0` and every positive starting state, the exact hybrid converges to `a=X^(−1/p)`. Near the root its regular circle branch is eventually selected, so it inherits local order five. The global theorem and the incidence-based controller are formalized in [RectangleCircleSafeguard.lean](../../LeanMath/Papers/RectangleCircleSafeguard.lean). The analytic assembly of the circle's local fifth order remains the written proof in [V21](../../paper/reciprocal_geometry_v21/Reciprocal_Root_Geometry_v21.pdf).

## A root-free geometric decision

Cache `E=R(s^p)` and `T=R(t)`, where `t=Xs^p`, `R(q)=(W,H(1−q))`, and `W=2,H=4`. Stop when `T=B=R(1)`.

1. Attempt the prescribed descending circle branch. Reject a missing transverse crossing, an unavailable branch, a coincident `G=B`, or an infinite readout center (`v=rho`). No mobile join is needed to classify these incidences on the prepared chart.
2. For a positive candidate `c`, construct its power and residual `u=Xc^p` by binary products and a fixed scale.
3. Construct `R(u²)` and `R(tu²)` by two more products. Accept precisely when

   ```text
   t ≤ 1:    t ≤ u²  and  tu² ≤ 1
   t ≥ 1:    u² ≤ t  and  1 ≤ tu².
   ```

   These require three order comparisons on the same oriented rail, including the choice of side of one. Larger values have lower ordinates. No logarithm, target root, numerical error oracle or new circle is used by this control.
4. If accepted, reuse the candidate's power and residual as the next cache. Otherwise draw centered AD using the cached `E`, then build the power and residual of its output.

For positive `t,u`, the two polynomial inequalities are equivalent to
`|log u| ≤ |log t|/2`. Logarithms appear only in the correctness proof.

## Five joins for a product

Prepare the top centers `U_f=(Wf/(f−1),H)` for `f=1/2,1/4`. Given the two rail points `R(a),R(b)` with `b>0`, if `R(b)=B` simply reuse `R(a)`. Otherwise:

1. `C R(b)` meets the top at `V=U_(1/b)`.
2. `U_(1/2) R(a)` meets the left rail at `L(a/2)`.
3. Its join to `V` returns to `R(ab/2)`.
4. Project through `U_(1/2)` to `L(ab/4)`.
5. Project through `U_(1/4)` back to `R(ab)`.

All five joins and intersections are nondegenerate when `b>0,b≠1`. The equality test handles the exact exception; close to it the center can still be far away. This is an exact construction, not a uniform conditioning theorem.

A fixed positive factor `c` needs only two joins: project left through
`U_[c/(2(1+c))]`, then right through `U_[1/(2(1+c))]`. Their ratio is `c`; both centers are finite and prepared once. This realizes the input factor `X` and circle factor `k`, including `X=1`.

## Fully counted protocol

Let `L=floor(log2 p)`, `h=popcount(p)`, and `m=L+h−1`. The binary program has `m` product gadgets. The following are upper bounds, because a product with unit second input skips all five joins.

| Operation | Joins J | Parallel macros P | Mobile arcs C |
|---|---:|---:|---:|
| Initial power and residual cache | `5m+2` | 0 | 0 |
| Circle trial from cached state | 6 | 0 | 0 |
| Candidate power and residual | `5m+2` | 0 | 0 |
| Two control products | 10 | 0 | 0 |
| **Accepted step, including next cache** | **`5m+18`** | **0** | **0** |
| Full trial rejected, AD and refreshed cache | `10m+22` | 2 | 1 |

The six circle joins are: two for `kt`, one for the saved `L(rho s)`, then `ZT`, `BG`, and the final rail readout. Centered AD adds two joins (`ME`, `AD`), two parallel macros and one arc. An early rejection costs less than a full rejected trial.

Fixed preparation, already-drawn intersections, final inversion, branch/incidence tests and comparisons are excluded from the trace columns. A completed gate makes **three ordered comparisons**; it also makes `m+2` product identity tests. Initial cache and fallback refresh each add `m` identity tests. The root-stop equality is separate. Thus this is a branching ruler/compass protocol with explicit comparisons, not an unconditional sequence of joins.

At `p=3`, initialization is at most **12 joins**, each accepted step **28 joins**, and a full rejected step **42J+2P+1C**. With the paper's `P=2J+3C` macro this is **46J+7C=53 traces**. At `p=10^6`, `m=25`: initialization is 127 joins and acceptance 143 joins. These are explicit upper bounds, not minimum costs. **“Globally convergent in eight lines” is not a result of this construction.**

## Why the hybrid converges globally

Write `e(s)=|log(Xs^p)|`. AD lies between `s` and the positive root, so it never increases `e`; an accepted circle step at least halves it. The nonnegative errors therefore decrease to some limit `ell`.

If `ell>0`, eventually the errors are below `3ell/2`. A halving step would then produce an error below `3ell/4`, contradicting the lower bound `ell`. Consequently all sufficiently late steps must be AD, whose global convergence forces error zero. Hence `ell=0` and `s→a`.

This proof permits any trial function and any additional availability rejections. It does not assume full-branch contraction of the circle. Local fifth order gives `e(c)/e(s)→0`, so the half-error gate eventually accepts on a regular neighborhood. The selected compact chart (the separate degree-four chart at `p=4`) is regular at `v=1`, as formally checked. It need not be regular everywhere.

## Formal boundary and reproduction

The Lean module proves the polynomial/logarithmic gate equivalence, the monotonicity property of AD, the switching convergence theorem, its closed circle specialization, five-join multiplication, two-join scaling, geometric binary powers, the rail gate and their composition with the hybrid. `ruler_circle_AD_global` states convergence using the actual incidence-based residual and gate program. The previously proved circle incidence certificates justify the circle candidate's geometric readout under the stated chart conditions.

`eventual_selection` and `local_order_inherited` are formal transfer theorems with explicit analytic premises. They do not replace the paper's inverse-function proof of the concrete circle's fifth order. The physical trace inventory is a written protocol count, independently instrumented by the geometry implementation; it is not a formal execution-cost semantics in Lean.

```sh
lake build LeanMath.Papers.RectangleCircleSafeguard
python3 scripts/audit_circle_safeguard.py
python3 research/fixed_circle_safeguard/verify.py
python3 research/fixed_circle_safeguard/draw.py
```

The geometric implementation places moving points by line/circle intersections; an independent scalar calculation is used only by the verifier. The 180-digit campaign covers **144 trajectories**, eight degrees from 3 to one million, three inputs (`0.01,2,500000`), and six initial log residuals from −30 to 30. It also checks forced full rejections, both-positive-root branch selection, exact unit products, exact fixed points, missing crossings and the singular readout cases `(p,t)=(3,7.75),(5,16)`. See [results.json](results.json).

Finite tests are not a proof of all inputs or a browser-precision guarantee. The numerical implementation conservatively rejects a small precision-dependent neighborhood of singular circle readouts. Its order comparisons are high-precision arithmetic, not outward-rounded interval certificates. Unbounded rail points and large powers remain possible for unrestricted positive data. The browser gallery and analog model are unchanged by this research addition.
