# Exact incidence audit of the four original rectangle protocols

**Post-V20 audit.** The V20 paper and frozen proof snapshot are unchanged.
For integer p≥3 and W,H,X,s>0, all required intermediates of native AK,
centered AD, projective AD [2/1] and decentered AD are finite and uniquely
defined. This is an incidence theorem, independent of scalar convergence.
No positive-domain counterexample or alternate chart is needed for these four
protocols. It does **not** assert this for the pencil or fixed-circle protocols.

The [machine-readable table](NATIVE_NONDEGENERACY.json) contains the same
step-by-step classification, parameter dependencies and formal references.

## Coordinates and determinant certificates

Write A0=(W,H), B=(W,0), C=(0,0), O=(0,H), P=(W,H(1−s)),
M=(0,H(1−1/X)), E=(W,H(1−s^p)), t=X*s^p.
A line is a*x+b*y=c, embedded as [a:b:−c]. Its meet with another line is
the homogeneous cross product. The meet's weight is the determinant a*b′−a′*b.
A nonzero weight proves a unique finite meet, and also proves both lines proper.
`homogeneous_meet_finite` and `homogeneous_meet_readout` connect these cross
products to the affine certificates. `homogeneous_intersection_unique` also proves
that every nonzero homogeneous common point has nonzero weight and the same
affine readout, excluding a second ideal intersection. No scalar convergence
theorem enters these proofs.

In the native chain Lj=(0,H(1−s^j)) and Bj=(W*s^j,H(1−s^j)).
The red line L1B has b=W. A parallel through Bj therefore meets the left
rail uniquely at L(j+1). The next horizontal meets OB with determinant −H
and the right rail with determinant −1. At s=1 all Lj=C and Bj=B;
the red line is CB, with no undefined join or meet.

For the shared correction, let m=H/(WX)*(1−t) be the slope of ME, and
let k be the support slope through A0 and D (D=K in AK). The actual determinant
of join(A0,D) and parallel(ME,P) is

`−W * (D.x−W) * (k−m)`.

The proof checks both nonzero horizontal separation and positive slope gap.
It then certifies the final horizontal intersection for every resulting T.
This addresses the actual constructed support, not just an equivalent scalar map.

For projective AD, `det(ZE,ell)=H/((2p−1)X)*((2p−1)t+p+1)>0`.
Thus ZE cannot be parallel to ell, D cannot become infinite, and Z cannot equal E.
Moreover D.x>W, so D cannot equal A0. Calling the support projective does not
force an infinite intermediate in this positive-domain chart.

For centered AD, the radius is r=H*s^p>0 and the prepared vertical passes
through F0. Its two circle intersections are (F0.x,F0.y±r); the strict lower
condition selects exactly one. For decentered AD, set

`alpha=(5p+2)/(p−2)`, `beta=(p−1)*sqrt((p−2)/(12p))`,
`dx=W−W/beta`, `delta=(H/X)*sqrt(alpha^2−1)`,
`F=(dx+delta,H−H/(X*beta))`, `G=(W,H+H*alpha/X)`.

Then EG=(H/X)(t+alpha)>0, and
`EG^2−delta^2=(H/X)^2*(t^2+2*alpha*t+1)>0`.
Lean proves the radius transfer, identity, strict positivity, and uniqueness
of the branch D.y<F.y. The remaining support has D.x−W=−W/beta≠0 and
k−m=H/(WX)*(t+beta*sqrt(t^2+2*alpha*t+1))>0.

## Step-by-step table

A means finite and unique; B means an optional ideal direction with complete
continuation. There are no C (true degeneracy) cases in this domain.
For already finite steps, “continuable” means yes, without needing infinity.
The equations below describe potential failure tests under the stated preparation
formulas; they are not claims that those formulas extend through excluded p or X.

| Method | Step | Exceptional equation | Positive-domain solutions | Finite? | Projectively continuable? | Fixed by normalization? | Alternate chart? | Lean theorem |
|---|---|---|---|---|---|---|---|---|
| AK | Rectangle O, A0, B, C; initial P | W=0 or H=0 would collapse a rectangle side | None | Yes | Yes | Not needed; no exception in the positive domain | No | `native_telescope` |
| AK | Initial horizontal; L1; B1; fixed OB | det(horizontal,left)=-1; det(horizontal,OB)=-H | None | Yes | Yes | Not needed; no exception in the positive domain | No | `native_telescope` |
| AK | Red join L1B | L1=B requires W=0 AND H(1-s)=0 | None | Yes | Yes | Not needed; no exception in the positive domain | No | `native_telescope` |
| AK | Each parallel through Bj; next Lj | det(left,parallel)=W=0 | None | Yes | Yes | Not needed; no exception in the positive domain | No | `native_telescope` |
| AK | Each horizontal; next Bj | det(horizontal,OB)=-H=0 | None | Yes | Yes | Not needed; no exception in the positive domain | No | `native_telescope` |
| AK | Final E on right rail | det(horizontal,right)=-1=0 | None | Yes | Yes | Not needed; no exception in the positive domain | No | `native_telescope` |
| AK | M and ME | X=0; M=E would require W=0 | None | Yes | Yes | Not needed; no exception in the positive domain | No | `report_certificate` |
| AK | Horizontal report T to P+ | det(horizontal(T.y),right)=-1=0 | None | Yes | Yes | Not needed; no exception in the positive domain | No | `report_certificate` |
| AK | s=1 (repeated named points) | s=1 is a harmless coincidence, not an exceptional meet | All p>=3, X,W,H>0 at s=1 | Yes | Yes | s/c=1 iff s=c; c=2 moves s=1, but no repair is necessary | No | `native_at_one` |
| AD | Rectangle O, A0, B, C; initial P | W=0 or H=0 would collapse a rectangle side | None | Yes | Yes | Not needed; no exception in the positive domain | No | `native_telescope` |
| AD | Initial horizontal; L1; B1; fixed OB | det(horizontal,left)=-1; det(horizontal,OB)=-H | None | Yes | Yes | Not needed; no exception in the positive domain | No | `native_telescope` |
| AD | Red join L1B | L1=B requires W=0 AND H(1-s)=0 | None | Yes | Yes | Not needed; no exception in the positive domain | No | `native_telescope` |
| AD | Each parallel through Bj; next Lj | det(left,parallel)=W=0 | None | Yes | Yes | Not needed; no exception in the positive domain | No | `native_telescope` |
| AD | Each horizontal; next Bj | det(horizontal,OB)=-H=0 | None | Yes | Yes | Not needed; no exception in the positive domain | No | `native_telescope` |
| AD | Final E on right rail | det(horizontal,right)=-1=0 | None | Yes | Yes | Not needed; no exception in the positive domain | No | `native_telescope` |
| AD | M and ME | X=0; M=E would require W=0 | None | Yes | Yes | Not needed; no exception in the positive domain | No | `report_certificate` |
| AD | Horizontal report T to P+ | det(horizontal(T.y),right)=-1=0 | None | Yes | Yes | Not needed; no exception in the positive domain | No | `report_certificate` |
| AD | s=1 (repeated named points) | s=1 is a harmless coincidence, not an exceptional meet | All p>=3, X,W,H>0 at s=1 | Yes | Yes | s/c=1 iff s=c; c=2 moves s=1, but no repair is necessary | No | `native_at_one` |
| projective | Rectangle O, A0, B, C; initial P | W=0 or H=0 would collapse a rectangle side | None | Yes | Yes | Not needed; no exception in the positive domain | No | `native_telescope` |
| projective | Initial horizontal; L1; B1; fixed OB | det(horizontal,left)=-1; det(horizontal,OB)=-H | None | Yes | Yes | Not needed; no exception in the positive domain | No | `native_telescope` |
| projective | Red join L1B | L1=B requires W=0 AND H(1-s)=0 | None | Yes | Yes | Not needed; no exception in the positive domain | No | `native_telescope` |
| projective | Each parallel through Bj; next Lj | det(left,parallel)=W=0 | None | Yes | Yes | Not needed; no exception in the positive domain | No | `native_telescope` |
| projective | Each horizontal; next Bj | det(horizontal,OB)=-H=0 | None | Yes | Yes | Not needed; no exception in the positive domain | No | `native_telescope` |
| projective | Final E on right rail | det(horizontal,right)=-1=0 | None | Yes | Yes | Not needed; no exception in the positive domain | No | `native_telescope` |
| projective | M and ME | X=0; M=E would require W=0 | None | Yes | Yes | Not needed; no exception in the positive domain | No | `report_certificate` |
| projective | Horizontal report T to P+ | det(horizontal(T.y),right)=-1=0 | None | Yes | Yes | Not needed; no exception in the positive domain | No | `report_certificate` |
| projective | s=1 (repeated named points) | s=1 is a harmless coincidence, not an exceptional meet | All p>=3, X,W,H>0 at s=1 | Yes | Yes | s/c=1 iff s=c; c=2 moves s=1, but no repair is necessary | No | `native_at_one` |
| arc | Rectangle O, A0, B, C; initial P | W=0 or H=0 would collapse a rectangle side | None | Yes | Yes | Not needed; no exception in the positive domain | No | `native_telescope` |
| arc | Initial horizontal; L1; B1; fixed OB | det(horizontal,left)=-1; det(horizontal,OB)=-H | None | Yes | Yes | Not needed; no exception in the positive domain | No | `native_telescope` |
| arc | Red join L1B | L1=B requires W=0 AND H(1-s)=0 | None | Yes | Yes | Not needed; no exception in the positive domain | No | `native_telescope` |
| arc | Each parallel through Bj; next Lj | det(left,parallel)=W=0 | None | Yes | Yes | Not needed; no exception in the positive domain | No | `native_telescope` |
| arc | Each horizontal; next Bj | det(horizontal,OB)=-H=0 | None | Yes | Yes | Not needed; no exception in the positive domain | No | `native_telescope` |
| arc | Final E on right rail | det(horizontal,right)=-1=0 | None | Yes | Yes | Not needed; no exception in the positive domain | No | `native_telescope` |
| arc | M and ME | X=0; M=E would require W=0 | None | Yes | Yes | Not needed; no exception in the positive domain | No | `report_certificate` |
| arc | Horizontal report T to P+ | det(horizontal(T.y),right)=-1=0 | None | Yes | Yes | Not needed; no exception in the positive domain | No | `report_certificate` |
| arc | s=1 (repeated named points) | s=1 is a harmless coincidence, not an exceptional meet | All p>=3, X,W,H>0 at s=1 | Yes | Yes | s/c=1 iff s=c; c=2 moves s=1, but no repair is necessary | No | `native_at_one` |
| AK | K preparation | p=0 | None | Yes | Yes | Not needed; no exception in the positive domain | No | `AK_support` |
| AK | A0K support | K=A0 requires H=0 and WX/p=0 | None | Yes | Yes | Not needed; no exception in the positive domain | No | `AK_support` |
| AK | Report parallel and T | k-m=H/(WX)*(p-1+t)=0 | None | Yes | Yes | Not needed; no exception in the positive domain | No | `AK_support` |
| AD | F0 and transferred radius | X(p-1)=0; H*s^p=0 | None | Yes | Yes | Not needed; no exception in the positive domain | No | `centered_circle` |
| AD | Circle / prepared vertical / lower D | margin=(H*s^p)^2=0 | None | Yes | Yes | Not needed; no exception in the positive domain | No | `centered_circle` |
| AD | A0D support | D.x-W=-2W/(p-1)=0 | None | Yes | Yes | Not needed; no exception in the positive domain | No | `AD_support` |
| AD | Report parallel and T | k-m=H/(2WX)*(p-1+(p+1)t)=0 | None | Yes | Yes | Not needed; no exception in the positive domain | No | `AD_support` |
| projective | Z and fixed ell | p(2p-1)X=0 or (p+1)X=0 | None | Yes | Yes | Not needed; no exception in the positive domain | No | `projective_projection` |
| projective | Z=E / proper ZE | Z.y-E.y=H/((2p-1)X)*((2p-1)t+p+1)=0 is necessary | None | Yes | Yes | Not needed; no exception in the positive domain | No | `projective_Z_ne_E` |
| projective | D=ZE intersect ell; parallelism; D at infinity | det(ZE,ell)=H/((2p-1)X)*((2p-1)t+p+1)=0 | None | Yes | Yes | Not needed; no exception in the positive domain | No | `projective_exception_equation` |
| projective | A0=D / A0D support | D.x-W=W*(5p-1)*pole/((p+1)*num)=0 | None | Yes | Yes | Not needed; no exception in the positive domain | No | `projective_support` |
| projective | Report parallel and T | k-m=H/(WX)*den/pole=0 | None | Yes | Yes | Not needed; no exception in the positive domain | No | `projective_support` |
| arc | beta, alpha, delta, F and fixed G | beta=0, X=0, or alpha^2-1<0 | None | Yes | Yes | Not needed; no exception in the positive domain | No | `arc_parameters` |
| arc | EG radius transfer | EG=0 iff t+alpha=0 | None | Yes | Yes | Not needed; no exception in the positive domain | No | `arc_radius_transfer` |
| arc | Circle / prepared vertical / lower D | margin=(H/X)^2*(t^2+2*alpha*t+1)=0 | None | Yes | Yes | Not needed; no exception in the positive domain | No | `arc_transverse` |
| arc | A0D support | D.x-W=-W/beta=0 | None | Yes | Yes | Not needed; no exception in the positive domain | No | `decentered_support` |
| arc | Report parallel and T | k-m=H/(WX)*(t+beta*sqrt(t^2+2*alpha*t+1))=0 | None | Yes | Yes | Not needed; no exception in the positive domain | No | `decentered_support` |
| all four | Optional ideal direction implementing a parallel | w=0 identically, direction=[b:-a:0] | Every parallel represented by its ideal direction | Ideal direction | Yes | No repair needed; direction remains ideal, sphere display only | No | `parallel_projective_continuation` |
| all four | Residual t=1; ME horizontal | t=1 is a harmless horizontal direction | All positive parameters satisfying X*s^p=1 | Yes | Yes | Cannot move t=1: residual_normalization proves invariance; no repair needed | No | `report_certificate` |
| all four | Fixed-vertex coincidences M=C; AK K=C | X=1 for M=C; X=p for AK K=C | X=1; X=p for AK | Yes | Yes | X changes to c^p X; target_marker_moves gives the exact transformed equation; no repair needed | No | `report_certificate` |

## Normalization and projective continuation

There is no exact positive-domain degeneracy here for normalization to repair.
It can improve numerical conditioning, and can move harmless markers depending
on s or X. Precisely, s/c=1 iff s=c, and c^p X=d iff X=d/c^p for c≠0.
Thus c=2 moves a native s=1 state away from that marker. Conversely,
`(c^p X)(s/c)^p=Xs^p`, so **every residual-only exceptional equation is invariant**.
The hypothetical report/projection/tangency equations depending on t cannot
be removed by a dyadic rescaling; they simply have no solution in this domain.
Zero-width/height boundaries and degree restrictions are also not repaired by
rescaling X and s. Positive rescaling preserves the domain.

If a parallel is implemented projectively, retain its direction as [b:−a:0].
It is nonzero for a proper line. Joining it to any finite Q produces the same
proper parallel; the next meet is finite by the certificates above. All such
directions display at N, but their original triples remain distinct. In particular,
the horizontal and vertical directions have nonzero mutual cross product even
though both display at N. No required original intermediate becomes infinite;
therefore there is no missing downstream exceptional-infinity case to resolve.

## Formal scope and four different claims

The explicit Lean theorem names are:

- `OriginalAK_global_geometric_existence`
- `OriginalAD_global_geometric_existence`
- `OriginalProjectiveAD_global_geometric_existence`
- `OriginalDecenteredAD_global_geometric_existence`

Their conclusions contain a `NativeCertificate`, a `ReportCertificate` for
actual joins and parallels, and the relevant circle/projection certificate.
`FinitePair` contains both a nonzero determinant and an `ExistsUnique` meet.
`LowerCircleCertificate` contains a positive radius, positive transverse margin,
an actual lower-branch point on the circle, and uniqueness of that branch.
This is stronger than merely declaring that an iterate exists as a real number.

`FastCertificate` separately proves all binary multiplier/copy intersections
finite and that their endpoint equals E. The four `Fast…_global_geometric_existence`
theorems reuse the original correction certificates without re-proving supports.

| Claim | Status |
|---|---|
| Global scalar convergence | Existing, separate results. AK/AD/projective formal; full decentered analytic convergence remains a written proof. |
| Global geometric existence | New incidence certificates for all four original and four fast protocols. |
| Finite affine realization | Every required intermediate is finite in exact real arithmetic; optional ideal-direction macros can use Euclidean parallels. |
| Numerically well-conditioned display | No global guarantee. Large finite extents, near-parallel lines and cancellation can exceed browser precision. |

The formal file is `LeanMath/Papers/RectangleNativeNondegeneracy.lean`, with 51 checked declarations and
its own audit `validation/rectangle_native_nondegeneracy/Audit.lean`. Historical
V20 audit counts remain 149+11. Run:

```sh
lake build LeanMath.Papers.RectangleNativeNondegeneracy
python3 scripts/audit_native_nondegeneracy.py
python3 scripts/test_native_nondegeneracy.py
npm run test:geometry
```
