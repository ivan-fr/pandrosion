# Existing AD5: factorizations, protocols and limits

For p≥3,t>0, g>0 and C5=(1+g)/(t+g). The complete nonzero scaled family is
κh=h(1+g), rh=h(1−t). This preserves scalar convergence, not drawing cost.

## Candidate ledger

| h | κh | rh | Geometric status |
|---|---|---|---|
| 1 | 1+g | 1−t | V20 baseline, fully implemented |
| positive constant c | c(1+g) | c(1−t) | constructible affine scalings; no automatic free rescaling claim |
| p/(1+g) | p | p(1−t)/(1+g) | fixed AK, explicit protocol below, implemented |
| 1/(1+g) | 1 | (1−t)/(1+g) | same protocol with support level 1; benchmarked |
| 2p/(1+g) | 2p | 2p(1−t)/(1+g) | same protocol, benchmarked |
| 1/(1+t) | (1+g)/(1+t) | (1−t)/(1+t) | bounded Cayley circle core below; full primitive circuit upper bound, not optimized |
| t/(1+t) | t(1+g)/(1+t) | t(1−t)/(1+t) | previous pair plus multiplication by t; does not bound both slopes at infinity |
| 1/g | 1+1/g | (1−t)/g | reuse g then divide; not an additional square root; no shorter protocol established |
| angle-optimal h | see derivation | see derivation | extra radical and t=1 singular scaling; rejected as a global budget solution |

For the last algebraic candidates use the signed arithmetic macros in
`report.md`. They are explicit constructibility upper bounds, not measured
minimum trace counts. The completed protocol comparison does not establish
Pareto-optimality over all these factorizations, let alone all constructions.

## Fixed support protocol (all four variants)

Choose a positive constant support level k0 (k0=p in the gallery).
Prepare K=(W(1−X/k0),0) and AK. Given the old coefficient κ0, construct

    R=(Wκ0/k0, H(1−t/X)).

The slope of MR is H/(WX) times k0(1−t)/κ0. Draw MR, its parallel
through P to AK, then the horizontal through T to P+. These last operations
are 1J+2P. They realize exactly the old scalar correction.

* Newton: k0=p gives R=E and recovers the original construction. For another
  k0 use the fixed vertical x=Wp/k0, meeting the last chain horizontal.
* Halley: prepare the fixed rail
  2k0 x/W+(p−1)X y/H=p+1+(p−1)X. The **already drawn** last horizontal
  meets it at R. No new mobile line is required. Its horizontal intersection
  is transverse because 2k0/W≠0. Both MR and AK are proper and their report
  is unique on positive states. No circle is needed.
* Projective [2/1]: put u=2p−1,v=p+1,
  t0=(k0(5p−1)−2pv)/(2pu−k0v). Prepare
  Zr=(2pWu/(k0v),H+H(5p−1)/(Xv)) and y=H(1−t0/X).
  ZrE meets this rail at Qr with x=2pW(ut+v)/(k0 V).
  Draw the vertical through Qr to the existing last horizontal to obtain R.
  This adds 1J+1P. The chart excludes 2pu=k0v; all tested k0=p, p≥3
  avoid it. The Lean projection lemma covers k0=p, not every chart choice.

## Decentered-arc transport, branch and radius

Let β=(p−1)sqrt((p−2)/(12p)), α=(5p+2)/(p−2),
q=sqrt(t²+2αt+1), so g=βq. Put

    m=H(1−1/X), G_y=H+Hα/X,
    λ=WXβ/(k0H), δ=Wβ sqrt(α²−1)/k0,
    Fr=(W/k0,m+δ), Gscale=(0,G_y).

If λ≠1, prepare the fixed homogeneous center
Zscale=(Wλ,(λ−1)G_y,λ−1). The join ZscaleE meets x=0 at
Escaled=(0,G_y+λ(E_y−G_y)). Its distance to Gscale is
λ EG=Wβ(t+α)/k0. If λ=1, use EG directly and omit that join.

Draw the circle centered at Fr with this radius. Its intersections with the
fixed horizontal y=m have abscissas

    W/k0 ± sqrt(radius²−δ²) = W/k0 ± Wβq/k0.

Select the **right** intersection Qr. Its x-coordinate is W(1+g)/k0.
The vertical through Qr meets the last chain horizontal at R. This uses
one reusable radical, one circle-line intersection operation (both roots
computed; right one selected), and one vertical transfer. The circle is
strictly transverse for p≥3,t>0 because q²>0.

Generic native totals: 3J+(2p+2)P+1C, compared with V20 AD5
3J+(2p+1)P+1C. Thus this concrete Transport-AD5 **adds one P**. At λ=1
it omits one J, but that does not imply a lower V20 expanded cost: P=2J+3C.
The radius-scaling center moves to infinity as λ approaches 1. The exact
λ=1 shortcut avoids the undefined finite-center construction; near it,
conditioning is still a separate issue.

## Cayley gauge: bounded radical, not a cost victory

Let z=(t−1)/(t+1) and γ=2(p+1)/(3p). Exact rationalization gives

    g/(t+1)=(p−1)/2 sqrt(1−γz²),
    κ=(1−z+(p−1)sqrt(1−γz²))/2,  r=−z.

One **fixed** unit circle, intersected with x=sqrt(γ)z, supplies the shared
radical as its upper ordinate. Since |z|<1 and p≥3,
1−γz²>(p−2)/(3p)≥1/9: this circle core is uniformly away from tangency.
Both κ and r are bounded in t for fixed p. Producing z requires a projective
stage and producing both slopes requires affine transfers; the distant input
E and the final report are not automatically well conditioned.

This establishes a promising bounded auxiliary construction, not a lower total
cost. No fixed-circle protocol was added to the public gallery on the strength
of the formula alone. A fixed circle has zero *mobile arcs* but still provides
a radical through a line-circle query; these metrics must not be conflated.

## Power-stage interface

The native telescope already draws E's horizontal. Binary exponentiation
returns E without that horizontal. Its use with the three nontrivial dual
transports therefore costs one additional P. The engine's research-only
binaryPower argument accounts for this. Power and correction optimizations
remain separate; saving a line by reuse depends on the interface actually
provided by the power stage.
