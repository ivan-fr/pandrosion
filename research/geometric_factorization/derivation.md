# Geometric factorization of reciprocal-root corrections

This is post-V20 research. The manuscript and its frozen Lean snapshot are unchanged.
The baseline is `paper/reciprocal_geometry_v20/main.tex`, especially the common
report identity, the four support definitions, and its J/P/C convention.

## Exact identity and terminology

Put A=(W,H), P=(W,H(1-s)), L=H/(WX). A support of slope Lκ
and the line of slope Lr through P meet, provided κ−r≠0, at

    T = (W − WXs/(κ−r), H − Hsκ/(κ−r)).

Thus the horizontal readout is s+=s C, C=κ/(κ−r). When C≠0,
r=κ(1−1/C). Every nonzero pair representing a fixed nonzero C is a nonzero
multiple of any other such pair: h=κ/κ0. Multiplication by h≠0 cancels
in the quotient. A zero of h is not an admissible geometric equivalence,
even though algebraic cancellation might extend the scalar formula there.

The precise description is **homogeneous scaling freedom of the coefficient
pair [κ:r]**. “Gauge freedom” is a useful informal analogy. This is a projective
one-dimensional parameter, not a projective transformation of the entire drawing.
Changing h generally changes T.x, both angles, and auxiliary constructions;
T.y and the scalar readout are unchanged. Constructing h is not free.

For a>0, s=a exp(e), a=X^(-1/p), the correct error map is

    e+ = e + log C(exp(p e)).

Contact C(t)−t^(-1/p)=c(t−1)^m+O((t−1)^(m+1)), c≠0, gives order m.
Rational degree and number of radicals are different quantities.
Reciprocity is **C(1/t)=1/C(t)**, implying an odd logarithmic error map.
It removes even error terms; it does not impose a universal finite order bound.

## Baseline recovered from V20

All four use r0=1−t, M=(0,H(1−1/X)), E=(W,H(1−t/X)). Set

    N=p+1+(p−1)t, D=p−1+(p+1)t,
    U=2p((2p−1)t+p+1), V=(p+1)t+5p−1,
    Q=(p+1)t²+2(2p−1)(p+1)t+(2p−1)(p−1),
    g=(p−1)sqrt(((p−2)(t²+1)+(10p+4)t)/(12p)).

| V20 method | Order | C | κ0 | Source of κ0 | Native total J,P,C |
|---|---:|---|---|---|---|
| AK / Newton | 2 | p/(p−1+t) | p | fixed AK | 2, 2p+1, 0 |
| AD / Halley | 3 | N/D | N/2 | centered radius transfer and AD join | 3, 2p+1, 1 |
| Projective AD [2/1] | 4 | U/Q | U/V | projection ZE to a fixed rail, then AD | 4, 2p+1, 0 |
| Decentered AD5 | 5 | (1+g)/(t+g) | 1+g | decentered circle, lower branch, AD | 3, 2p+1, 1 |

Q−U=(t−1)V. Fixed preparation and intersection selection are excluded from
these mobile counts, exactly as in V20. A parallel is the V20 macro 2J+3C;
these are not Lemoine's elementary placements. The power chain alone costs
1J+(2p−1)P; the common report costs 1J+2P.

All original maps are positive and globally convergent on positive states in
the written V20 analysis; Newton and projective [2/1] may cross the root.
Only Halley and AD5 in this table are reciprocal. The written analytic AD5
convergence proof is not a complete Lean convergence theorem.

For AK fixed, the correct Halley transport is **2p(1−t)/N**. The proposed
(p+1)(1−t)/N is incorrect (except the irrelevant p=1 coincidence).

## A useful local angle calculation

The sine of the angle between the two directions after scaling by h is

    |Lh(κ0−r0)| / sqrt((1+(Lhκ0)²)(1+(Lhr0)²)).

For κ0 r0≠0 its maximum over |h|>0 occurs at
|h|=1/(L sqrt(|κ0 r0|)). Differentiating its square gives a numerator
proportional to 1−L⁴h⁴κ0²r0². This optimizes only one intersection angle;
it may introduce another radical, has no finite limit when r0=0, and does
not minimize preparation or full-circuit sensitivity. It is not a global
geometric optimizer.

## Normalization

X'=c^p X, s'=s/c preserves t. Consequently it cannot cure a t-dependent
negative radicand or pole. It can change raw-X-dependent centers M, G and Z.
The browser's calibrated X band and finite search over aspect ratios are
separate numerical aids, not optimality or uniform-conditioning theorems.
