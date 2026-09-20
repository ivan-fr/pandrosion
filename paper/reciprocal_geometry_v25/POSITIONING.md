# Appendix F (V25; argument retained from V24): the decentered arc under specified equivalences

This supplement gives the details of Appendix F without proposing another solver. All parameters below satisfy **real p > 2** unless an integer restriction is stated. These are written arguments with exact symbolic checks; they are **outside the Lean audit of Theorem 4.3**.

## Definitions and results

Use x=s/a, t=x^p, a=X^(−1/p), and e=log x. Set

```
S(t) = (p−2)(t²+1) + (10p+4)t
q(t) = sqrt(S(t)/(12p)), positive near t=1
Phi(t) = (1+(p−1)q(t))/(t+(p−1)q(t))
P(t,v) = (p−1)² S(t)(v−1)² − 12p(tv−1)².
```

The state map is A(x)=x Phi(x^p). Its error map is F(e)=e+log Phi(exp(pe)). The rational comparator is R(x)=x h22(x^p), with the h22 coefficients printed in the manuscript.

| Equivalence under consideration | Conclusion | Scope |
|---|---|---|
| Identity in the same logarithmic error | The arc, circle and rational Padé formulas differ. | Every real p>2; distinct fifth-order coefficients. |
| Independent invertible homographies of the correction's input and output | Cannot turn Phi into a rational correction. | Every real p>2; rationality is preserved by invertible rational substitutions. |
| Möbius conjugacy of the complete state maps | A is not conjugate to a rational state map, including R. | Integer p≥3 only. This includes a germ identity at the fixed point. |
| Diagonal quadratic Hermite–Padé/Shafer type (2,2,2) for t^(−1/p) | The arc is not that approximant in the stated normalization. | Every real p>2; its primitive implicit polynomial has contact six, whereas the specified type requires at least eight. |
| Real analytic local conjugacy | The arc and rational Padé error maps are conjugate. The arc and circle are not. | Every real p>2; regular coordinate changes fixing zero, near the root only. |
| Complex analytic local conjugacy | All three fifth-order germs are conjugate. | Local statement only; complex scaling removes the sign distinction. |
| Equivalence to every known algebraic solver under every transformation | Not established or excluded. | No exhaustive classification or historical priority claim. |

## Why homographies do not rationalize the arc

The discriminant of S as a polynomial in t is 96p(p+1), its leading coefficient is p−2 and S(0)=p−2. Thus it has two distinct nonzero complex roots. A square of a rational function has even multiplicity at every zero and pole, so S is not a square in C(t). A nonzero complex constant such as 12p does not affect this argument.

The unsquared correction formula gives

```
q(t) = (1−t Phi(t))/((p−1)(Phi(t)−1)).
```

This is an identity of meromorphic functions: division is allowed because Phi is not identically one. Indeed the explicit formula could equal one only at t=1. A removable singularity in the recovery formula at t=1 causes no difficulty. If Phi were rational, q would be rational, contradicting the simple roots of S.

Independent Möbius transformations U and V have rational inverses. If V∘Phi∘U were rational, then Phi=V^(-1)∘(V∘Phi∘U)∘U^(-1) would be rational as well. This is an input/output statement about the correction, not yet about the iterated state.

For **integer p≥3**, S(x^p) is a polynomial. Each of its zeros x0 is nonzero; its derivative there is p x0^(p−1) S'(x0^p), which is nonzero. Hence its 2p complex zeros are simple. If A(x) were rational, then Phi(x^p)=A(x)/x would be rational, and the recovery identity would make sqrt(S(x^p)/(12p)) rational. This is impossible. A Möbius conjugate of a rational map is rational. Even a local conjugacy identity by a Möbius map would express A as a rational germ; its recovered square root would square to S(x^p)/(12p) on an open set and therefore identically as rational functions, giving the same contradiction.

For noninteger real p, x^p is analytic locally at x=1 but is not a rational function of x. The above polynomial argument does not exclude Möbius conjugacy of the complete state maps for these parameters. We do not extend it beyond its proved domain.

## A concrete Shafer comparison, with the contact convention fixed

For f(t)=t^(−1/p), type (2,2,2) means a nonzero polynomial A(t)v²+B(t)v+C(t), each coefficient of degree at most two, for which substitution v=f(t) has a zero of order at least eight at t=1. This is the degree convention in [Cabay–Labahn, CS-89-09 (1989), equations (1.4)–(1.6)](https://cs.uwaterloo.ca/research/tr/1989/CS-89-09.pdf): the general exponent is n0+…+nk+k, here 2+2+2+2. The source explicitly relates quadratic forms to Shafer on printed page 2. This comparison does not rely on having accessed Shafer's original full text.

An independent binomial expansion in u=t−1 gives

```
P(1+u,(1+u)^(−1/p))
  = [(p−2)(p−1)²(p+1)(3p+1)/(60p⁴)] u⁶ + O(u⁷).
```

The coefficient is strictly positive for p>2. To rule out another polynomial with the same degree bounds defining this same branch, first observe that the coefficients of P are primitive in C[t]: a common divisor would divide P(t,1)=−12p(t−1)², but the coefficient of v² at t=1 is 12p²(p−2)≠0. Second, the discriminant in v is 48p(p−1)²(t−1)² S(t), a nonsquare in C(t). Thus P is irreducible over C(t), and primitivity makes it irreducible in C[t,v]. Any other polynomial Q vanishing on this branch is divisible by P. Since P has degree two in each variable, the same separate degree bounds force Q to be a constant multiple. Its contact is again six, not eight.

The double root at (1,1) matters. One cannot simply infer an eighth-order explicit branch from the implicit contact condition. For our branch, ∂P/∂v evaluated on the target begins −24p(p−1)u. Dividing the leading residual by this first-order derivative yields fifth-order correction error, consistent with the manuscript's coefficient after t=exp(pe). No new Shafer iteration or convergence theorem is introduced here. We do not claim exclusion of other types, other algebraic families, or a changed approximation target.

## Why local analytic conjugacy does exist

For fixed p>2, exp(pe), the positive square root at S(1)/(12p)=1, and the logarithm at Phi(1)=1 extend holomorphically near zero. Hence the arc's error map is an analytic germ. The rational Padé and selected circle maps are analytic there as well. Their leading terms are

```
arc:      cA e⁵,   cA = (p−2)(p²−1)(3p+1)/1440 > 0
rational: cR e⁵,   cR = (p²−1)(4p²−1)/720 > 0
circle:   cC e⁵,   cC = −(p²−1)(p²−4)/720 < 0.
```

The classical one-variable Böttcher theorem supplies a germ phi tangent to the identity with phi∘F=cF phi⁵. See [Buff–Epstein–Koch, *Böttcher coordinates*, Introduction](https://people.math.harvard.edu/~kochs/bottcher.pdf). Its application here is our inference from the verified analytic hypotheses and coefficients, not a claim that this source studies our solvers.

These tangent-to-identity coordinates can be chosen real. For completeness, uniqueness follows by comparing two such coordinates: their quotient by composition is a tangent-to-identity germ psi commuting with z↦c z⁵. If psi(z)=z+b z^m+… has a first nonzero higher term, m>1, the commuting identity has a nonzero term 5cb z^(m+4) on one side, while the other side's first possible correction has degree 5m>m+4. Thus b=0, a contradiction. Complex conjugation of a normalized Böttcher coordinate is another one for a real germ; uniqueness makes them equal.

Choose the positive real number lambda with

```
lambda⁴ = cA/cR = (p−2)(3p+1)/(2(4p²−1)).
```

Then h=phiR^(-1)∘(lambda·)∘phiA satisfies h∘Farc=Frational∘h. It is a real analytic local diffeomorphism. Conversely, comparing leading terms in any regular real analytic conjugacy h∘F=G∘h gives lambda cF=cG lambda⁵, so the sign of cF is invariant. The circle's negative coefficient excludes such a real conjugacy with the arc. Over C a fourth root of a negative ratio exists, removing that obstruction.

This is not an executable conversion with a counted number of joins. The normalizing coordinates depend on the maps and, when expressed in the original state s, use the root normalization a. The local theorem does not give a continuation on the full positive axis, identify the geometric supports, preserve branch predicates, or preserve the cost inventory. The paper's constructive contribution does not depend on a new local conjugacy class.

## Reproduction and boundaries

Run `python3 paper/reciprocal_geometry_v25/src/positioning/verify.py` from the repository root. It checks the elimination, discriminants, primitive-coefficient identities, exact residual coefficients, fifth-order consistency and scaling law. Integer square-freeness examples supplement the universal written argument; they do not replace it. The existing uniform verifier independently derives all three fifth-order coefficients.

The audit of 69 Lean declarations still concerns the scalar circle theorem. Neither this positioning supplement nor Böttcher's existence theorem has been added to that audit. The literature ledger records access to the original sources and expressly leaves broader equivalence and historical-priority questions open.
