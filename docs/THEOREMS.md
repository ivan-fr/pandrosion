# Audited mathematics

- PROVED: recursive bilateral factorization, alternating recursion and local orders 3,9,27,81 for p>2; see `theory/recursive_bilateral.md`.
- PROVED: near-balanced reciprocal Padé lift identity with its exact scope; see `theory/pade_audit.md`.
- PROVED: spectral certificates below. Numerical speed is a separate question.

## Perron/Collatz

For any finite complex matrix A and B=|A|, |A^k|≤B^k entrywise, so the spectral-radius formula yields rho(A)≤rho(B). For x_i>0, diagonal similarity D^(-1)BD has row sums (Bx)_i/x_i. Its spectral radius is bounded above by their maximum U. Since Bx≥Lx, iteration and the same spectral-radius formula yield rho(B)≥L (the L=0 case is immediate). Irreducibility is not required for these bounds.

For Hermitian G, A=G−I has lambda_max(G)≤1+rho(A)≤1+U. Thus U<1 suffices. For interval entries, form a nonnegative upper majorant of |G−I| and rigorously verify Bx<x; a floating point approximate Perron vector may suggest x but cannot certify it. Raw power iteration need not strictly contract the interval every step: B=[[0,2],[1,0]] with x=(1,1) cycles row ratios {1,2}. Positivity/aperiodicity or a shift is needed for a convergence claim.

## Trace-power enclosure

The spectral theorem gives trace(G^(2m))=Σ λ_i^(2m)≥lambda_max(G)^(2m) for every Hermitian G (PSD is sufficient but unnecessary). Hence upper(trace(G^(2m)))<2^(2m) implies lambda_max(G)<2. Equivalently compute trace((G/2)^q)<1 for even q. For H=G/2, trace(H^(2r))=||H^r||_F². Bounding this sum of squares avoids another interval matrix multiplication.

A box of independently variable symmetric entries need not itself consist only of PSD matrices. That causes no soundness problem for the even-power test. The actual translation matrices are contained in it and are Hermitian. For complex Hermitian matrices use squared complex moduli in the Frobenius formula; the implementation in this continuation targets real even-kernel matrices only.

## Cayley coordinate: exact negative result for classification alone

f(lambda)=(lambda−2)/(lambda+2) is strictly increasing on lambda>−2, with derivative 4/(lambda+2)². For a spectral enclosure [L,U] in that domain, U<2 iff f(U)<0. Applying the coordinate to an unchanged enclosure cannot prune any additional boxes. A benefit requires a tighter enclosure or a cheaper branch-specific functional calculation. No such benefit is established merely by relabelling endpoints.

## Soundness boundary for integration

lambda_max(G)<2 is not a proof of the upstream weighted pair-energy inequality F(g)≥epsilon. A contractor may classify the spectral branch, but may not replace that verifier's acceptance predicate. No missing bridge functional is assumed.

## Rigorous midpoint recentering

Write each actual real symmetric matrix as M+E, with M the exact dyadic midpoint of its entry balls. Let δ bound every absolute row sum of E. Symmetry implies ||E||₂≤δ, hence λmax(G)≤λmax(M)+δ. Therefore 2[upper(tr((M/2)^q))]^(1/q)+δ<2 is sufficient. This avoids propagating the entire entry radius through every power. The ball representation of an exact dyadic midpoint has zero radius.

For the independent replay, interval LDL proves 2I−M−δI positive definite. The same perturbation bound then proves G<2I for every original matrix in the box. This is a different numerical sufficient condition from the production trace cascade and reuses the same certified kernel implementation.

For Chebyshev degree d, b=19/10 and c>b, define P(t)=T_d(2t/b−1)/T_d(2c/b−1). For t≥c, T_d is positive increasing on [1,∞), so P(t)²≥1. Thus ||P(M)||F²<1 rules out an eigenvalue ≥c. Direct boxes use c=2; midpoint boxes use c=2−δ and Weyl. Recentring resolves interval explosion at a cost; it is not automatically a faster classifier.

## Lean audit

`lean/BilateralCore.lean` independently checks the core log algebra over an abstract field and the Cayley inverse in characteristic zero. All three declarations have only propext, Classical.choice and Quot.sound as axioms. This does not assert a full Lean formalization of the real-analytic theorem.

## Signed small-block continuation

See `theory/small_block_defect.md` and `theory/SMALL_BLOCK_RESULTS.md` for the exact three/four-point defect formula, signed triangle/cubic moment criterion, and a rigorously bounded direct-assembly family. Three strict local gains and two family-ceiling witnesses were certified by Arb and independently replayed. The Lean companion checks the triangle algebra. No density improvement follows from those local gains alone.
