import LeanMath.Papers.V14CompressedAnalytic
import LeanMath.Papers.V14SeriesContact

/-! Theorem 13.1: the near-balanced reciprocal lift is the diagonal Padé function at R=1. -/
noncomputable section
namespace LeanMath.Papers.V14PadeTheorem
open Polynomial Filter Asymptotics
open scoped Topology
open LeanMath.Papers.V14PadeNormalization

/-- The classical type-(d,d) Padé condition for R^a at R=1.
Pairs need not be reduced; equality of rational functions is by cross products. -/
def IsDiagonal (a : ℝ) (d : ℕ) (A B : ℝ[X]) : Prop :=
  A.natDegree ≤ d ∧ B.natDegree ≤ d ∧ B.eval 1 ≠ 0 ∧
    (fun h : ℝ => A.eval (1+h)/B.eval (1+h)-(1+h)^a)
      =O[𝓝 0] (fun h => h^(2*d+1))

/-- Full analytic identification. `germ a` is analytic, equals the paper's
sqrt/artanh formula for positive z near zero, and takes value a at zero.
Specializing a=1/p gives Theorem 13.1 for every real p>1. -/
theorem near_balanced_diagonal (a : ℝ) (P Q : ℝ[X]) (m n : ℕ)
    (hP : P.natDegree ≤ m) (hQ : Q.natDegree ≤ n) (hbal : n=m ∨ n=m+1)
    (hQ0 : Q.eval 0 ≠ 0)
    (hmatch : (fun z : ℝ => V14CompressedAnalytic.germ a z-P.eval z/Q.eval z)
      =O[𝓝 0] (fun z => z^(m+n+1))) :
    IsDiagonal a (m+n+1) (residualNumerator P Q (m+n+1)) (residualDenominator P Q (m+n+1)) ∧
    AnalyticAt ℝ (fun R => (residualNumerator P Q (m+n+1)).eval R /
      (residualDenominator P Q (m+n+1)).eval R) 1 ∧
    ∀ A B : ℝ[X], IsDiagonal a (m+n+1) A B →
      residualNumerator P Q (m+n+1)*B=A*residualDenominator P Q (m+n+1) := by
  have hm := V14SeriesContact.analytic_matching _ _ (V14CompressedAnalytic.germ_represents a)
    P Q (m+n+1) hQ0 hmatch
  have hdN := V14Homography.clear_degree (V14Pade.numerator P Q) (m+n+1)
  have hdD := V14Homography.clear_degree (V14Pade.denominator P Q) (m+n+1)
  have hb0 : (residualDenominator P Q (m+n+1)).eval 1 ≠ 0 := by
    rw [(at_one P Q m n hP hQ hbal).2]
    exact mul_ne_zero hQ0 (pow_ne_zero _ (by norm_num))
  have hc := V14PadeContact.lifted_residual_contact a P Q m n hP hQ hbal hQ0 hm
  refine ⟨⟨hdN,hdD,hb0,hc⟩,analytic_at_one P Q m n hP hQ hbal hQ0,?_⟩
  intro A B hAB
  exact V14AnalyticUniqueness.rational_unique _ _ A B (m+n+1) (fun R : ℝ => R^a)
    hdN hdD hAB.1 hAB.2.1 hb0 hAB.2.2.1 hc hAB.2.2.2

/-- The equality is an identity at every common regular point, not just a local-order statement. -/
theorem identity_where_defined (a : ℝ) (P Q A B : ℝ[X]) (m n : ℕ)
    (hP : P.natDegree ≤ m) (hQ : Q.natDegree ≤ n) (hbal : n=m ∨ n=m+1)
    (hQ0 : Q.eval 0 ≠ 0)
    (hmatch : (fun z : ℝ => V14CompressedAnalytic.germ a z-P.eval z/Q.eval z)
      =O[𝓝 0] (fun z => z^(m+n+1)))
    (hAB : IsDiagonal a (m+n+1) A B) (R : ℝ)
    (hden : (residualDenominator P Q (m+n+1)).eval R ≠ 0) (hB : B.eval R ≠ 0) :
    (residualNumerator P Q (m+n+1)).eval R/(residualDenominator P Q (m+n+1)).eval R =
      A.eval R/B.eval R := by
  have hh := (near_balanced_diagonal a P Q m n hP hQ hbal hQ0 hmatch).2.2 A B hAB
  apply (div_eq_div_iff hden hB).mpr
  simpa only [eval_mul] using congrArg (Polynomial.eval R) hh

end LeanMath.Papers.V14PadeTheorem
