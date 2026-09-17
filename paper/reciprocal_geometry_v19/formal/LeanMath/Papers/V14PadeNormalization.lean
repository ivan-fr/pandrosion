import LeanMath.Papers.V14Homography
import LeanMath.Papers.V14RootSeries
import Mathlib.Analysis.Analytic.Polynomial

/-! Normalization and analyticity of the reciprocal lift after returning to R. -/
noncomputable section
namespace LeanMath.Papers.V14PadeNormalization
open Polynomial
open LeanMath.Papers.V14Pade LeanMath.Papers.V14Homography

def residualNumerator (P Q : ℝ[X]) (d : ℕ) := clear (numerator P Q) d
def residualDenominator (P Q : ℝ[X]) (d : ℕ) := clear (denominator P Q) d

theorem at_one (P Q : ℝ[X]) (m n : ℕ)
    (hP : P.natDegree ≤ m) (hQ : Q.natDegree ≤ n) (hbal : n=m ∨ n=m+1) :
    (residualNumerator P Q (m+n+1)).eval 1 = Q.eval 0*2^(m+n+1) ∧
    (residualDenominator P Q (m+n+1)).eval 1 = Q.eval 0*2^(m+n+1) := by
  obtain ⟨hnum,hden⟩ := lifted_degrees P Q m n hP hQ hbal
  constructor
  · rw [residualNumerator,clear_eval _ _ hnum 1 (by norm_num)]
    norm_num [numerator]
  · rw [residualDenominator,clear_eval _ _ hden 1 (by norm_num)]
    norm_num [denominator]

/-- The usual Padé normalization excludes a pole at the expansion point R=1. -/
theorem analytic_at_one (P Q : ℝ[X]) (m n : ℕ)
    (hP : P.natDegree ≤ m) (hQ : Q.natDegree ≤ n) (hbal : n=m ∨ n=m+1)
    (hQ0 : Q.eval 0 ≠ 0) :
    AnalyticAt ℝ (fun R => (residualNumerator P Q (m+n+1)).eval R /
      (residualDenominator P Q (m+n+1)).eval R) 1 := by
  have hden : (residualDenominator P Q (m+n+1)).eval 1 ≠ 0 := by
    rw [(at_one P Q m n hP hQ hbal).2]
    exact mul_ne_zero hQ0 (pow_ne_zero _ (by norm_num))
  exact ((AnalyticOnNhd.eval_polynomial (𝕜:=ℝ) (residualNumerator P Q (m+n+1))) 1 (by trivial)).div
    ((AnalyticOnNhd.eval_polynomial (𝕜:=ℝ) (residualDenominator P Q (m+n+1))) 1 (by trivial)) hden

theorem quotient_at_one (P Q : ℝ[X]) (m n : ℕ)
    (hP : P.natDegree ≤ m) (hQ : Q.natDegree ≤ n) (hbal : n=m ∨ n=m+1)
    (hQ0 : Q.eval 0 ≠ 0) :
    (residualNumerator P Q (m+n+1)).eval 1 /
      (residualDenominator P Q (m+n+1)).eval 1 = 1 := by
  rw [(at_one P Q m n hP hQ hbal).1,(at_one P Q m n hP hQ hbal).2]
  exact div_self (mul_ne_zero hQ0 (pow_ne_zero _ (by norm_num)))

/-- These homogeneous polynomials evaluate to precisely the reciprocal lift. -/
theorem residual_quotient (P Q : ℝ[X]) (m n : ℕ)
    (hP : P.natDegree ≤ m) (hQ : Q.natDegree ≤ n) (hbal : n=m ∨ n=m+1)
    (R : ℝ) (hR : R+1 ≠ 0) :
    (residualNumerator P Q (m+n+1)).eval R /
      (residualDenominator P Q (m+n+1)).eval R =
      (numerator P Q).eval ((R-1)/(R+1))/(denominator P Q).eval ((R-1)/(R+1)) := by
  obtain ⟨hn,hd⟩ := lifted_degrees P Q m n hP hQ hbal
  exact quotient_eval _ _ _ hn hd R hR

end LeanMath.Papers.V14PadeNormalization
