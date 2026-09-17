import LeanMath.Papers.V14AnalyticLocal
import LeanMath.Papers.V14OddRemainder

/-! The strengthened local expansion in Theorem 9.3, for the actual corrections. -/
noncomputable section
namespace LeanMath.Papers.V14LocalRemainder
open Filter Asymptotics
open scoped Topology
open LeanMath.Papers.V14Local

/-- The next possible error term has degree m+2, since the analytic error is odd. -/
theorem exact_local_remainder (i : Index) (p : ℝ) (hp : 2 < p) :
    (fun e : ℝ => rootLogError i p e -
      (coefficient i (V14Defect.a p)*p^(order i)/2^(order i-1))*e^(order i))
      =O[𝓝 0] (fun e => e^(order i+2)) := by
  exact V14OddRemainder.odd_leading_remainder _ _ _
    (by cases i <;> decide)
    (V14AnalyticLocal.error_analytic i p hp)
    (fun e => V14Cell.error_odd i p e hp)
    (V14Cell.error_zero i p hp)
    (exact_local_order i p hp)

/-- Analyticity, positivity, reciprocity and the full printed local expansion. -/
theorem theorem_9_3 (i : Index) (p : ℝ) (hp : 2 < p) :
    AnalyticAt ℝ (correction i p) 1 ∧
    (∀ᶠ R : ℝ in 𝓝 1, 0 < correction i p R) ∧
    (∀ R : ℝ, 0 < R → correction i p R⁻¹ = (correction i p R)⁻¹) ∧
    0 < coefficient i (V14Defect.a p)*p^(order i)/2^(order i-1) ∧
    (fun e : ℝ => rootLogError i p e -
      (coefficient i (V14Defect.a p)*p^(order i)/2^(order i-1))*e^(order i))
      =O[𝓝 0] (fun e => e^(order i+2)) := by
  exact ⟨V14AnalyticLocal.correction_analytic i p hp,
    V14AnalyticLocal.correction_positive_near_one i p hp,
    fun R hR => correction_reciprocal i p R hp hR,
    local_constant_positive i p hp, exact_local_remainder i p hp⟩

end LeanMath.Papers.V14LocalRemainder
