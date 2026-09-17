import LeanMath.Papers.CompactPosynomial
import LeanMath.Papers.CubicReversion
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

noncomputable section
-- Nested operator spaces require deeper instance synthesis; this changes no theorem assumptions.
set_option maxSynthPendingDepth 3
namespace LeanMath.Papers.PosynomialDifferential
open Set PosynomialSystem CompactPosynomial

variable {n M : ℕ} [Nonempty (Fin M)] (P : System n M)

theorem smooth_logPartition : ContDiff ℝ ⊤ (logPartition P) := by
  apply contDiff_pi.mpr
  intro i
  have hp : ContDiff ℝ ⊤ (partition P i) := by
    unfold partition term
    fun_prop
  exact hp.log (fun x => (partition_pos P i x).ne')

theorem fderiv_eq_jacobian : fderiv ℝ (logPartition P) = jacobian P := by
  funext x
  exact (hasFDerivAt_logPartition P x).fderiv

theorem smooth_jacobian : ContDiff ℝ ⊤ (jacobian P) := by
  rw [← fderiv_eq_jacobian]
  exact (smooth_logPartition P).fderiv_right (by simp)

def hessian (x : Space n) : Space n →L[ℝ] Space n →L[ℝ] Space n :=
  fderiv ℝ (jacobian P) x

def third (x : Space n) : Space n →L[ℝ] Space n →L[ℝ] Space n →L[ℝ] Space n :=
  fderiv ℝ (hessian P) x

theorem smooth_hessian : ContDiff ℝ ⊤ (hessian P) :=
  (smooth_jacobian P).fderiv_right (by simp)

theorem continuous_third : Continuous (third P) :=
  ((smooth_hessian P).fderiv_right (by simp : (⊤ : WithTop ℕ∞) + 1 ≤ ⊤)).continuous

theorem third_bounded_on_closedBall (z : Space n) (r : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ Metric.closedBall z r, ‖third P x‖ ≤ C := by
  obtain ⟨C,hC⟩ := (isCompact_closedBall z r).exists_bound_of_continuousOn
    (continuous_third P).continuousOn
  exact ⟨|C|+1, by positivity, fun x hx => (hC x hx).trans (by linarith [le_abs_self C])⟩

theorem third_direction_bounded_on_closedBall (z : Space n) (r : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ Metric.closedBall z r, ∀ v : Space n,
      ‖third P x v v v‖ ≤ C * ‖v‖^3 := by
  obtain ⟨C,hC,hb⟩ := third_bounded_on_closedBall P z r
  refine ⟨C,hC,fun x hx v => ?_⟩
  calc
    ‖third P x v v v‖ ≤ ‖third P x v v‖ * ‖v‖ := (third P x v v).le_opNorm v
    _ ≤ (‖third P x‖ * ‖v‖ * ‖v‖) * ‖v‖ :=
      mul_le_mul_of_nonneg_right ((third P x).le_opNorm₂ v v) (norm_nonneg v)
    _ ≤ C * ‖v‖^3 := by nlinarith [mul_le_mul_of_nonneg_right (hb x hx) (pow_nonneg (norm_nonneg v) 3)]

theorem jacobian_bijective (hdet : ∀ A ∈ rowHull P, A.det ≠ 0) (x : Space n) :
    Function.Bijective (jacobian P x) := by
  let A : Matrix (Fin n) (Fin n) ℝ := fun i => meanRow P i x
  have hu : IsUnit A := A.isUnit_iff_isUnit_det.mpr
    (isUnit_iff_ne_zero.mpr (hdet A (fun i => mean_mem_hull P i x)))
  rw [jacobian_eq_mean_operator]
  exact ⟨Matrix.mulVec_injective_iff_isUnit.mpr hu,
    Matrix.mulVec_surjective_iff_isUnit.mpr hu⟩

def jacobianEquiv (hdet : ∀ A ∈ rowHull P, A.det ≠ 0) (x : Space n) :
    Space n ≃L[ℝ] Space n :=
  ContinuousLinearEquiv.ofBijective (jacobian P x)
    (LinearMap.ker_eq_bot.mpr (jacobian_bijective P hdet x).1)
    (LinearMap.range_eq_top.mpr (jacobian_bijective P hdet x).2)

theorem jacobianEquiv_apply (hdet : ∀ A ∈ rowHull P, A.det ≠ 0) (x v : Space n) :
    jacobianEquiv P hdet x v = jacobian P x v := rfl

theorem open_logPartition (hdet : ∀ A ∈ rowHull P, A.det ≠ 0) :
    IsOpenMap (logPartition P) := by
  apply isOpenMap_of_hasStrictFDerivAt_equiv (f' := jacobianEquiv P hdet)
  intro x
  exact (smooth_logPartition P).contDiffAt.hasStrictFDerivAt'
    (hasFDerivAt_logPartition P x) (by simp)

end LeanMath.Papers.PosynomialDifferential
