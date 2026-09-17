import LeanMath.Papers.CompactJacobian
import LeanMath.Papers.PosynomialSystem
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Compactness.Compact

/-! Compactness and uniform invertibility of the actual rectangular exponent hull.
This module bridges finite exponent matrices and continuous linear operators. -/
noncomputable section
namespace LeanMath.Papers.CompactPosynomial
open Set PosynomialSystem

def matrixOperator {n : ℕ} : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ]
    (Space n →L[ℝ] Space n) :=
  LinearMap.toContinuousLinearMap.toLinearMap.comp Matrix.toLin'.toLinearMap

theorem matrixOperator_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : Space n) :
    matrixOperator A v = A.mulVec v := rfl

def rowHull {n M : ℕ} (P : System n M) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {A | ∀ i, A i ∈ convexHull ℝ (Set.range (P.exponent i))}

theorem rowHull_compact {n M : ℕ} (P : System n M) : IsCompact (rowHull P) :=
  isCompact_pi_infinite (fun i => (Set.finite_range (P.exponent i)).isCompact_convexHull ℝ)

theorem rowHull_nonempty {n M : ℕ} [Nonempty (Fin M)] (P : System n M) :
    (rowHull P).Nonempty :=
  ⟨fun i => meanRow P i 0, fun i => mean_mem_hull P i 0⟩

theorem operatorHull_compact {n M : ℕ} (P : System n M) :
    IsCompact (matrixOperator '' rowHull P) :=
  (rowHull_compact P).image matrixOperator.continuous_of_finiteDimensional

theorem jacobian_eq_mean_operator {n M : ℕ} (P : System n M) (x : Space n) :
    jacobian P x = matrixOperator (fun i => meanRow P i x) := by
  ext v i
  rw [jacobian_apply]
  rfl

theorem uniform_lower_bound {n M : ℕ} [Nonempty (Fin M)] [Nontrivial (Space n)]
    (P : System n M) (hdet : ∀ A ∈ rowHull P, A.det ≠ 0) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ A ∈ rowHull P, ∀ v : Space n,
      σ * ‖v‖ ≤ ‖A.mulVec v‖ := by
  have hinj : ∀ T ∈ matrixOperator '' rowHull P, Function.Injective T := by
    rintro _ ⟨A,hA,rfl⟩
    have hu : IsUnit A := A.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr (hdet A hA))
    exact Matrix.mulVec_injective_iff_isUnit.mpr hu
  obtain ⟨σ,hσ,hb⟩ := CompactJacobian.uniform_lower_bound
    (matrixOperator '' rowHull P) (operatorHull_compact P)
    ((rowHull_nonempty P).image matrixOperator) hinj
  exact ⟨σ,hσ,fun A hA v => hb (matrixOperator A) ⟨A,hA,rfl⟩ v⟩

theorem jacobian_uniform_lower_bound {n M : ℕ} [Nonempty (Fin M)] [Nontrivial (Space n)]
    (P : System n M) (hdet : ∀ A ∈ rowHull P, A.det ≠ 0) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ x v : Space n, σ * ‖v‖ ≤ ‖jacobian P x v‖ := by
  obtain ⟨σ,hσ,hb⟩ := uniform_lower_bound P hdet
  refine ⟨σ,hσ,fun x v => ?_⟩
  rw [jacobian_eq_mean_operator]
  exact hb (fun i => meanRow P i x) (fun i => mean_mem_hull P i x) v

end LeanMath.Papers.CompactPosynomial
