import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-! A finite-dimensional maximum principle for Z-matrices with a positive witness.
The signs off the diagonal are essential and occur in every applicable statement. -/
noncomputable section
namespace LeanMath.Papers.MMatrixSign
open Finset Matrix
open scoped BigOperators

variable {n : ℕ}

theorem maximum_principle (A : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (hZ : ∀ i j, i ≠ j → A i j ≤ 0)
    (hAw : ∀ i, 0 < A.mulVec w i) (x : Fin n → ℝ)
    (hAx : ∀ i, 0 ≤ A.mulVec x i) : ∀ i, 0 ≤ x i := by
  intro j
  by_contra! hj
  obtain ⟨i,_,hmin⟩ := Finset.exists_min_image Finset.univ
    (fun k => x k / w k) ⟨j, Finset.mem_univ j⟩
  let α := x i / w i
  have hα : α < 0 := (hmin j (Finset.mem_univ j)).trans_lt (div_neg_of_neg_of_pos hj (hw j))
  have hxi : α * w i = x i := by dsimp [α]; field_simp [ne_of_gt (hw i)]
  have hrow : ∀ k, A i k * x k ≤ α * (A i k * w k) := by
    intro k
    by_cases hk : i = k
    · subst k
      rw [← hxi]
      ring_nf
      exact le_rfl
    · have hratio : α * w k ≤ x k := (le_div_iff₀ (hw k)).mp (hmin k (Finset.mem_univ k))
      have hh := mul_le_mul_of_nonpos_left hratio (hZ i k hk)
      nlinarith
  have hs : A.mulVec x i ≤ α * A.mulVec w i := by
    change (∑ k, A i k * x k) ≤ α * ∑ k, A i k * w k
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun k _ => hrow k)
  have hn := mul_neg_of_neg_of_pos hα (hAw i)
  linarith [hAx i]

theorem mulVec_injective (A : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (hZ : ∀ i j, i ≠ j → A i j ≤ 0)
    (hAw : ∀ i, 0 < A.mulVec w i) : Function.Injective A.mulVec := by
  intro x y hxy
  have hzero : A.mulVec (x-y) = 0 := by simp [Matrix.mulVec_sub, hxy]
  have hpos := maximum_principle A w hw hZ hAw (x-y) (by simp [hzero])
  have hneg := maximum_principle A w hw hZ hAw (-(x-y)) (by
    simp only [Matrix.mulVec_neg, hzero, Pi.zero_apply, Pi.neg_apply, neg_zero, le_refl,
      implies_true])
  funext i
  have hp := hpos i
  have hn := hneg i
  simp only [Pi.sub_apply, Pi.neg_apply] at hp hn
  linarith

theorem invertible_of_positive_witness (A : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (hZ : ∀ i j, i ≠ j → A i j ≤ 0)
    (hAw : ∀ i, 0 < A.mulVec w i) : IsUnit A :=
  Matrix.mulVec_injective_iff_isUnit.mp (mulVec_injective A w hw hZ hAw)

theorem inverse_maps_nonneg (A : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (hZ : ∀ i j, i ≠ j → A i j ≤ 0)
    (hAw : ∀ i, 0 < A.mulVec w i) (b : Fin n → ℝ) (hb : ∀ i, 0 ≤ b i) :
    ∀ i, 0 ≤ A⁻¹.mulVec b i := by
  have hd := A.isUnit_iff_isUnit_det.mp (invertible_of_positive_witness A w hw hZ hAw)
  apply maximum_principle A w hw hZ hAw
  simpa only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hd, Matrix.one_mulVec] using hb

theorem inverse_nonneg (A : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (hZ : ∀ i j, i ≠ j → A i j ≤ 0)
    (hAw : ∀ i, 0 < A.mulVec w i) : ∀ i j, 0 ≤ A⁻¹ i j := by
  intro i j
  have h := inverse_maps_nonneg A w hw hZ hAw (Pi.single j 1)
    (by intro k; simp [Pi.single_apply]; split_ifs <;> norm_num) i
  simpa only [Matrix.mulVec_single_one, Matrix.col, Matrix.transpose_apply] using h

theorem positive_witness_of_inverse_nonneg (A : Matrix (Fin n) (Fin n) ℝ)
    (hunit : IsUnit A) (hinv : ∀ i j, 0 ≤ A⁻¹ i j) :
    ∃ w : Fin n → ℝ, (∀ i, 0 < w i) ∧ (∀ i, 0 < A.mulVec w i) := by
  have hd := A.isUnit_iff_isUnit_det.mp hunit
  let w := A⁻¹.mulVec (fun _ => 1)
  have hAw : A.mulVec w = fun _ => 1 := by
    simp only [w, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hd, Matrix.one_mulVec]
  refine ⟨w, ?_, fun i => by rw [hAw]; norm_num⟩
  intro i
  by_contra! hwi
  have hwrow : w i = ∑ j, A⁻¹ i j := by simp [w, Matrix.mulVec, dotProduct]
  have hzero : ∀ j, A⁻¹ i j = 0 := by
    intro j
    have hs := Finset.single_le_sum (fun k _ => hinv i k) (Finset.mem_univ j)
    rw [← hwrow] at hs
    linarith [hinv i j]
  have he := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i i)
    (Matrix.nonsing_inv_mul A hd)
  simp [Matrix.mul_apply, hzero] at he

/-- Exact witness/inverse-positivity criterion for a real Z-matrix. -/
theorem positive_witness_iff (A : Matrix (Fin n) (Fin n) ℝ)
    (hZ : ∀ i j, i ≠ j → A i j ≤ 0) :
    (∃ w : Fin n → ℝ, (∀ i, 0 < w i) ∧ (∀ i, 0 < A.mulVec w i)) ↔
      IsUnit A ∧ (∀ i j, 0 ≤ A⁻¹ i j) := by
  constructor
  · rintro ⟨w,hw,hAw⟩
    exact ⟨invertible_of_positive_witness A w hw hZ hAw,
      inverse_nonneg A w hw hZ hAw⟩
  · rintro ⟨hu,hi⟩
    exact positive_witness_of_inverse_nonneg A hu hi

end LeanMath.Papers.MMatrixSign
