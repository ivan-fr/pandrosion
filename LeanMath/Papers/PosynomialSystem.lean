import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Convex.Combination
import LeanMath.Papers.MultivariateGuard

/-! Finite positive exponent laws; the Jacobian rows are separate tilted means.
No common scalar potential, covariance invertibility, or P-matrix assumption is used. -/
noncomputable section
namespace LeanMath.Papers.PosynomialSystem
open Finset Set
open scoped BigOperators NNReal

abbrev Space (n : ℕ) := Fin n → ℝ

def linearForm {n : ℕ} (a : Space n) : Space n →L[ℝ] ℝ :=
  ∑ j, a j • ContinuousLinearMap.proj j

theorem linearForm_apply {n : ℕ} (a x : Space n) :
    linearForm a x = ∑ j, a j * x j := by
  simp [linearForm]

theorem linearForm_norm_le {n : ℕ} (a : Space n) :
    ‖linearForm a‖ ≤ ∑ j, |a j| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  intro v
  rw [linearForm_apply]
  calc
    ‖∑ j, a j * v j‖ ≤ ∑ j, ‖a j * v j‖ := norm_sum_le _ _
    _ ≤ ∑ j, |a j| * ‖v‖ := Finset.sum_le_sum (fun j _ => by
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) (abs_nonneg _))
    _ = (∑ j, |a j|) * ‖v‖ := (Finset.sum_mul _ _ _).symm

theorem row_norm_le {n : ℕ} (a : Space n) (i : Fin n) (η : ℝ) :
    ‖(ContinuousLinearMap.proj i : Space n →L[ℝ] ℝ) - η • linearForm a‖ ≤
      ∑ j, |(if j=i then 1 else 0) - η*a j| := by
  have he : (ContinuousLinearMap.proj i : Space n →L[ℝ] ℝ) - η • linearForm a =
      linearForm (fun j => (if j=i then 1 else 0) - η*a j) := by
    ext v
    simp [linearForm_apply, Finset.sum_sub_distrib, sub_mul, Finset.mul_sum, mul_assoc]
  rw [he]
  exact linearForm_norm_le _

/-- The original diagonal-dominance hypothesis implies the finite support certificate. -/
theorem row_norm_of_dominance {n : ℕ} (a : Space n) (i : Fin n) (η m : ℝ)
    (hη : 0 ≤ η) (hdiag : η * a i ≤ 1)
    (hdom : m ≤ a i - ∑ j ∈ Finset.univ.erase i, |a j|) :
    ‖(ContinuousLinearMap.proj i : Space n →L[ℝ] ℝ) - η • linearForm a‖ ≤ 1-η*m := by
  apply (row_norm_le a i η).trans
  have he : (∑ j ∈ Finset.univ.erase i, |(if j=i then 1 else 0) - η*a j|) =
      η * ∑ j ∈ Finset.univ.erase i, |a j| := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [hji, abs_mul, abs_of_nonneg hη]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), he]
  simp only [ite_true, abs_of_nonneg (sub_nonneg.mpr hdiag)]
  have hd := mul_le_mul_of_nonneg_left hdom hη
  nlinarith

structure System (n M : ℕ) where
  exponent : Fin n → Fin M → Space n
  coeff : Fin n → Fin M → ℝ
  coeff_pos : ∀ i t, 0 < coeff i t

variable {n M : ℕ} (P : System n M)

def term (i : Fin n) (t : Fin M) (x : Space n) :=
  P.coeff i t * Real.exp (linearForm (P.exponent i t) x)

def partition (i : Fin n) (x : Space n) := ∑ t, (term P) i t x

def logPartition (x : Space n) (i : Fin n) := Real.log ((partition P) i x)

def tilt (i : Fin n) (x : Space n) (t : Fin M) :=
  (term P) i t x / (partition P) i x

def meanRow (i : Fin n) (x : Space n) : Space n :=
  ∑ t, (tilt P) i x t • P.exponent i t

def rowDerivative (i : Fin n) (x : Space n) : Space n →L[ℝ] ℝ :=
  ∑ t, (tilt P) i x t • linearForm (P.exponent i t)

def jacobian (x : Space n) : Space n →L[ℝ] Space n :=
  ContinuousLinearMap.pi (fun i => (rowDerivative P) i x)

theorem term_pos (i : Fin n) (t : Fin M) (x : Space n) : 0 < (term P) i t x :=
  mul_pos (P.coeff_pos i t) (Real.exp_pos _)

theorem partition_pos [Nonempty (Fin M)] (i : Fin n) (x : Space n) :
    0 < (partition P) i x := by
  exact Finset.sum_pos (fun t _ => (term_pos P) i t x) Finset.univ_nonempty

theorem tilt_nonneg [Nonempty (Fin M)] (i : Fin n) (x : Space n) (t : Fin M) :
    0 ≤ (tilt P) i x t :=
  (div_pos ((term_pos P) i t x) ((partition_pos P) i x)).le

theorem tilt_sum [Nonempty (Fin M)] (i : Fin n) (x : Space n) :
    ∑ t, (tilt P) i x t = 1 := by
  simp only [tilt, div_eq_mul_inv, ← Finset.sum_mul]
  exact mul_inv_cancel₀ (ne_of_gt ((partition_pos P) i x))

theorem mean_mem_hull [Nonempty (Fin M)] (i : Fin n) (x : Space n) :
    (meanRow P) i x ∈ convexHull ℝ (Set.range (P.exponent i)) := by
  apply (convex_convexHull ℝ _).sum_mem
  · exact fun t _ => (tilt_nonneg P) i x t
  · exact (tilt_sum P) i x
  · exact fun t _ => subset_convexHull ℝ _ (Set.mem_range_self t)

/-- The full row-mean matrix lies in the convex hull of all independent row selections. -/
theorem mean_matrix_mem_hull [Nonempty (Fin M)] (x : Space n) :
    (fun i => (meanRow P) i x) ∈ convexHull ℝ
      (Set.univ.pi (fun i => Set.range (P.exponent i))) := by
  exact mem_convexHull_pi (fun i _ => (mean_mem_hull P) i x)

theorem hasFDerivAt_partition (i : Fin n) (x : Space n) :
    HasFDerivAt ((partition P) i)
      (∑ t, (term P) i t x • linearForm (P.exponent i t)) x := by
  unfold partition
  have ht : ∀ t, HasFDerivAt (term P i t)
      (term P i t x • linearForm (P.exponent i t)) x := by
    intro t
    convert! (((linearForm (P.exponent i t)).hasFDerivAt).exp.const_mul
      (P.coeff i t)) using 1 <;> simp [term, smul_smul]
  convert! HasFDerivAt.sum (u := Finset.univ) (fun t _ => ht t) using 1
  ext y
  simp

theorem hasFDerivAt_log_row [Nonempty (Fin M)] (i : Fin n) (x : Space n) :
    HasFDerivAt (fun y => (logPartition P) y i) ((rowDerivative P) i x) x := by
  have h := ((hasFDerivAt_partition P) i x).log (ne_of_gt ((partition_pos P) i x))
  simpa only [logPartition, rowDerivative, tilt, smul_sum, smul_smul,
    div_eq_mul_inv, mul_comm] using h

theorem hasFDerivAt_logPartition [Nonempty (Fin M)] (x : Space n) :
    HasFDerivAt (logPartition P) ((jacobian P) x) x := by
  exact hasFDerivAt_pi.mpr (fun i => (hasFDerivAt_log_row P) i x)

theorem jacobian_apply (x v : Space n) (i : Fin n) :
    (jacobian P) x v i = ∑ j, (meanRow P) i x j * v j := by
  simp only [jacobian, ContinuousLinearMap.pi_apply, rowDerivative,
    _root_.sum_apply, smul_apply, smul_eq_mul,
    linearForm_apply, meanRow, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  ext j
  congr 1
  ext t
  ring

/-- A finite support test controls the derivative everywhere, despite distinct row tilts. -/
theorem jacobian_contraction_of_support [Nonempty (Fin M)] (η : ℝ) (q : ℝ≥0)
    (hb : ∀ i t,
      ‖(ContinuousLinearMap.proj i : Space n →L[ℝ] ℝ) -
        η • linearForm (P.exponent i t)‖ ≤ q) (x : Space n) :
    ‖ContinuousLinearMap.id ℝ (Space n) - η • jacobian P x‖ ≤ q := by
  apply ContinuousLinearMap.opNorm_le_bound _ q.coe_nonneg
  intro v
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg q.coe_nonneg (norm_nonneg v))).mpr
  intro i
  have he : (ContinuousLinearMap.proj i : Space n →L[ℝ] ℝ) - η • rowDerivative P i x =
      ∑ t, tilt P i x t • ((ContinuousLinearMap.proj i : Space n →L[ℝ] ℝ) -
        η • linearForm (P.exponent i t)) := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul,
      tilt_sum P i x, one_smul, rowDerivative, smul_sum, smul_smul]
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    rw [mul_comm]
  change ‖((ContinuousLinearMap.proj i : Space n →L[ℝ] ℝ) -
    η • rowDerivative P i x) v‖ ≤ (q : ℝ) * ‖v‖
  rw [he, _root_.sum_apply]
  calc
    ‖∑ t, (tilt P i x t • ((ContinuousLinearMap.proj i : Space n →L[ℝ] ℝ) -
      η • linearForm (P.exponent i t))) v‖ ≤
      ∑ t, ‖(tilt P i x t • ((ContinuousLinearMap.proj i : Space n →L[ℝ] ℝ) -
      η • linearForm (P.exponent i t))) v‖ := norm_sum_le _ _
    _ ≤ ∑ t, tilt P i x t * ((q : ℝ) * ‖v‖) := by
      apply Finset.sum_le_sum
      intro t _
      rw [smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (tilt_nonneg P i x t)]
      apply mul_le_mul_of_nonneg_left _ (tilt_nonneg P i x t)
      exact (ContinuousLinearMap.le_opNorm _ v).trans
        (mul_le_mul_of_nonneg_right (hb i t) (norm_nonneg v))
    _ = (q : ℝ) * ‖v‖ := by rw [← Finset.sum_mul, tilt_sum P i x, one_mul]

theorem global_lipschitz [Nonempty (Fin M)] (c : Space n) (η : ℝ) (q : ℝ≥0)
    (hb : ∀ i t, ‖(ContinuousLinearMap.proj i : Space n →L[ℝ] ℝ) -
      η • linearForm (P.exponent i t)‖ ≤ q) :
    LipschitzWith q (MultivariateGuard.fallback (fun x => logPartition P x - c) η) := by
  apply MultivariateGuard.fallback_lipschitz _ (jacobian P) η q
  · intro x
    exact (hasFDerivAt_logPartition P x).sub_const c
  · exact jacobian_contraction_of_support P η q hb

theorem unique_solution [Nonempty (Fin M)] (c : Space n) (η : ℝ) (hη : η ≠ 0)
    (q : ℝ≥0) (hq : q < 1)
    (hb : ∀ i t, ‖(ContinuousLinearMap.proj i : Space n →L[ℝ] ℝ) -
      η • linearForm (P.exponent i t)‖ ≤ q) :
    ∃! x, logPartition P x = c := by
  simpa only [sub_eq_zero] using MultivariateGuard.exists_unique_root
    (fun x => logPartition P x - c) η hη q hq (global_lipschitz P c η q hb)

end LeanMath.Papers.PosynomialSystem
