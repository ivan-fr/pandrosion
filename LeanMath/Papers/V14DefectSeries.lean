import LeanMath.Papers.V14Defect
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! The convergent infinite series in Theorem 9.1. -/
noncomputable section
namespace LeanMath.Papers.V14DefectSeries
open Real Set
open LeanMath.Papers.V14Defect

/-- The coefficients d_j in the manuscript; only odd j >= 3 are used. -/
def d (p : ℝ) (j : ℕ) : ℝ := (p-1)*(a p-(a p)^j)/(2*j)

theorem artanh_hasSum (y : ℝ) (hy : |y|<1) :
    HasSum (fun k : ℕ => y^(2*k+1)/(2*k+1)) (artanh y) := by
  have h := (hasSum_log_sub_log_of_abs_lt_one hy).div_const 2
  have hy' := abs_lt.mp hy
  have he : (log (1+y)-log (1-y))/2 = artanh y := by
    rw [artanh_eq_half_log ⟨hy'.1.le,hy'.2.le⟩,
      log_div (by linarith : 1+y ≠ 0) (by linarith : 1-y ≠ 0)]
    ring
  rw [he] at h
  convert! h using 1
  ext k
  ring

theorem defect_hasSum_from_one (p y : ℝ) (hp : 2<p) (hy : |y|<1) :
    HasSum (fun k : ℕ => d p (2*k+1)*y^(2*k+1)) (defect p y/2) := by
  have h := (((artanh_hasSum y hy).mul_left (a p)).sub
    (artanh_hasSum (a p*y) (abs_lt.mpr (scaled_mem p y hp (abs_lt.mp hy))))).mul_left ((p-1)/2)
  rw [exact_defect_identity p y hp (abs_lt.mp hy)]
  convert! h using 1
  · ext k
    simp only [d,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,mul_pow]
    field_simp
  · ring

/-- The linear term vanishes, leaving exactly the odd powers 3,5,7,... . -/
theorem defect_hasSum (p y : ℝ) (hp : 2<p) (hy : |y|<1) :
    HasSum (fun k : ℕ => d p (2*k+3)*y^(2*k+3)) (defect p y/2) := by
  have h := defect_hasSum_from_one p y hp hy
  have hs : HasSum (fun k : ℕ => d p (2*(k+1)+1)*y^(2*(k+1)+1)) (defect p y/2) := by
    apply (hasSum_nat_add_iff 1 (f := fun k : ℕ => d p (2*k+1)*y^(2*k+1))).mpr
    simpa [Finset.sum_range_one,d] using h
  simpa only [show ∀ k : ℕ, 2*(k+1)+1=2*k+3 by omega] using hs

end LeanMath.Papers.V14DefectSeries
