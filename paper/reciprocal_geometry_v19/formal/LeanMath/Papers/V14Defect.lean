import LeanMath.Papers.Bilateral
import LeanMath.Papers.Comparison

/-! Exact identities for §§9 and 11 of Reciprocal Geometry v14.
The functions below use the existing geometric center, not an independent
axiomatized replacement. All statements concern exact real arithmetic. -/
noncomputable section
namespace LeanMath.Papers.V14Defect
open Real Set
open LeanMath.Papers.Cayley LeanMath.Papers.RealBracket

def a (p : ℝ) : ℝ := (p - 2) / p

def defect (p y : ℝ) : ℝ :=
  log ((unchi y) ^ (1 / p) / center p (unchi y))

def defectCoordinate (p y : ℝ) : ℝ := tanh (defect p y / 2)

theorem a_mem (p : ℝ) (hp : 2 < p) : a p ∈ Ioo 0 1 := by
  have hp0 : 0 < p := by linarith
  constructor
  · exact div_pos (by linarith) hp0
  · unfold a; exact (div_lt_one hp0).mpr (by linarith)

theorem scaled_mem (p y : ℝ) (hp : 2 < p) (hy : y ∈ Ioo (-1) 1) :
    a p * y ∈ Ioo (-1) 1 := by
  have ha := a_mem p hp
  have hab : |a p * y| < 1 := by
    rw [abs_mul, abs_of_pos ha.1]
    have h := mul_lt_mul_of_pos_left (abs_lt.mpr hy) ha.1
    nlinarith [ha.2]
  exact abs_lt.mp hab

theorem log_unchi (y : ℝ) (hy : y ∈ Ioo (-1) 1) :
    log (unchi y) = 2 * artanh y := by
  rw [artanh_eq_half_log ⟨hy.1.le, hy.2.le⟩]
  unfold unchi
  ring

theorem center_ratio (p y : ℝ) (hp : 2 < p) (hy : y ∈ Ioo (-1) 1) :
    ((p - 1) * unchi y + 1) / (unchi y + p - 1) = unchi (a p * y) := by
  have hp0 : p ≠ 0 := by linarith
  have hy0 : 1-y ≠ 0 := by linarith [hy.2]
  have hR := LeanMath.Papers.Cayley.unchi_pos y hy
  have hd : unchi y + p - 1 ≠ 0 := by linarith
  have ham := scaled_mem p y hp hy
  have hd' : 1 - a p * y ≠ 0 := by linarith [ham.2]
  unfold unchi a at *
  field_simp
  <;> ring

theorem log_center_coordinate (p y : ℝ) (hp : 2 < p) (hy : y ∈ Ioo (-1) 1) :
    log (center p (unchi y)) =
      (3-p)*artanh y + (p-1)*artanh (a p*y) := by
  have hp1 : 1 < p := by linarith
  have hR := LeanMath.Papers.Cayley.unchi_pos y hy
  have hA : 0 < (p-1)*unchi y+1 := by positivity
  have hB : 0 < unchi y+p-1 := by linarith
  rw [log_center p _ hp1 hR]
  unfold logCenter
  rw [← log_div hA.ne' hB.ne', center_ratio p y hp hy,
    log_unchi y hy, log_unchi _ (scaled_mem p y hp hy)]
  ring

/-- Theorem 9.1: the defect of the actual geometric center. -/
theorem exact_defect_identity (p y : ℝ) (hp : 2 < p) (hy : y ∈ Ioo (-1) 1) :
    defect p y = (p-1)*(a p*artanh y-artanh (a p*y)) := by
  have hR := LeanMath.Papers.Cayley.unchi_pos y hy
  have hG := center_pos p _ (by linarith) hR
  unfold defect
  rw [log_div (rpow_pos_of_pos hR _).ne' hG.ne', log_rpow hR,
    log_unchi y hy, log_center_coordinate p y hp hy]
  unfold a
  field_simp
  <;> ring

theorem artanh_neg_eq (y : ℝ) (hy : y ∈ Ioo (-1) 1) :
    artanh (-y) = -artanh y := by
  have h := log_unchi (-y) ⟨by linarith [hy.2], by linarith [hy.1]⟩
  rw [unchi_neg, log_inv, log_unchi y hy] at h
  linarith

theorem defect_odd (p y : ℝ) (hp : 2 < p) (hy : y ∈ Ioo (-1) 1) :
    defect p (-y) = -defect p y := by
  rw [exact_defect_identity p y hp hy,
    exact_defect_identity p (-y) hp ⟨by linarith [hy.2], by linarith [hy.1]⟩]
  rw [mul_neg, artanh_neg_eq y hy, artanh_neg_eq _ (scaled_mem p y hp hy)]
  ring

theorem defectCoordinate_odd (p y : ℝ) (hp : 2 < p) (hy : y ∈ Ioo (-1) 1) :
    defectCoordinate p (-y) = -defectCoordinate p y := by
  simp [defectCoordinate, defect_odd p y hp hy, neg_div, tanh_neg]

theorem unchi_tanh (t : ℝ) : unchi (tanh t) = exp (2*t) := by
  have hm : tanh t ∈ Ioo (-1) 1 := ⟨neg_one_lt_tanh t, tanh_lt_one t⟩
  have h := log_unchi (tanh t) hm
  rw [artanh_tanh] at h
  rw [← h, exp_log (LeanMath.Papers.Cayley.unchi_pos _ hm)]

/-- Equation 9.6: multiplying the center by its exact defect gives the root. -/
theorem exact_correction (p y : ℝ) (hp : 2 < p) (hy : y ∈ Ioo (-1) 1) :
    center p (unchi y) * unchi (defectCoordinate p y) = (unchi y)^(1/p) := by
  have hR := LeanMath.Papers.Cayley.unchi_pos y hy
  have hG := center_pos p _ (by linarith) hR
  rw [defectCoordinate, unchi_tanh]
  rw [show 2*(defect p y/2)=defect p y by ring]
  rw [defect, exp_log (div_pos (rpow_pos_of_pos hR _) hG)]
  field_simp

/-- Equation 11.2, the inverse-Cayley composition law, with its domain conditions. -/
theorem cayley_composition (s t : ℝ) (hs : |s| < 1) (ht : |t| < 1) :
    unchi s * unchi t = unchi ((s+t)/(1+s*t)) := by
  have hs' := abs_lt.mp hs
  have ht' := abs_lt.mp ht
  have hprod : |s*t| < 1 := by
    rw [abs_mul]
    have h := mul_le_mul_of_nonneg_left ht.le (abs_nonneg s)
    nlinarith
  have hd : 1+s*t ≠ 0 := by have := (abs_lt.mp hprod).1; linarith
  have h1 : 1-s ≠ 0 := by linarith [hs'.2]
  have h2 : 1-t ≠ 0 := by linarith [ht'.2]
  have h3 : 1+s*t-(s+t) ≠ 0 := by
    rw [show 1+s*t-(s+t)=(1-s)*(1-t) by ring]
    exact mul_ne_zero h1 h2
  unfold unchi
  field_simp
  <;> ring

end LeanMath.Papers.V14Defect
