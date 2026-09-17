import LeanMath.Papers.CrossBracket

noncomputable section
namespace LeanMath.Papers.RealBracket
open Real Set
open LeanMath.Papers.Cayley

def width (p R : ℝ) := log (upper p R)-log (lower p R)
def upperRatio (p R : ℝ) := (log (upper p R)-log (C₇ p R))/width p R
/-- Ratio of the certified Cayley interval width to the original width. -/
def widthRatio (p R : ℝ) := if 1 ≤ R then upperRatio p R else 1-upperRatio p R

theorem width_pos (p R : ℝ) (hp : 1 < p) (hR : 0 < R) (hne : R ≠ 1) :
    0 < width p R := by
  exact sub_pos.mpr ((log_lt_log_iff (lower_pos p R hp hR) (upper_pos p R hp hR)).mpr
    ((lower_strict p R hp hR hne).trans (upper_strict p R hp hR hne)))

theorem center_lt_C₇ (p R : ℝ) (hp : 3 ≤ p) (hR : 1 < R) : center p R < C₇ p R := by
  rcases hp.eq_or_lt with he | ht
  · subst p
    exact RealCorrections.center_three_lt_C₇ R hR
  · exact (center_lt_halley p R ht hR).trans
      (RealCorrections.C₃_lt_C₇ p R (by linarith) hR)

theorem upperRatio_lt_half (p R : ℝ) (hp : 3 ≤ p) (hR : 1 < R) : upperRatio p R < 1/2 := by
  have hp1 : 1 < p := by linarith
  have hR0 : 0 < R := by linarith
  have h := (log_lt_log_iff (center_pos p R hp1 hR0) (C₇_pos p R hp1 hR0)).mpr
    (center_lt_C₇ p R hp hR)
  have hw := half_width p R hp1 hR0
  rw [log_div (upper_pos p R hp1 hR0).ne' (center_pos p R hp1 hR0).ne',
    log_div (upper_pos p R hp1 hR0).ne' (lower_pos p R hp1 hR0).ne'] at hw
  apply (div_lt_iff₀ (width_pos p R hp1 hR0 (by linarith))).mpr
  unfold width
  linarith

theorem width_inverse (p R : ℝ) : width p R⁻¹=width p R := by
  simp [width,upper,log_inv]
  <;> ring

theorem upperRatio_inverse (p R : ℝ) (hp : 1 < p) (hR : 0 < R) (hne : R ≠ 1) :
    upperRatio p R⁻¹=1-upperRatio p R := by
  unfold upperRatio
  rw [width_inverse,C₇_reciprocal p R hR,log_inv]
  have hn := (width_pos p R hp hR hne).ne'
  apply (eq_sub_iff_add_eq).mpr
  rw [←add_div]
  convert div_self hn using 1
  congr 1
  simp [width,upper,log_inv]
  <;> ring

theorem widthRatio_lt_half (p R : ℝ) (hp : 3 ≤ p) (hR : 0 < R) (hne : R ≠ 1) :
    widthRatio p R < 1/2 := by
  unfold widthRatio
  split_ifs with ht
  · exact upperRatio_lt_half p R hp (lt_of_le_of_ne ht (Ne.symm hne))
  · rw [←upperRatio_inverse p R (by linarith) hR hne]
    exact upperRatio_lt_half p R⁻¹ hp ((one_lt_inv₀ hR).mpr (lt_of_not_ge ht))

theorem upperRatio_square_gt_half (R : ℝ) (hR : 1 < R) : 1/2 < upperRatio 2 R := by
  have hR0 : 0 < R := by linarith
  have hc : C₇ 2 R < center 2 R := by
    rw [square_root_exact R hR0,Real.sqrt_eq_rpow]
    exact (C₇_above_one_below_root 2 R (by norm_num) hR).2
  have h := (log_lt_log_iff (C₇_pos 2 R (by norm_num) hR0)
    (center_pos 2 R (by norm_num) hR0)).mpr hc
  have hw := half_width 2 R (by norm_num) hR0
  rw [log_div (upper_pos 2 R (by norm_num) hR0).ne' (center_pos 2 R (by norm_num) hR0).ne',
    log_div (upper_pos 2 R (by norm_num) hR0).ne' (lower_pos 2 R (by norm_num) hR0).ne'] at hw
  apply (lt_div_iff₀ (width_pos 2 R (by norm_num) hR0 (by linarith))).mpr
  unfold width
  linarith

theorem widthRatio_square_gt_half (R : ℝ) (hR : 0 < R) (hne : R ≠ 1) :
    1/2 < widthRatio 2 R := by
  unfold widthRatio
  split_ifs with ht
  · exact upperRatio_square_gt_half R (lt_of_le_of_ne ht (Ne.symm hne))
  · rw [←upperRatio_inverse 2 R (by norm_num) hR hne]
    exact upperRatio_square_gt_half R⁻¹ ((one_lt_inv₀ hR).mpr (lt_of_not_ge ht))

theorem widthRatio_below_formula (p R : ℝ) (hp : 1 < p) (hR : 0 < R) (hR1 : R < 1) :
    widthRatio p R=(log (C₇ p R)-log (lower p R))/width p R := by
  rw [widthRatio,if_neg (not_le.mpr hR1)]
  unfold upperRatio
  apply (sub_eq_iff_eq_add).mpr
  rw [←add_div]
  have hn := (width_pos p R hp hR (by linarith)).ne'
  symm
  convert div_self hn using 1
  unfold width
  congr 1
  ring

theorem upperRatio_mem_unit (p R : ℝ) (hp : 2 ≤ p) (hR : 1 < R) :
    upperRatio p R ∈ Ioo 0 1 := by
  have hp1 : 1 < p := by linarith
  have hR0 : 0 < R := by linarith
  have hchain := refinement_above 2 p R hp hR
  have hlo : lower p R < C₇ p R := hchain.1
  have hup : C₇ p R < upper p R := hchain.2.1.trans hchain.2.2
  have hloglo := (log_lt_log_iff (lower_pos p R hp1 hR0) (C₇_pos p R hp1 hR0)).mpr hlo
  have hlogup := (log_lt_log_iff (C₇_pos p R hp1 hR0) (upper_pos p R hp1 hR0)).mpr hup
  have hw := width_pos p R hp1 hR0 (by linarith)
  constructor
  · exact div_pos (sub_pos.mpr hlogup) hw
  · apply (div_lt_iff₀ hw).mpr
    unfold width
    linarith

theorem widthRatio_mem_unit (p R : ℝ) (hp : 2 ≤ p) (hR : 0 < R) (hne : R ≠ 1) :
    widthRatio p R ∈ Ioo 0 1 := by
  unfold widthRatio
  split_ifs with ht
  · exact upperRatio_mem_unit p R hp (lt_of_le_of_ne ht (Ne.symm hne))
  · rw [←upperRatio_inverse p R (by linarith) hR hne]
    exact upperRatio_mem_unit p R⁻¹ hp ((one_lt_inv₀ hR).mpr (lt_of_not_ge ht))

end LeanMath.Papers.RealBracket
