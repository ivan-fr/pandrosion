import LeanMath.Papers.StrictBracket

/-! Weighted-mean identities and uniqueness of the reciprocal constant log-affine blend. -/
noncomputable section
namespace LeanMath.Papers.V14WeightedMeans
open Real
open LeanMath.Papers.RealBracket

def arithmetic (p R : ℝ) := (R+p-1)/p
def harmonic (p R : ℝ) := (arithmetic p R⁻¹)⁻¹

theorem arithmetic_pos (p R : ℝ) (hp : 1<p) (hR : 0<R) : 0<arithmetic p R := by
  unfold arithmetic
  exact div_pos (by linarith) (by linarith)

theorem harmonic_pos (p R : ℝ) (hp : 1<p) (hR : 0<R) : 0<harmonic p R :=
  inv_pos.mpr (arithmetic_pos p R⁻¹ hp (inv_pos.mpr hR))

theorem harmonic_formula (p R : ℝ) (hR : 0<R) :
    harmonic p R=p*R/((p-1)*R+1) := by
  unfold harmonic arithmetic
  rw [inv_div]
  have he : R⁻¹+p-1=((p-1)*R+1)/R := by field_simp; ring
  rw [he,div_div_eq_mul_div]

theorem root_le_arithmetic (p R : ℝ) (hp : 1<p) (hR : 0<R) :
    R^(1/p)≤arithmetic p R := by
  have hp0 : p≠0 := by linarith
  have hh := power_tangent p (R^(1/p)) hp (rpow_pos_of_pos hR _)
  rw [←rpow_mul hR.le,one_div_mul_cancel hp0,rpow_one] at hh
  exact (le_div_iff₀ (by linarith : 0<p)).mpr (by simpa [mul_comm] using hh)

theorem harmonic_le_root (p R : ℝ) (hp : 1<p) (hR : 0<R) :
    harmonic p R≤R^(1/p) := by
  have hh := root_le_arithmetic p R⁻¹ hp (inv_pos.mpr hR)
  have hi := (inv_le_inv₀ (arithmetic_pos p R⁻¹ hp (inv_pos.mpr hR)) (rpow_pos_of_pos (inv_pos.mpr hR) (1/p))).mpr hh
  simpa [harmonic,inv_rpow hR.le] using hi

theorem lower_mean (p R : ℝ) (hp : 1<p) (hR : 0<R) :
    lower p R=R/(arithmetic p R)^(p-1) := by
  unfold lower arithmetic
  rw [←inv_div (R+p-1) p,inv_rpow (div_pos (by linarith : 0<R+p-1) (by linarith : 0<p)).le]
  rfl

theorem upper_mean (p R : ℝ) (hp : 1<p) (hR : 0<R) :
    upper p R=R/(harmonic p R)^(p-1) := by
  rw [upper,lower_mean p R⁻¹ hp (inv_pos.mpr hR)]
  simp only [harmonic,inv_div,inv_inv,inv_rpow (arithmetic_pos p R⁻¹ hp (inv_pos.mpr hR)).le,div_inv_eq_mul]
  ring

theorem logarithmic_width (p R : ℝ) (hp : 1<p) (hR : 0<R) :
    log (upper p R/lower p R)=(p-1)*log (arithmetic p R/harmonic p R) := by
  have hA := arithmetic_pos p R hp hR
  have hH := harmonic_pos p R hp hR
  rw [log_div (upper_pos p R hp hR).ne' (lower_pos p R hp hR).ne',
    upper_mean p R hp hR,lower_mean p R hp hR,
    log_div hR.ne' (rpow_pos_of_pos hH _).ne',log_div hR.ne' (rpow_pos_of_pos hA _).ne',
    log_rpow hH,log_rpow hA,log_div hA.ne' hH.ne']
  ring

def blend (p theta R : ℝ) := (lower p R)^(1-theta)*(upper p R)^theta

theorem blend_pos (p theta R : ℝ) (hp : 1<p) (hR : 0<R) : 0<blend p theta R :=
  mul_pos (rpow_pos_of_pos (lower_pos p R hp hR) _) (rpow_pos_of_pos (upper_pos p R hp hR) _)

theorem log_blend (p theta R : ℝ) (hp : 1<p) (hR : 0<R) :
    log (blend p theta R)=(1-theta)*log (lower p R)+theta*log (upper p R) := by
  unfold blend
  rw [log_mul (rpow_pos_of_pos (lower_pos p R hp hR) _).ne'
    (rpow_pos_of_pos (upper_pos p R hp hR) _).ne',
    log_rpow (lower_pos p R hp hR),log_rpow (upper_pos p R hp hR)]

theorem blend_half (p R : ℝ) (hp : 1<p) (hR : 0<R) : blend p (1/2) R=center p R := by
  apply log_injOn_pos (blend_pos p (1/2) R hp hR) (center_pos p R hp hR)
  rw [log_blend p (1/2) R hp hR]
  unfold center
  rw [log_sqrt (mul_pos (upper_pos p R hp hR) (lower_pos p R hp hR)).le,
    log_mul (upper_pos p R hp hR).ne' (lower_pos p R hp hR).ne']
  ring

/-- Even reciprocity at one nonunit residual forces the constant weight to be one half. -/
theorem reciprocal_weight (p theta R : ℝ) (hp : 1<p) (hR : 0<R) (hne : R≠1)
    (hrec : blend p theta R⁻¹=(blend p theta R)⁻¹) : theta=1/2 := by
  have hh := congrArg log hrec
  rw [log_blend p theta R⁻¹ hp (inv_pos.mpr hR),log_inv,log_blend p theta R hp hR] at hh
  have hL : lower p R⁻¹=(upper p R)⁻¹ := by simp [upper]
  have hU : upper p R⁻¹=(lower p R)⁻¹ := by simp [upper]
  rw [hL,hU,log_inv,log_inv] at hh
  have hw : 0<log (upper p R)-log (lower p R) := sub_pos.mpr
    ((log_lt_log_iff (lower_pos p R hp hR) (upper_pos p R hp hR)).mpr
      ((lower_strict p R hp hR hne).trans (upper_strict p R hp hR hne)))
  have he : (2*theta-1)*(log (upper p R)-log (lower p R))=0 := by nlinarith [hh]
  have ht := (mul_eq_zero.mp he).resolve_right (ne_of_gt hw)
  linarith

theorem reciprocal_blend_iff (p theta : ℝ) (hp : 1<p) :
    (∀ R : ℝ, 0<R → blend p theta R⁻¹=(blend p theta R)⁻¹) ↔ theta=1/2 := by
  constructor
  · intro hh
    exact reciprocal_weight p theta 2 hp (by norm_num) (by norm_num) (hh 2 (by norm_num))
  · rintro rfl R hR
    rw [blend_half p R⁻¹ hp (inv_pos.mpr hR),blend_half p R hp hR]
    exact center_reciprocal p R hp hR

end LeanMath.Papers.V14WeightedMeans
