import LeanMath.Papers.Corrections
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
namespace LeanMath.Papers.RealBracket
open Real

def lower (p R : ℝ) := R*(p/(R+p-1))^(p-1)
def upper (p R : ℝ) := (lower p R⁻¹)⁻¹
def center (p R : ℝ) := sqrt (upper p R*lower p R)
def logCenter (p R : ℝ) := ((3-p)*log R+(p-1)*(log ((p-1)*R+1)-log (R+p-1)))/2

theorem lower_pos (p R : ℝ) (hp : 1 < p) (hR : 0 < R) : 0 < lower p R := by
  have hd : 0 < R+p-1 := by linarith
  exact mul_pos hR (rpow_pos_of_pos (div_pos (by linarith) hd) _)

theorem upper_pos (p R : ℝ) (hp : 1 < p) (hR : 0 < R) : 0 < upper p R :=
  inv_pos.mpr (lower_pos p R⁻¹ hp (inv_pos.mpr hR))

theorem center_pos (p R : ℝ) (hp : 1 < p) (hR : 0 < R) : 0 < center p R :=
  sqrt_pos_of_pos (mul_pos (upper_pos p R hp hR) (lower_pos p R hp hR))

theorem power_tangent (p q : ℝ) (hp : 1 < p) (hq : 0 < q) : p*q ≤ q^p+p-1 := by
  have hp0 : 0 < p := by linarith
  have he : exp (p*log q)=q^p := by
    rw [rpow_def_of_pos hq]
    congr 1
    ring
  have h := exp_chord 0 p 1 (log q) hp0 (by norm_num) hp.le
  simp only [endpointMGF,zero_mul,exp_zero,one_mul,exp_log hq,sub_zero,he,mul_one] at h
  have hh := mul_le_mul_of_nonneg_left h hp0.le
  field_simp at hh
  nlinarith

theorem lower_le_root (p q : ℝ) (hp : 1 < p) (hq : 0 < q) : lower p (q^p) ≤ q := by
  have hp0 : 0 < p := by linarith
  have hden : 0 < q^p+p-1 := by linarith [rpow_pos_of_pos hq p]
  have ha : 0 < p/(q^p+p-1) := div_pos hp0 hden
  have hb : q*(p/(q^p+p-1)) ≤ 1 := by
    rw [←mul_div_assoc]
    exact (div_le_one hden).mpr (by simpa [mul_comm] using power_tangent p q hp hq)
  have hpow : (q*(p/(q^p+p-1)))^(p-1) ≤ 1 :=
    rpow_le_one (mul_pos hq ha).le hb (by linarith)
  have hsplit : q^p=q*q^(p-1) := by rw [rpow_sub hq,rpow_one]; field_simp
  calc lower p (q^p)=q*(q*(p/(q^p+p-1)))^(p-1) := by
         unfold lower
         rw [mul_rpow hq.le ha.le]
         rw [hsplit]
         ring
       _ ≤ q*1 := mul_le_mul_of_nonneg_left hpow hq.le
       _ = q := mul_one q

theorem certified_bracket (p q : ℝ) (hp : 1 < p) (hq : 0 < q) :
    lower p (q^p) ≤ q ∧ q ≤ upper p (q^p) := by
  have hl := lower_le_root p q hp hq
  have hu := lower_le_root p q⁻¹ hp (inv_pos.mpr hq)
  have hpos := lower_pos p (q⁻¹^p) hp (rpow_pos_of_pos (inv_pos.mpr hq) _)
  have h := (inv_le_inv₀ (inv_pos.mpr hq) hpos).mpr hu
  refine ⟨hl,?_⟩
  simpa only [upper,inv_rpow hq.le,inv_inv] using h

theorem upper_formula (p R : ℝ) (hp : 1 < p) (hR : 0 < R) :
    upper p R=R*((p-1+R⁻¹)/p)^(p-1) := by
  have hd : 0 < R⁻¹+p-1 := by linarith [inv_pos.mpr hR]
  have ha : 0 ≤ p/(R⁻¹+p-1) := (div_pos (by linarith) hd).le
  unfold upper lower
  rw [mul_inv_rev,←inv_rpow ha,inv_div,inv_inv,mul_comm]
  congr 2
  ring

theorem log_lower (p R : ℝ) (hp : 1 < p) (hR : 0 < R) :
    log (lower p R)=log R+(p-1)*(log p-log (R+p-1)) := by
  have hp0 : 0 < p := by linarith
  have hd : 0 < R+p-1 := by linarith
  unfold lower
  rw [log_mul hR.ne' (rpow_pos_of_pos (div_pos hp0 hd) _).ne',
    log_rpow (div_pos hp0 hd),log_div hp0.ne' hd.ne']

theorem log_upper (p R : ℝ) (hp : 1 < p) (hR : 0 < R) :
    log (upper p R)=(2-p)*log R+(p-1)*(log ((p-1)*R+1)-log p) := by
  have hA : 0 < (p-1)*R+1 := by positivity
  have hi : 0 < R⁻¹ := inv_pos.mpr hR
  have he : R⁻¹+p-1=((p-1)*R+1)/R := by field_simp; ring
  unfold upper
  rw [log_inv,log_lower p R⁻¹ hp hi,he,log_div hA.ne' hR.ne',log_inv]
  ring

theorem log_center (p R : ℝ) (hp : 1 < p) (hR : 0 < R) :
    log (center p R)=logCenter p R := by
  have hl := lower_pos p R hp hR
  have hu := upper_pos p R hp hR
  unfold center
  rw [log_sqrt (mul_pos hu hl).le,log_mul hu.ne' hl.ne',log_upper p R hp hR,log_lower p R hp hR]
  unfold logCenter
  ring

theorem half_width (p R : ℝ) (hp : 1 < p) (hR : 0 < R) :
    log (upper p R/center p R)=log (upper p R/lower p R)/2 := by
  have hl := lower_pos p R hp hR
  have hu := upper_pos p R hp hR
  have hg := center_pos p R hp hR
  rw [log_div hu.ne' hg.ne',log_div hu.ne' hl.ne']
  unfold center
  rw [log_sqrt (mul_pos hu hl).le,log_mul hu.ne' hl.ne']
  ring

end LeanMath.Papers.RealBracket
