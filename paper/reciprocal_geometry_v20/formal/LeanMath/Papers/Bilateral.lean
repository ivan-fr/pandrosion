import LeanMath.Papers.RealBracket
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section
namespace LeanMath.Papers.RealBracket
open Real Set

def gap (p R : ℝ) := logCenter p R-log R/p

theorem hasDerivAt_logCenter (p R : ℝ) (hp : 1 < p) (hR : 0 < R) :
    HasDerivAt (logCenter p)
      (((3-p)/R+(p-1)*((p-1)/((p-1)*R+1)-1/(R+p-1)))/2) R := by
  have hA : 0 < (p-1)*R+1 := by positivity
  have hB : 0 < R+p-1 := by linarith
  convert! (((hasDerivAt_log hR.ne').const_mul (3-p)).add
    (((((hasDerivAt_id R).const_mul (p-1)).add_const 1).log hA.ne').sub
      ((((hasDerivAt_id R).add_const p).sub_const 1).log hB.ne') |>.const_mul (p-1))).div_const 2 using 1
  simp [id_eq,div_eq_mul_inv,mul_comm]

theorem hasDerivAt_gap (p R : ℝ) (hp : 1 < p) (hR : 0 < R) :
    HasDerivAt (gap p)
      (-(p-1)^2*(p-2)*(R-1)^2/(2*p*R*((p-1)*R+1)*(R+p-1))) R := by
  have hA : 0 < (p-1)*R+1 := by positivity
  have hB : 0 < R+p-1 := by linarith
  have hp0 : p ≠ 0 := by linarith
  convert! (hasDerivAt_logCenter p R hp hR).sub ((hasDerivAt_log hR.ne').div_const p) using 1
  field_simp
  <;> ring

theorem gap_one (p : ℝ) : gap p 1=0 := by simp [gap,logCenter]

theorem center_below_root (p R : ℝ) (hp : 2 < p) (hR : 1 < R) : center p R < R^(1/p) := by
  have hp1 : 1 < p := by linarith
  have ha : StrictAntiOn (gap p) (Ici 1) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici 1)
    · intro t ht
      change 1 ≤ t at ht
      exact (hasDerivAt_gap p t hp1 (by linarith [ht])).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      change 1 < t at ht
      have ht0 : 0 < t := by linarith [ht]
      rw [(hasDerivAt_gap p t hp1 ht0).deriv]
      have hA : 0 < (p-1)*t+1 := by positivity
      have hB : 0 < t+p-1 := by linarith
      have hpm1 : 0 < p-1 := by linarith
      have hpm2 : 0 < p-2 := by linarith
      have htm1 : 0 < t-1 := by linarith
      apply div_neg_of_neg_of_pos
      · have : 0 < (p-1)^2*(p-2)*(t-1)^2 := by positivity
        nlinarith
      · positivity
  have h := ha (show (1:ℝ) ∈ Ici 1 by simp) hR.le hR
  rw [gap_one] at h
  have hR0 : 0 < R := by linarith
  apply (log_lt_log_iff (center_pos p R hp1 hR0) (rpow_pos_of_pos hR0 _)).mp
  rw [log_center p R hp1 hR0,log_rpow hR0]
  have hh := sub_neg.mp h
  simpa [div_eq_mul_inv,mul_comm] using hh

theorem logCenter_inv (p R : ℝ) (hp : 1 < p) (hR : 0 < R) :
    logCenter p R⁻¹ = -logCenter p R := by
  have hA : 0 < (p-1)*R+1 := by positivity
  have hB : 0 < R+p-1 := by linarith
  have heA : (p-1)*R⁻¹+1=(R+p-1)/R := by field_simp; ring
  have heB : R⁻¹+p-1=((p-1)*R+1)/R := by field_simp; ring
  unfold logCenter
  rw [heA,heB,log_inv,log_div hA.ne' hR.ne',log_div hB.ne' hR.ne']
  ring

theorem center_reciprocal (p R : ℝ) (hp : 1 < p) (hR : 0 < R) :
    center p R⁻¹=(center p R)⁻¹ := by
  have hg := center_pos p R hp hR
  have hgi := center_pos p R⁻¹ hp (inv_pos.mpr hR)
  calc center p R⁻¹ = exp (log (center p R⁻¹)) := (exp_log hgi).symm
       _ = exp (-log (center p R)) := by rw [log_center p R⁻¹ hp (inv_pos.mpr hR),
          logCenter_inv p R hp hR,log_center p R hp hR]
       _ = (center p R)⁻¹ := by rw [exp_neg,exp_log hg]

theorem center_above_root (p R : ℝ) (hp : 2 < p) (hR0 : 0 < R) (hR1 : R < 1) :
    R^(1/p) < center p R := by
  have hp1 : 1 < p := by linarith
  have h := center_below_root p R⁻¹ hp ((one_lt_inv₀ hR0).mpr hR1)
  rw [center_reciprocal p R hp1 hR0,inv_rpow hR0.le] at h
  exact (inv_lt_inv₀ (center_pos p R hp1 hR0) (rpow_pos_of_pos hR0 _)).mp h

theorem square_root_exact (R : ℝ) (hR : 0 < R) : center 2 R = sqrt R := by
  have hlog : log (center 2 R)=log (sqrt R) := by
    rw [log_center 2 R (by norm_num) hR,log_sqrt hR.le]
    unfold logCenter
    norm_num
    rw [show R+2-1=R+1 by ring]
    ring
  have h := congrArg exp hlog
  rwa [exp_log (center_pos 2 R (by norm_num) hR),exp_log (sqrt_pos_of_pos hR)] at h

theorem cube_root_halley (R : ℝ) (hR : 0 < R) : center 3 R=(2*R+1)/(R+2) := by
  have hA : 0 < 2*R+1 := by positivity
  have hB : 0 < R+2 := by positivity
  have hlog : log (center 3 R)=log ((2*R+1)/(R+2)) := by
    rw [log_center 3 R (by norm_num) hR,log_div hA.ne' hB.ne']
    unfold logCenter
    norm_num
    congr 1 <;> congr 1 <;> ring
  have h := congrArg exp hlog
  rwa [exp_log (center_pos 3 R (by norm_num) hR),exp_log (div_pos hA hB)] at h

theorem logCenter_derivative_formula (p R : ℝ) (hp : 1 < p) (hR : 0 < R) :
    deriv (logCenter p) R =
      (2*p*R-(p-1)*(p-3)*(R-1)^2)/(2*R*((p-1)*R+1)*(R+p-1)) := by
  have hA : 0 < (p-1)*R+1 := by positivity
  have hB : 0 < R+p-1 := by linarith
  have hA' : 1+p*R-R ≠ 0 := by nlinarith [mul_pos (sub_pos.mpr hp) hR]
  rw [(hasDerivAt_logCenter p R hp hR).deriv]
  field_simp [hA.ne',hA',hB.ne',hR.ne']
  ring_nf
  field_simp [hA']
  <;> ring

theorem center_above_one_on_cell (p R : ℝ) (hp : 3 ≤ p) (hR : 1 < R)
    (hcell : p*(R-1)^2 ≤ 1) : 1 < center p R := by
  have hp1 : 1 < p := by linarith
  have hR0 : 0 < R := by linarith
  have hmono : StrictMonoOn (logCenter p) (Icc 1 R) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 1 R)
    · intro t ht
      exact (hasDerivAt_logCenter p t hp1 (by linarith [ht.1])).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have ht0 : 0 < t := by linarith [ht.1]
      have hsq : (t-1)^2 ≤ (R-1)^2 := by nlinarith [ht.1,ht.2]
      have hsmall : p*(t-1)^2 ≤ 1 := (mul_le_mul_of_nonneg_left hsq (by linarith)).trans hcell
      have hcoef : (p-1)*(p-3) ≤ p^2 := by nlinarith
      have hnum : 0 < 2*p*t-(p-1)*(p-3)*(t-1)^2 := by
        nlinarith [mul_le_mul_of_nonneg_right hcoef (sq_nonneg (t-1)),
          mul_le_mul_of_nonneg_left hsmall (by linarith : 0 ≤ p),mul_pos (by linarith : 0<p) ht0]
      rw [logCenter_derivative_formula p t hp1 ht0]
      have hA : 0 < (p-1)*t+1 := by positivity
      have hB : 0 < t+p-1 := by linarith
      exact div_pos hnum (by positivity)
  have h := hmono ⟨le_rfl,hR.le⟩ ⟨hR.le,le_rfl⟩ hR
  have hzero : logCenter p 1=0 := by simp [logCenter]
  rw [hzero,←log_center p R hp1 hR0] at h
  exact (log_pos_iff (center_pos p R hp1 hR0).le).mp h

end LeanMath.Papers.RealBracket
