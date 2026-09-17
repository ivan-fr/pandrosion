import LeanMath.Papers.Bilateral

noncomputable section
namespace LeanMath.Papers.RealBracket
open Real Set

def lowerGap (p R : ℝ) := log R/p-(log R+(p-1)*(log p-log (R+p-1)))

theorem lowerGap_derivative (p R : ℝ) (hp : 1 < p) (hR : 0 < R) :
    HasDerivAt (lowerGap p) ((p-1)^2*(R-1)/(p*R*(R+p-1))) R := by
  have hD : 0 < R+p-1 := by linarith
  convert! ((hasDerivAt_log hR.ne').div_const p).sub
    ((hasDerivAt_log hR.ne').add
      (((((hasDerivAt_id R).add_const p).sub_const 1).log hD.ne').const_sub (log p) |>.const_mul (p-1))) using 1
  simp only [id_eq]
  field_simp
  <;> ring

theorem lowerGap_one (p : ℝ) : lowerGap p 1=0 := by
  unfold lowerGap
  rw [show (1:ℝ)+p-1=p by ring]
  simp

theorem lowerGap_positive (p R : ℝ) (hp : 1 < p) (hR : 0 < R) (hne : R ≠ 1) :
    0 < lowerGap p R := by
  have hp0 : 0 < p := by linarith
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hm : StrictAntiOn (lowerGap p) (Ioc 0 1) := by
      apply strictAntiOn_of_deriv_neg (convex_Ioc 0 1)
      · exact fun t ht => (lowerGap_derivative p t hp ht.1).continuousAt.continuousWithinAt
      · intro t ht
        rw [interior_Ioc] at ht
        have ht0 : 0 < t := ht.1
        rw [(lowerGap_derivative p t hp ht.1).deriv]
        have hD : 0 < t+p-1 := by linarith [ht.1]
        have hsq : 0 < (p-1)^2 := sq_pos_of_pos (by linarith)
        exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hsq (by linarith [ht.2])) (by positivity)
    have h := hm ⟨hR,hlt.le⟩ ⟨by norm_num,le_rfl⟩ hlt
    rwa [lowerGap_one] at h
  · have hm : StrictMonoOn (lowerGap p) (Ici 1) := by
      apply strictMonoOn_of_deriv_pos (convex_Ici 1)
      · intro t ht
        change 1 ≤ t at ht
        exact (lowerGap_derivative p t hp (by linarith)).continuousAt.continuousWithinAt
      · intro t ht
        rw [interior_Ici] at ht
        change 1 < t at ht
        have ht0 : 0 < t := by linarith
        rw [(lowerGap_derivative p t hp ht0).deriv]
        have hD : 0 < t+p-1 := by linarith
        have hp1 : 0 < p-1 := by linarith
        have ht1 : 0 < t-1 := by linarith
        positivity
    have h := hm (by simp) hgt.le hgt
    rwa [lowerGap_one] at h

theorem lower_strict (p R : ℝ) (hp : 1 < p) (hR : 0 < R) (hne : R ≠ 1) :
    lower p R < R^(1/p) := by
  have h := lowerGap_positive p R hp hR hne
  apply (log_lt_log_iff (lower_pos p R hp hR) (rpow_pos_of_pos hR _)).mp
  rw [log_lower p R hp hR,log_rpow hR]
  unfold lowerGap at h
  have he : (1/p)*log R=log R/p := by ring
  rw [he]
  linarith

theorem upper_strict (p R : ℝ) (hp : 1 < p) (hR : 0 < R) (hne : R ≠ 1) :
    R^(1/p) < upper p R := by
  have hni : R⁻¹ ≠ 1 := by simpa using hne
  have h := lower_strict p R⁻¹ hp (inv_pos.mpr hR) hni
  rw [inv_rpow hR.le] at h
  have hh := (inv_lt_inv₀ (inv_pos.mpr (rpow_pos_of_pos hR (1/p)))
    (lower_pos p R⁻¹ hp (inv_pos.mpr hR))).mpr h
  simpa [upper] using hh

theorem center_inside_bracket (p R : ℝ) (hp : 1 < p) (hR : 0 < R) (hne : R ≠ 1) :
    lower p R < center p R ∧ center p R < upper p R := by
  have hl := lower_pos p R hp hR
  have hu := upper_pos p R hp hR
  have hg := center_pos p R hp hR
  have hstrict := (lower_strict p R hp hR hne).trans (upper_strict p R hp hR hne)
  have hlog := (log_lt_log_iff hl hu).mpr hstrict
  have hw := half_width p R hp hR
  rw [log_div hu.ne' hg.ne',log_div hu.ne' hl.ne'] at hw
  constructor
  · apply (log_lt_log_iff hl hg).mp
    linarith
  · apply (log_lt_log_iff hg hu).mp
    linarith

end LeanMath.Papers.RealBracket
