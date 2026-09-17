import LeanMath.Papers.Bilateral
import LeanMath.Papers.RealCorrections

noncomputable section
namespace LeanMath.Papers.RealBracket
open Real Set
open LeanMath.Papers.Cayley

def logHalley (p R : ℝ) := log ((p+1)*R+p-1)-log ((p-1)*R+p+1)
def halleyGap (p R : ℝ) := logHalley p R-logCenter p R

theorem log_C₃ (p R : ℝ) (hp : 1 < p) (hR : 0 < R) : log (C₃ p R)=logHalley p R := by
  rw [halley_formula p R hp hR]
  have hA : 0 < (p+1)*R+(p-1) := by positivity
  have hB : 0 < (p-1)*R+(p+1) := by positivity
  rw [log_div hA.ne' hB.ne']
  unfold logHalley
  congr 1 <;> congr 1 <;> ring

theorem halleyGap_one (p : ℝ) : halleyGap p 1=0 := by
  unfold halleyGap logHalley logCenter
  simp
  congr 1
  ring

theorem halleyGap_derivative (p R : ℝ) (hp : 1 < p) (hR : 0 < R) :
    HasDerivAt (halleyGap p)
      ((R-1)^2*(p-3)*(p-1)*((p^2-1)*R^2+2*(p^2-p+1)*R+(p^2-1))/
        (2*R*(R+p-1)*((p-1)*R+1)*((p-1)*R+p+1)*((p+1)*R+p-1))) R := by
  have hA : 0 < (p+1)*R+p-1 := by nlinarith [mul_pos (by linarith : 0 < p+1) hR]
  have hB : 0 < (p-1)*R+p+1 := by positivity
  have hdA := (((hasDerivAt_id R).const_mul (p+1)).add_const p).sub_const 1
  have hdB := (((hasDerivAt_id R).const_mul (p-1)).add_const p).add_const 1
  convert! ((hdA.log hA.ne').sub (hdB.log hB.ne')).sub (hasDerivAt_logCenter p R hp hR) using 1
  have hC : 0 < R+p-1 := by linarith
  have hD : 0 < (p-1)*R+1 := by positivity
  simp only [id_eq]
  generalize ha : (p+1)*R+p-1=A at *
  generalize hb : (p-1)*R+p+1=B at *
  generalize hc : R+p-1=C at *
  generalize hd : (p-1)*R+1=D at *
  field_simp [hA.ne',hB.ne',hC.ne',hR.ne',hD.ne']
  subst A B C D
  ring

theorem halleyGap_sign (p R : ℝ) (hp : 1 < p) (hR : 1 < R) :
    (3 < p → 0 < halleyGap p R) ∧ (p < 3 → halleyGap p R < 0) := by
  have hcont : ContinuousOn (halleyGap p) (Ici 1) := by
    intro t ht
    change 1 ≤ t at ht
    exact (halleyGap_derivative p t hp (by linarith)).continuousAt.continuousWithinAt
  have hsign : ∀ t, 1 < t →
      (3 < p → 0 < deriv (halleyGap p) t) ∧ (p < 3 → deriv (halleyGap p) t < 0) := by
    intro t ht
    have ht0 : 0 < t := by linarith
    have hp0 : 0 < p := by linarith
    have ht1 : 0 < t-1 := by linarith
    have hp1 : 0 < p-1 := by linarith
    have hs : 0 < p^2-1 := by nlinarith
    have hs2 : 0 < p^2-p+1 := by nlinarith [sq_nonneg (p-1)]
    have hQ : 0 < (p^2-1)*t^2+2*(p^2-p+1)*t+(p^2-1) := by positivity
    have hA : 0 < (p+1)*t+p-1 := by nlinarith [mul_pos (by linarith : 0 < p+1) ht0]
    have hB : 0 < (p-1)*t+p+1 := by positivity
    have hC : 0 < t+p-1 := by linarith
    have hD : 0 < (p-1)*t+1 := by positivity
    rw [(halleyGap_derivative p t hp ht0).deriv]
    constructor
    · intro hp3
      have : 0 < p-3 := by linarith
      positivity
    · intro hp3
      apply div_neg_of_neg_of_pos
      · have hneg : (t-1)^2*(p-3) < 0 := mul_neg_of_pos_of_neg (by positivity) (by linarith)
        exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hneg hp1) hQ
      · positivity
  constructor
  · intro hp3
    have hm : StrictMonoOn (halleyGap p) (Ici 1) := by
      apply strictMonoOn_of_deriv_pos (convex_Ici 1) hcont
      intro t ht
      rw [interior_Ici] at ht
      exact (hsign t ht).1 hp3
    have h := hm (by simp) hR.le hR
    rwa [halleyGap_one] at h
  · intro hp3
    have hm : StrictAntiOn (halleyGap p) (Ici 1) := by
      apply strictAntiOn_of_deriv_neg (convex_Ici 1) hcont
      intro t ht
      rw [interior_Ici] at ht
      exact (hsign t ht).2 hp3
    have h := hm (by simp) hR.le hR
    rwa [halleyGap_one] at h

theorem center_lt_halley (p R : ℝ) (hp : 3 < p) (hR : 1 < R) : center p R < C₃ p R := by
  have hp1 : 1 < p := by linarith
  have hR0 : 0 < R := by linarith
  have hc : 0 < C₃ p R := by
    simpa [Cayley.family,Cayley.truncation,C₃] using Cayley.family_pos 0 p R hp1 hR0
  apply (log_lt_log_iff (center_pos p R hp1 hR0) hc).mp
  rw [log_C₃ p R hp1 hR0,log_center p R hp1 hR0]
  exact sub_pos.mp ((halleyGap_sign p R hp1 hR).1 hp)

theorem halley_lt_center (p R : ℝ) (hp : 1 < p) (hp3 : p < 3) (hR : 1 < R) : C₃ p R < center p R := by
  have hR0 : 0 < R := by linarith
  have hc : 0 < C₃ p R := by
    simpa [Cayley.family,Cayley.truncation,C₃] using Cayley.family_pos 0 p R hp hR0
  apply (log_lt_log_iff hc (center_pos p R hp hR0)).mp
  rw [log_C₃ p R hp hR0,log_center p R hp hR0]
  exact sub_neg.mp ((halleyGap_sign p R hp hR).2 hp3)

end LeanMath.Papers.RealBracket
