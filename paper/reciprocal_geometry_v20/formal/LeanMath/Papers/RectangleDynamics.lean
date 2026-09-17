import LeanMath.Papers.RectangleRaw
import LeanMath.Papers.Family
import LeanMath.Papers.LocalOrder

noncomputable section
namespace LeanMath.Papers.RectangleDynamics
open LeanMath.Papers.RectangleReports LeanMath.Papers.RectangleRaw
open LeanMath.Papers Filter Set Function
open scoped Topology

theorem ad_pos (p : ℕ) (X s : ℝ) (hp : 2≤p) (hX : 0<X) (hs : 0<s) : 0<ad p X s := by
  have hp' : (2:ℝ)≤p := by exact_mod_cast hp
  have hm : 0<(p:ℝ)-1 := by linarith
  exact div_pos (by positivity) (denominators_pos p X s hp hX hs).2

theorem ad_eq_halley (p : ℕ) (X s : ℝ) (hp : 2≤p) (hX : 0<X) (hs : 0<s) :
    ad p X s=Certified.step (Cayley.family 0 (p:ℝ)) (p:ℝ) X⁻¹ s := by
  have hp' : (1:ℝ)<p := by exact_mod_cast (show 1<p by omega)
  have hpow : 0<s^p := pow_pos hs p
  unfold Certified.step
  rw [(Cayley.family_identification (p:ℝ) (X⁻¹/s^(p:ℝ))).1,
    Real.rpow_natCast,Cayley.halley_formula (p:ℝ) _ hp' (by positivity)]
  unfold ad
  field_simp
  <;> ring

theorem ad_global_convergence (p : ℕ) (X s : ℝ) (hp : 2≤p) (hX : 0<X) (hs : 0<s) :
    Tendsto (fun n : ℕ => (ad p X)^[n] s) atTop (𝓝 (X⁻¹ ^ (1/(p:ℝ)))) := by
  have hp' : (1:ℝ)<p := by exact_mod_cast (show 1<p by omega)
  have hpos : ∀ n : ℕ, 0<(ad p X)^[n] s := by
    intro n; induction n with
    | zero => exact hs
    | succ n ih => rw [iterate_succ_apply']; exact ad_pos p X _ hp hX ih
  have he : ∀ n : ℕ, (ad p X)^[n] s=
      (Certified.step (Cayley.family 0 (p:ℝ)) (p:ℝ) X⁻¹)^[n] s := by
    intro n; induction n with
    | zero => rfl
    | succ n ih =>
      rw [iterate_succ_apply',iterate_succ_apply',ad_eq_halley p X _ hp hX (hpos n),ih]
  simpa only [← he] using Cayley.family_global_convergence 0 (p:ℝ) X⁻¹ s hp' (inv_pos.mpr hX) hs

theorem hasDerivAt_ad (p : ℕ) (X s : ℝ) (hp : 2≤p)
    (hd : (p:ℝ)-1+((p:ℝ)+1)*X*s^p≠0) :
    HasDerivAt (ad p X)
      (((p:ℝ)^2-1)*(X*s^p-1)^2/((p:ℝ)-1+((p:ℝ)+1)*X*s^p)^2) s := by
  have hpow : s*s^(p-1)=s^p := by rw [← pow_succ']; congr 1; omega
  have h := ((hasDerivAt_id s).mul
    ((((hasDerivAt_id s).pow p).const_mul (((p:ℝ)-1)*X)).const_add ((p:ℝ)+1))).div
    ((((hasDerivAt_id s).pow p).const_mul (((p:ℝ)+1)*X)).const_add ((p:ℝ)-1)) hd
  convert! h using 1
  simp only [id_eq,mul_one,one_mul,Pi.pow_apply,Pi.mul_apply]
  field_simp [hd]
  rw [← hpow]
  ring

def adFactor (p : ℕ) (e : ℝ) :=
  ((p:ℝ)^2-1)*(sumPowers p (1+e))^2/((p:ℝ)-1+((p:ℝ)+1)*(1+e)^p)^2

theorem ad_order_three (p : ℕ) (hp : 2≤p) :
    Tendsto (fun e : ℝ => (ad p 1 (1+e)-1)/e^3) (𝓝[≠] 0)
      (𝓝 (((p:ℝ)^2-1)/12)) := by
  have hp' : (2:ℝ)≤p := by exact_mod_cast hp
  have hp0 : (p:ℝ)≠0 := by linarith
  have hd0 : (p:ℝ)-1+((p:ℝ)+1)*(1+(0:ℝ))^p≠0 := by simp; linarith
  have hf0 : ad p 1 (1+0)-1=0 := by
    simp only [ad,add_zero,one_pow,mul_one,one_mul]
    rw [show (p:ℝ)+1+((p:ℝ)-1)=(p:ℝ)-1+((p:ℝ)+1) by ring,
      div_self (by linarith : (p:ℝ)-1+((p:ℝ)+1)≠0),sub_self]
  have hc : ContinuousAt (fun e : ℝ => ad p 1 (1+e)-1) 0 := by
    unfold ad
    apply ContinuousAt.sub _ continuousAt_const
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · simpa using hd0
  have hg : ContinuousAt (adFactor p) 0 := by
    unfold adFactor sumPowers
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · exact pow_ne_zero _ hd0
  have hh : ∀ᶠ e : ℝ in 𝓝[≠] 0,
      HasDerivAt (fun e : ℝ => ad p 1 (1+e)-1) (e^2*adFactor p e) e := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (show (-1:ℝ)<0 by norm_num))] with e he
    have hpos : 0<1+e := by have : -1<e := he; linarith
    have hd := (denominators_pos p 1 (1+e) hp (by norm_num) hpos).2.ne'
    have hd' := ((hasDerivAt_ad p 1 (1+e) hp hd).comp e ((hasDerivAt_id e).const_add 1)).sub_const 1
    convert! hd' using 1
    simp only [one_mul,mul_one]
    have hi := sum_identity p (1+e)
    have hi' : (1+e)^p-1=e*sumPowers p (1+e) := by nlinarith [hi]
    rw [hi']; unfold adFactor; ring
  have ht := LocalOrder.from_derivative 2 (fun e : ℝ => ad p 1 (1+e)-1) (adFactor p) hf0 hc hg hh
  have hv : adFactor p 0/((2:ℝ)+1)=((p:ℝ)^2-1)/12 := by
    simp [adFactor,sumPowers]; field_simp [hp0] <;> ring
  simpa only [Nat.reduceAdd,Nat.cast_ofNat,hv] using ht

theorem ad_order_coefficient_pos (p : ℕ) (hp : 2≤p) : 0<((p:ℝ)^2-1)/12 := by
  have : (2:ℝ)≤p := by exact_mod_cast hp
  apply div_pos _ (by norm_num)
  nlinarith

/-- Scaling transfers the unit-root order to any positive target root a. -/
theorem ad_scale (p : ℕ) (X a t : ℝ) (ha : X*a^p=1) :
    ad p X (a*t)=a*ad p 1 t := by
  unfold ad; rw [mul_pow]
  have h : X*(a^p*t^p)=t^p := by rw [← mul_assoc,ha,one_mul]
  simp only [mul_assoc] at h ⊢
  rw [show X*(a^p*t^p)=t^p from h]
  ring
theorem ad_relative_order_three (p : ℕ) (X a : ℝ) (hp : 2≤p)
    (ha : 0<a) (hroot : X*a^p=1) :
    Tendsto (fun e : ℝ => (ad p X (a*(1+e))/a-1)/e^3) (𝓝[≠] 0)
      (𝓝 (((p:ℝ)^2-1)/12)) := by
  simpa only [ad_scale p X a _ hroot,mul_div_cancel_left₀ _ ha.ne'] using ad_order_three p hp

end LeanMath.Papers.RectangleDynamics
