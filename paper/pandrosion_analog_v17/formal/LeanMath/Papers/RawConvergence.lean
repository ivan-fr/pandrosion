import LeanMath.Papers.Raw
import LeanMath.Papers.MonotoneIteration
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
namespace LeanMath.Papers.Raw
open Real Filter Function
open scoped Topology BigOperators

theorem S_strictMono (p : ℕ) (hp : 2 ≤ p) (s t : ℝ) (hs : 0 < s) (hst : s < t) :
    S p s < S p t := by
  apply Finset.sum_lt_sum
  · intro i hi
    exact pow_le_pow_left₀ hs.le hst.le i
  · exact ⟨1,Finset.mem_range.mpr hp,by simpa using hst⟩

theorem step_strictMono (p : ℕ) (x s t : ℝ) (hp : 2 ≤ p)
    (hx : 1 < x) (hs : 0 < s) (hst : s < t) : step p x s < step p x t := by
  have hx0 : 0 < x := by linarith
  have hS := S_strictMono p hp s t hs hst
  have h := div_lt_div_of_pos_left (sub_pos.mpr hx)
    (mul_pos hx0 (S_pos p s (by omega) hs)) (mul_lt_mul_of_pos_left hS hx0)
  unfold step
  linarith

theorem displacement (p : ℕ) (x s : ℝ) (hp : 1 ≤ p) (hx : 0 < x) (hs : 0 < s) :
    step p x s - s = (1-x*s^p)/(x*S p s) := by
  have hS0 : S p s ≠ 0 := (S_pos p s hp hs).ne'
  have hd : x*S p s ≠ 0 := (mul_pos hx (S_pos p s hp hs)).ne'
  have hb := congrArg (fun t : ℝ => x*t) (bridge p s)
  unfold step
  field_simp [hS0]
  nlinarith

theorem continuousAt_step (p : ℕ) (x s : ℝ) (hp : 1 ≤ p) (hx : 0 < x) (hs : 0 < s) :
    ContinuousAt (step p x) s := by
  have hS : Continuous (S p) := by unfold S; fun_prop
  exact continuousAt_const.sub (continuousAt_const.div
    (continuousAt_const.mul hS.continuousAt) (mul_pos hx (S_pos p s hp hs)).ne')

theorem converge_to_fixed_point (p : ℕ) (x s r : ℝ) (hp : 2 ≤ p)
    (hx : 1 < x) (hs : 0 < s) (hr : 0 < r) (hroot : x*r^p=1) :
    Tendsto (fun n : ℕ => (step p x)^[n] s) atTop (𝓝 r) := by
  have hx0 : 0 < x := by linarith
  have hp1 : 1 ≤ p := by omega
  have hp0 : p ≠ 0 := by omega
  have hfix := (fixed_iff p x r hp1 hx0 hr).mpr hroot
  apply Iteration.converge (step p x) r s hr hs
  · exact fun t ht => continuousAt_step p x t hp1 hx0 ht
  · exact hfix
  · intro t ht htr
    have hpow := mul_lt_mul_of_pos_left (pow_lt_pow_left₀ htr ht.le hp0) hx0
    have hd : 0 < step p x t-t := by
      rw [displacement p x t hp1 hx0 ht]
      exact div_pos (by linarith) (mul_pos hx0 (S_pos p t hp1 ht))
    have hm := step_strictMono p x t r hp hx ht htr
    rw [hfix] at hm
    exact ⟨by linarith,hm⟩
  · intro t hrt
    have ht : 0 < t := hr.trans hrt
    have hpow := mul_lt_mul_of_pos_left (pow_lt_pow_left₀ hrt hr.le hp0) hx0
    have hd : step p x t-t < 0 := by
      rw [displacement p x t hp1 hx0 ht]
      exact div_neg_of_neg_of_pos (by linarith) (mul_pos hx0 (S_pos p t hp1 ht))
    have hm := step_strictMono p x r t hp hx hr hrt
    rw [hfix] at hm
    exact ⟨hm,by linarith⟩

/-- Reciprocal Geometry 2.2, including the visible root readout. -/
theorem global_raw_convergence (p : ℕ) (x s : ℝ) (hp : 2 ≤ p) (hx : 1 < x) (hs : 0 < s) :
    Tendsto (fun n : ℕ => (step p x)^[n] s) atTop (𝓝 ((x^((p:ℝ)⁻¹))⁻¹)) ∧
    Tendsto (fun n : ℕ => x*((step p x)^[n] s)^(p-1)) atTop (𝓝 (x^((p:ℝ)⁻¹))) := by
  have hx0 : 0 < x := by linarith
  have hp0 : p ≠ 0 := by omega
  let r : ℝ := (x^((p:ℝ)⁻¹))⁻¹
  have hr : 0 < r := inv_pos.mpr (rpow_pos_of_pos hx0 _)
  have hroot : x*r^p=1 := by
    dsimp [r]
    rw [inv_pow,rpow_inv_natCast_pow hx0.le hp0,mul_inv_cancel₀ hx0.ne']
  have h := converge_to_fixed_point p x s r hp hx hs hr hroot
  refine ⟨h,?_⟩
  have hv := (h.pow (p-1)).const_mul x
  rw [visible_readout p x r (by omega) hr hroot] at hv
  simpa [r] using hv

end LeanMath.Papers.Raw
