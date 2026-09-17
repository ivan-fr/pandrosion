import LeanMath.Papers.Bilateral
import LeanMath.Papers.CertifiedConvergence

noncomputable section
namespace LeanMath.Papers.RealBracket
open Real Set Filter
open scoped Topology

/-- Correct strict range: p=1 must be excluded, and p=2 is exact. -/
theorem subquadratic_above_root (p R : ℝ) (hp : 1 < p) (hp2 : p < 2) (hR : 1 < R) :
    R^(1/p) < center p R := by
  have hm : StrictMonoOn (gap p) (Ici 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 1)
    · intro t ht
      change 1 ≤ t at ht
      exact (hasDerivAt_gap p t hp (by linarith)).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      change 1 < t at ht
      have ht0 : 0 < t := by linarith
      rw [(hasDerivAt_gap p t hp ht0).deriv]
      have hA : 0 < (p-1)*t+1 := by positivity
      have hB : 0 < t+p-1 := by linarith
      have h1 : 0 < (p-1)^2 := sq_pos_of_pos (by linarith)
      have h2 : p-2 < 0 := by linarith
      have h3 : 0 < (t-1)^2 := sq_pos_of_pos (by linarith)
      have hn : 0 < -(p-1)^2*(p-2)*(t-1)^2 := by
        have := mul_neg_of_pos_of_neg h1 h2
        nlinarith [mul_neg_of_neg_of_pos this h3]
      exact div_pos hn (by positivity)
  have h := hm (show (1:ℝ) ∈ Ici 1 by simp) hR.le hR
  rw [gap_one] at h
  have hR0 : 0 < R := by linarith
  apply (log_lt_log_iff (rpow_pos_of_pos hR0 _) (center_pos p R hp hR0)).mp
  rw [log_center p R hp hR0,log_rpow hR0]
  have hh := sub_pos.mp h
  simpa [div_eq_mul_inv,mul_comm] using hh

theorem center_above_one_low_degree (p R : ℝ) (hp : 1 < p) (hp3 : p ≤ 3) (hR : 1 < R) :
    1 < center p R := by
  have hm : StrictMonoOn (logCenter p) (Ici 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 1)
    · intro t ht
      change 1 ≤ t at ht
      exact (hasDerivAt_logCenter p t hp (by linarith)).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      change 1 < t at ht
      have ht0 : 0 < t := by linarith
      rw [logCenter_derivative_formula p t hp ht0]
      have hc : (p-1)*(p-3)*(t-1)^2 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)) (sq_nonneg _)
      have hA : 0 < (p-1)*t+1 := by positivity
      have hB : 0 < t+p-1 := by linarith
      exact div_pos (by nlinarith [mul_pos (show 0 < p by linarith) ht0]) (by positivity)
  have h := hm (show (1:ℝ) ∈ Ici 1 by simp) hR.le hR
  have hz : logCenter p 1=0 := by simp [logCenter]
  rw [hz,←log_center p R hp (by linarith)] at h
  exact (log_pos_iff (center_pos p R hp (by linarith)).le).mp h

theorem continuousAt_center (p R : ℝ) (hp : 1 < p) (hR : 0 < R) :
    ContinuousAt (center p) R := by
  have he : ∀ᶠ t : ℝ in 𝓝 R, center p t=exp (logCenter p t) := by
    filter_upwards [Ioi_mem_nhds hR] with t ht
    rw [←log_center p t hp ht,exp_log (center_pos p t hp ht)]
  have hc := Real.continuous_exp.continuousAt.comp (hasDerivAt_logCenter p R hp hR).continuousAt
  exact hc.congr_of_eventuallyEq he

theorem center_one (p : ℝ) (hp : 1 < p) : center p 1=1 := by
  have h := log_center p 1 hp (by norm_num)
  have hz : logCenter p 1=0 := by simp [logCenter]
  rw [hz] at h
  have hh := congrArg exp h
  simpa only [exp_log (center_pos p 1 hp (by norm_num)),exp_zero] using hh

/-- For 2<p≤3 the center needs no dyadic safeguard: its update converges globally. -/
theorem low_degree_global_convergence (p x u : ℝ) (hp : 2 < p) (hp3 : p ≤ 3)
    (hx : 0 < x) (hu : 0 < u) :
    Tendsto (fun n : ℕ => (Certified.step (center p) p x)^[n] u)
      atTop (𝓝 (x^(1/p))) := by
  have hp1 : 1 < p := by linarith
  apply Certified.global (center p) p x u (by linarith) hx hu
  · exact fun t ht => continuousAt_center p t hp1 ht
  · exact center_one p hp1
  · intro R hR
    exact ⟨center_above_one_low_degree p R hp1 hp3 hR,center_below_root p R hp hR⟩
  · intro R hR0 hR1
    refine ⟨center_above_root p R hp hR0 hR1,?_⟩
    have h := center_above_one_low_degree p R⁻¹ hp1 hp3 ((one_lt_inv₀ hR0).mpr hR1)
    rw [center_reciprocal p R hp1 hR0] at h
    exact (one_lt_inv₀ (center_pos p R hp1 hR0)).mp h

end LeanMath.Papers.RealBracket
