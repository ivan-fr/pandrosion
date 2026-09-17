import LeanMath.Papers.Hybrid
import LeanMath.Papers.CayleyConvergence
import LeanMath.Papers.CayleyLocal

noncomputable section
namespace LeanMath.Papers.Cayley.Hybrid
open Real Filter Function
open scoped Topology

def localError (p e : ℝ) := log (Cayley.step p 1 (exp e))

theorem step_pos (p u : ℝ) (hp : 1 < p) (hu : 0 < u) : 0 < Cayley.step p 1 u := by
  exact mul_pos hu (C₇_pos p _ hp (div_pos (by norm_num) (rpow_pos_of_pos hu _)))

theorem localError_zero (p : ℝ) : localError p 0=0 := by
  simp [localError,Cayley.step,C₇_one]

theorem conjugacy (p e : ℝ) (hp : 1 < p) (n : ℕ) :
    exp ((localError p)^[n] e)=(Cayley.step p 1)^[n] (exp e) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply',iterate_succ_apply']
    change exp (log (Cayley.step p 1 (exp ((localError p)^[n] e)))) = _
    rw [exp_log (step_pos p _ hp (exp_pos _)),ih]

theorem local_convergence (p e : ℝ) (hp : 1 < p) :
    Tendsto (fun n : ℕ => (localError p)^[n] e) atTop (𝓝 0) := by
  have ht := Cayley.global_convergence p 1 (exp e) hp (by norm_num) (exp_pos e)
  simp only [one_rpow] at ht
  have hl := (continuousAt_log (by norm_num : (1:ℝ) ≠ 0)).tendsto.comp ht
  have he : (fun n : ℕ => log ((Cayley.step p 1)^[n] (exp e))) =
      (fun n : ℕ => (localError p)^[n] e) := by
    funext n
    rw [←conjugacy p e hp n,log_exp]
  simpa only [Function.comp_def,he,log_one] using hl

theorem abs_nonincreasing (p e : ℝ) (hp : 1 < p) : |localError p e| ≤ |e| := by
  have hpos := exp_pos e
  have heq : Cayley.step p 1 (exp e)=rootStep p 1 (exp e) :=
    step_eq_rootStep p 1 1 (exp e) (by norm_num) hpos (by simp)
  rcases lt_trichotomy e 0 with he | he | he
  · have hue : exp e < 1 := by simpa using exp_lt_exp.mpr he
    obtain ⟨h1,h2⟩ := rootStep_below p 1 (exp e) hp (by norm_num) hpos hue
    rw [←heq] at h1 h2
    have hlog1 := (log_lt_log_iff hpos (step_pos p _ hp hpos)).mpr h1
    have hlog2 := (log_lt_log_iff (step_pos p _ hp hpos) (by norm_num : (0:ℝ)<1)).mpr h2
    simp only [log_exp,log_one] at hlog1 hlog2
    change |log (Cayley.step p 1 (exp e))| ≤ |e|
    rw [abs_of_neg hlog2,abs_of_neg he]
    linarith
  · subst e
    simp [localError_zero]
  · have hue : 1 < exp e := by simpa using exp_lt_exp.mpr he
    obtain ⟨h1,h2⟩ := rootStep_above p 1 (exp e) hp (by norm_num) hue
    rw [←heq] at h1 h2
    have hlog1 := (log_lt_log_iff (by norm_num : (0:ℝ)<1) (step_pos p _ hp hpos)).mpr h1
    have hlog2 := (log_lt_log_iff (step_pos p _ hp hpos) hpos).mpr h2
    simp only [log_exp,log_one] at hlog1 hlog2
    change |log (Cayley.step p 1 (exp e))| ≤ |e|
    rw [abs_of_pos hlog1,abs_of_pos he]
    exact hlog2.le

theorem localError_eq_logError (p e : ℝ) (hp : 1 < p) : localError p e=logError p e := by
  have he : 1/(exp e)^p=exp (-p*e) := by
    rw [rpow_def_of_pos (exp_pos e),log_exp,one_div,←exp_neg]
    congr 1
    ring
  unfold localError Cayley.step logError
  rw [he,log_mul (exp_pos e).ne' (C₇_pos p _ hp (exp_pos _)).ne',log_exp]

/-- The actual guarded log-error iteration converges: fallback outside the cell,
Cayley order seven inside it. The fallback cannot be reactivated after entry. -/
theorem dyadic_hybrid_convergence (p s : ℕ) (hp : 2 ≤ p) (ε e : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ =>
      (Papers.Hybrid.step (localError p) (Dyadic.rho p (Dyadic.denominator p s)) ε)^[n] e)
      atTop (𝓝 0) := by
  have hp1 : (1:ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hb := Dyadic.dyadic_strict_bound p s (by omega)
  have hpow : (1:ℝ) ≤ 2^(s+1) := one_le_pow₀ (by norm_num)
  have hrho : |Dyadic.rho p (Dyadic.denominator p s)| < 1 :=
    hb.trans_le ((div_le_one (by positivity)).mpr hpow)
  exact Papers.Hybrid.converge _ _ ε e hrho hε
    (fun t ht => (abs_nonincreasing p t hp1).trans ht)
    (fun t _ => local_convergence p t hp1)

/-- Guarding leaves the exact seventh-order local coefficient unchanged. -/
theorem hybrid_exact_order (p ρ ε : ℝ) (hp : 1 < p) (hε : 0 < ε) :
    Tendsto (fun e : ℝ => Papers.Hybrid.step (localError p) ρ ε e/e^7)
      (𝓝[≠] 0) (𝓝 (kappa₇ p)) := by
  apply (exact_order_seven p hp).congr'
  have hm : Set.Ioo (-ε) ε ∈ 𝓝 (0:ℝ) := Ioo_mem_nhds (by linarith) hε
  filter_upwards [mem_nhdsWithin_of_mem_nhds hm] with e he
  have he' : |e| ≤ ε := abs_le.mpr ⟨he.1.le,he.2.le⟩
  rw [Papers.Hybrid.step,if_pos he',localError_eq_logError p e hp]

/-- Reconstruction of the positive root estimate from the guarded log error. -/
theorem root_estimates_converge (p s : ℕ) (hp : 2 ≤ p) (ε e r : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => r * exp (
      (Papers.Hybrid.step (localError p) (Dyadic.rho p (Dyadic.denominator p s)) ε)^[n] e))
      atTop (𝓝 r) := by
  have h := ((Real.continuous_exp.continuousAt.tendsto).comp
    (dyadic_hybrid_convergence p s hp ε e hε)).const_mul r
  simpa using h

end LeanMath.Papers.Cayley.Hybrid
