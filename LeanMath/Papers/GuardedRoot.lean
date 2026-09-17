import LeanMath.Papers.CayleyHybrid

noncomputable section
namespace LeanMath.Papers.GuardedRoot
open Real Filter Function
open scoped Topology

def update (p D δ x u : ℝ) :=
  if |log (x/u^p)| ≤ δ then Cayley.step p x u
  else u*Dyadic.correction p D (x/u^p)

theorem residual_log (p r u : ℝ) (hr : 0 < r) (hu : 0 < u) :
    log (r^p/u^p) = -p*log (u/r) := by
  rw [log_div (rpow_pos_of_pos hr p).ne' (rpow_pos_of_pos hu p).ne',
    log_rpow hr,log_rpow hu,log_div hu.ne' hr.ne']
  ring

theorem residual_exp (p r u : ℝ) (hr : 0 < r) (hu : 0 < u) :
    r^p/u^p=exp (-p*log (u/r)) := by
  rw [←residual_log p r u hr hu,exp_log (div_pos (rpow_pos_of_pos hr _) (rpow_pos_of_pos hu _))]

theorem update_pos (p D δ r u : ℝ) (hp : 1 < p) (hr : 0 < r) (hu : 0 < u) :
    0 < update p D δ (r^p) u := by
  unfold update
  split
  · exact mul_pos hu (Cayley.C₇_pos p _ hp (div_pos (rpow_pos_of_pos hr _) (rpow_pos_of_pos hu _)))
  · exact mul_pos hu (rpow_pos_of_pos (div_pos (rpow_pos_of_pos hr _) (rpow_pos_of_pos hu _)) _)

/-- The guard uses the computable residual; it does not require knowing the root. -/
theorem log_update (p D ε r u : ℝ) (hp : 1 < p) (hr : 0 < r) (hu : 0 < u) :
    log (update p D (p*ε) (r^p) u/r) =
      Hybrid.step (Cayley.Hybrid.localError p) (Dyadic.rho p D) ε (log (u/r)) := by
  have hp0 : 0 < p := by linarith
  have hg : |log (r^p/u^p)| ≤ p*ε ↔ |log (u/r)| ≤ ε := by
    rw [residual_log p r u hr hu,abs_mul,abs_neg,abs_of_pos hp0]
    constructor <;> intro h <;> nlinarith
  unfold update Hybrid.step
  by_cases hguard : |log (u/r)| ≤ ε
  · rw [if_pos (hg.mpr hguard),if_pos hguard]
    rw [Cayley.Hybrid.localError_eq_logError p _ hp]
    unfold Cayley.step Cayley.logError
    rw [log_div (mul_pos hu (Cayley.C₇_pos p _ hp
      (div_pos (rpow_pos_of_pos hr _) (rpow_pos_of_pos hu _)))).ne' hr.ne',
      log_mul hu.ne' (Cayley.C₇_pos p _ hp
      (div_pos (rpow_pos_of_pos hr _) (rpow_pos_of_pos hu _))).ne',
      residual_exp p r u hr hu,log_div hu.ne' hr.ne']
    ring
  · rw [if_neg (fun h => hguard (hg.mp h)),if_neg hguard]
    rw [←div_rpow hr.le hu.le]
    exact Dyadic.log_error_linear p D r u hr hu

theorem orbit_positive (p D ε r u : ℝ) (hp : 1 < p) (hr : 0 < r) (hu : 0 < u) :
    ∀ n : ℕ, 0 < (update p D (p*ε) (r^p))^[n] u := by
  intro n
  induction n with
  | zero => exact hu
  | succ n ih =>
    rw [iterate_succ_apply']
    exact update_pos p D (p*ε) r _ hp hr ih

theorem orbit_log (p D ε r u : ℝ) (hp : 1 < p) (hr : 0 < r) (hu : 0 < u) (n : ℕ) :
    log ((update p D (p*ε) (r^p))^[n] u/r) =
      (Hybrid.step (Cayley.Hybrid.localError p) (Dyadic.rho p D) ε)^[n] (log (u/r)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply',iterate_succ_apply',
      log_update p D ε r _ hp hr (orbit_positive p D ε r u hp hr hu n),ih]

/-- Global convergence of the residual-guarded root update. -/
theorem convergence (p s : ℕ) (hp : 2 ≤ p) (ε r u : ℝ)
    (hε : 0 < ε) (hr : 0 < r) (hu : 0 < u) :
    Tendsto (fun n : ℕ => (update p (Dyadic.denominator p s) (p*ε) (r^(p:ℝ)))^[n] u)
      atTop (𝓝 r) := by
  have hp1 : (1:ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have h := Cayley.Hybrid.root_estimates_converge p s hp ε (log (u/r)) r hε
  apply h.congr'
  apply Eventually.of_forall
  intro n
  dsimp only
  rw [←orbit_log p (Dyadic.denominator p s) ε r u hp1 hr hu n,
    exp_log (div_pos (orbit_positive p (Dyadic.denominator p s) ε r u hp1 hr hu n) hr)]
  field_simp

/-- Every positive input x is covered, using its unique positive real root. -/
theorem convergence_for_input (p s : ℕ) (hp : 2 ≤ p) (ε x u : ℝ)
    (hε : 0 < ε) (hx : 0 < x) (hu : 0 < u) :
    Tendsto (fun n : ℕ => (update p (Dyadic.denominator p s) (p*ε) x)^[n] u)
      atTop (𝓝 (x^(1/(p:ℝ)))) := by
  have hp0 : (p:ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hr := rpow_pos_of_pos hx (1/(p:ℝ))
  have he : (x^(1/(p:ℝ)))^(p:ℝ)=x := by
    rw [one_div,rpow_inv_rpow hx.le hp0]
  simpa only [he] using convergence p s hp ε (x^(1/(p:ℝ))) u hε hr hu

end LeanMath.Papers.GuardedRoot
