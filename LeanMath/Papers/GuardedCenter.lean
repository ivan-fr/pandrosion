import LeanMath.Papers.BilateralHybrid
import LeanMath.Papers.GuardedRoot

noncomputable section
namespace LeanMath.Papers.GuardedCenter
open Real Filter Function
open scoped Topology

def update (p D x u : ℝ) :=
  if |log (x/u^p)| ≤ log (1+1/sqrt p) then u*RealBracket.center p (x/u^p)
  else u*Dyadic.correction p D (x/u^p)

/-- The logarithmic test is exactly the reciprocal cell printed in Theorem 5.5. -/
theorem guard_equivalence (p R : ℝ) (hp : 0 < p) (hR : 0 < R) :
    (|log R| ≤ log (1+1/sqrt p)) ↔
      (1+1/sqrt p)⁻¹ ≤ R ∧ R ≤ 1+1/sqrt p := by
  have hα : 0 < 1+1/sqrt p := by positivity
  rw [abs_le,←log_inv]
  rw [log_le_log_iff (inv_pos.mpr hα) hR,log_le_log_iff hR hα]

theorem update_pos (p D r u : ℝ) (hp : 1 < p) (hr : 0 < r) (hu : 0 < u) :
    0 < update p D (r^p) u := by
  unfold update
  split
  · exact mul_pos hu (RealBracket.center_pos p _ hp
      (div_pos (rpow_pos_of_pos hr _) (rpow_pos_of_pos hu _)))
  · exact mul_pos hu (rpow_pos_of_pos (div_pos (rpow_pos_of_pos hr _) (rpow_pos_of_pos hu _)) _)

theorem log_update (p D r u : ℝ) (hp : 1 < p) (hr : 0 < r) (hu : 0 < u) :
    log (update p D (r^p) u/r) =
      Hybrid.step (RealBracket.Local.error p) (Dyadic.rho p D)
        (RealBracket.Local.radius p) (log (u/r)) := by
  have hp0 : 0 < p := by linarith
  have hg : |log (r^p/u^p)| ≤ log (1+1/sqrt p) ↔ |log (u/r)| ≤ RealBracket.Local.radius p := by
    rw [GuardedRoot.residual_log p r u hr hu,abs_mul,abs_neg,abs_of_pos hp0]
    unfold RealBracket.Local.radius
    rw [le_div_iff₀ hp0]
    constructor <;> intro h <;> nlinarith
  unfold update Hybrid.step
  by_cases hguard : |log (u/r)| ≤ RealBracket.Local.radius p
  · rw [if_pos (hg.mpr hguard),if_pos hguard]
    unfold RealBracket.Local.error
    rw [log_div (mul_pos hu (RealBracket.center_pos p _ hp
      (div_pos (rpow_pos_of_pos hr _) (rpow_pos_of_pos hu _)))).ne' hr.ne',
      log_mul hu.ne' (RealBracket.center_pos p _ hp
      (div_pos (rpow_pos_of_pos hr _) (rpow_pos_of_pos hu _))).ne',
      GuardedRoot.residual_exp p r u hr hu,log_div hu.ne' hr.ne']
    ring
  · rw [if_neg (fun h => hguard (hg.mp h)),if_neg hguard]
    rw [←div_rpow hr.le hu.le]
    exact Dyadic.log_error_linear p D r u hr hu

theorem orbit_positive (p D r u : ℝ) (hp : 1 < p) (hr : 0 < r) (hu : 0 < u) :
    ∀ n : ℕ, 0 < (update p D (r^p))^[n] u := by
  intro n
  induction n with
  | zero => exact hu
  | succ n ih =>
    rw [iterate_succ_apply']
    exact update_pos p D r _ hp hr ih

theorem orbit_log (p D r u : ℝ) (hp : 1 < p) (hr : 0 < r) (hu : 0 < u) (n : ℕ) :
    log ((update p D (r^p))^[n] u/r) =
      (Hybrid.step (RealBracket.Local.error p) (Dyadic.rho p D)
        (RealBracket.Local.radius p))^[n] (log (u/r)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply',iterate_succ_apply',
      log_update p D r _ hp hr (orbit_positive p D r u hp hr hu n),ih]

/-- The center-based guarded solver converges from every positive initial estimate. -/
theorem convergence (p s : ℕ) (hp : 2 ≤ p) (r u : ℝ) (hr : 0 < r) (hu : 0 < u) :
    Tendsto (fun n : ℕ => (update p (Dyadic.denominator p s) (r^(p:ℝ)))^[n] u)
      atTop (𝓝 r) := by
  have hp1 : (1:ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have ht := RealBracket.Local.dyadic_center_convergence p s hp (log (u/r))
  have hexp := (Real.continuous_exp.continuousAt.tendsto.comp ht).const_mul r
  simp only [exp_zero,mul_one] at hexp
  apply hexp.congr'
  apply Eventually.of_forall
  intro n
  dsimp only [Function.comp_def]
  rw [←orbit_log p (Dyadic.denominator p s) r u hp1 hr hu n,
    exp_log (div_pos (orbit_positive p (Dyadic.denominator p s) r u hp1 hr hu n) hr)]
  field_simp

theorem convergence_for_input (p s : ℕ) (hp : 2 ≤ p) (x u : ℝ) (hx : 0 < x) (hu : 0 < u) :
    Tendsto (fun n : ℕ => (update p (Dyadic.denominator p s) x)^[n] u)
      atTop (𝓝 (x^(1/(p:ℝ)))) := by
  have hp0 : (p:ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hr := rpow_pos_of_pos hx (1/(p:ℝ))
  have he : (x^(1/(p:ℝ)))^(p:ℝ)=x := by rw [one_div,rpow_inv_rpow hx.le hp0]
  simpa only [he] using convergence p s hp (x^(1/(p:ℝ))) u hr hu

end LeanMath.Papers.GuardedCenter
