import LeanMath.Papers.V14Cell

/-! Physical positive iterates for the guarded center-defect solver. -/
noncomputable section
namespace LeanMath.Papers.V14Solver
open Real Filter Function
open scoped Topology
open LeanMath.Papers
open V14Local

/-- The normalized logarithmic error, with target root `r`. -/
def error (r u : ℝ) := log (u/r)

/-- The physical solver uses the exact residual `(r/u)^p`. -/
def step (i : Index) (p s : ℕ) (r u : ℝ) :=
  if |error r u| ≤ RealBracket.Local.radius p then
    u * correction i p ((r/u)^(p:ℝ))
  else u * Dyadic.correction p (Dyadic.denominator p s) ((r/u)^(p:ℝ))

theorem residual_eq (p r u : ℝ) (hr : 0 < r) (hu : 0 < u) :
    (r/u)^p = exp (-p * error r u) := by
  rw [rpow_def_of_pos (div_pos hr hu)]
  have hh : log (r/u) = -log (u/r) := by
    rw [log_div hr.ne' hu.ne',log_div hu.ne' hr.ne']; ring
  rw [hh]; congr 1; unfold error; ring

theorem local_correction_pos (i : Index) (p r u : ℝ) (hp : 3 ≤ p)
    (hr : 0 < r) (hu : 0 < u) (he : |error r u| ≤ RealBracket.Local.radius p) :
    0 < correction i p ((r/u)^p) := by
  rw [residual_eq p r u hr hu]
  have ha := V14Defect.a_mem p (by linarith)
  have hq := V14Cell.Q_mem i _ _ ha.1 ha.2 (V14Cell.coordinate_small p _ hp he)
  exact mul_pos (RealBracket.center_pos p _ (by linarith) (exp_pos _))
    (Cayley.unchi_pos _ hq)

theorem step_pos (i : Index) (p s : ℕ) (r u : ℝ) (hp : 3 ≤ p)
    (hr : 0 < r) (hu : 0 < u) : 0 < step i p s r u := by
  unfold step
  split_ifs with he
  · exact mul_pos hu (local_correction_pos i p r u (by exact_mod_cast hp) hr hu he)
  · exact mul_pos hu (rpow_pos_of_pos (rpow_pos_of_pos (div_pos hr hu) _) _)

/-- Exact conjugacy, including the dyadic fallback branch. -/
theorem step_error (i : Index) (p s : ℕ) (r u : ℝ) (hp : 3 ≤ p)
    (hr : 0 < r) (hu : 0 < u) :
    error r (step i p s r u) =
      Hybrid.step (rootLogError i p) (Dyadic.rho p (Dyadic.denominator p s))
        (RealBracket.Local.radius p) (error r u) := by
  unfold step Hybrid.step
  split_ifs with he
  · have hc := local_correction_pos i p r u (by exact_mod_cast hp) hr hu he
    change log ((u * correction i p ((r/u)^(p:ℝ)))/r) = _
    rw [log_div (mul_pos hu hc).ne' hr.ne',log_mul hu.ne' hc.ne']
    rw [residual_eq (p:ℝ) r u hr hu]
    unfold rootLogError error
    rw [log_div hu.ne' hr.ne']; ring
  · exact Dyadic.log_error_linear p (Dyadic.denominator p s) r u hr hu

theorem iterate_pos (i : Index) (p s : ℕ) (r u : ℝ) (hp : 3 ≤ p)
    (hr : 0 < r) (hu : 0 < u) (n : ℕ) : 0 < (step i p s r)^[n] u := by
  induction n with
  | zero => exact hu
  | succ n ih => rw [iterate_succ_apply']; exact step_pos i p s r _ hp hr ih

theorem iterate_error (i : Index) (p s : ℕ) (r u : ℝ) (hp : 3 ≤ p)
    (hr : 0 < r) (hu : 0 < u) (n : ℕ) :
    error r ((step i p s r)^[n] u) =
      (Hybrid.step (rootLogError i p) (Dyadic.rho p (Dyadic.denominator p s))
        (RealBracket.Local.radius p))^[n] (error r u) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply',iterate_succ_apply',
      step_error i p s r _ hp hr (iterate_pos i p s r u hp hr hu n),ih]

/-- Corollary 9.6 for actual positive approximations, from every positive start. -/
theorem solver_convergence (i : Index) (p s : ℕ) (r u : ℝ) (hp : 3 ≤ p)
    (hr : 0 < r) (hu : 0 < u) :
    Tendsto (fun n : ℕ => (step i p s r)^[n] u) atTop (𝓝 r) := by
  have he := V14Cell.global_convergence i p s hp (error r u)
  have ht := (Real.continuous_exp.tendsto 0).comp he
  have hh := ht.const_mul r
  simp only [exp_zero,mul_one] at hh
  convert! hh using 1
  funext n
  simp only [Function.comp_apply]
  rw [← iterate_error i p s r u hp hr hu n]
  unfold error
  rw [exp_log (div_pos (iterate_pos i p s r u hp hr hu n) hr)]
  field_simp

/-- Replace the target-root residual by the executable residual `X/u^p`. -/
theorem residual_of_radicand (X u : ℝ) (p : ℕ) (hX : 0 < X) (hu : 0 < u)
    (hp : 0 < p) : ((X^(1/(p:ℝ)))/u)^(p:ℝ) = X/u^p := by
  rw [div_rpow (rpow_nonneg hX.le _) hu.le,← rpow_mul hX.le]
  have hp0 : (p:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
  rw [one_div_mul_cancel hp0,rpow_one,rpow_natCast]

/-- Algorithm expressed entirely in its inputs, without a root oracle. -/
def solveStep (i : Index) (p s : ℕ) (X u : ℝ) :=
  let R := X/u^p
  if |log R| ≤ log (1+1/sqrt (p:ℝ)) then
    u * correction i p R
  else u * Dyadic.correction p (Dyadic.denominator p s) R

theorem executable_step (i : Index) (p s : ℕ) (X u : ℝ) (hp : 3 ≤ p)
    (hX : 0 < X) (hu : 0 < u) :
    solveStep i p s X u = step i p s (X^(1/(p:ℝ))) u := by
  have hp0 : (0:ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hr := rpow_pos_of_pos hX (1/(p:ℝ))
  have hR := residual_of_radicand X u p hX hu (by omega)
  have hlog : log (X/u^p) = -(p:ℝ)*error (X^(1/(p:ℝ))) u := by
    rw [← hR,residual_eq _ _ _ hr hu,log_exp]
  have hguard : |log (X/u^p)| ≤ log (1+1/sqrt (p:ℝ)) ↔
      |error (X^(1/(p:ℝ))) u| ≤ RealBracket.Local.radius p := by
    rw [hlog,abs_mul,abs_neg,abs_of_pos hp0]
    unfold RealBracket.Local.radius
    rw [le_div_iff₀ hp0]
    rw [mul_comm]
  unfold solveStep step
  dsimp only
  simp only [hguard,hR]

theorem solveStep_convergence (i : Index) (p s : ℕ) (X u : ℝ) (hp : 3 ≤ p)
    (hX : 0 < X) (hu : 0 < u) :
    Tendsto (fun n : ℕ => (solveStep i p s X)^[n] u) atTop (𝓝 (X^(1/(p:ℝ)))) := by
  have hr := rpow_pos_of_pos hX (1/(p:ℝ))
  have heq : ∀ n : ℕ, (solveStep i p s X)^[n] u = (step i p s (X^(1/(p:ℝ))))^[n] u := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [iterate_succ_apply',iterate_succ_apply',ih,
        executable_step i p s X _ hp hX (iterate_pos i p s _ u hp hr hu n)]
  simpa only [heq] using solver_convergence i p s _ u hp hr hu

end LeanMath.Papers.V14Solver
