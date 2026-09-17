import LeanMath.Papers.MultivariateGuard

/-! Explicit Newton damping from a quantitative Taylor remainder.
No contraction of the Euler map or sign pattern of the Jacobian is assumed. -/
noncomputable section
namespace LeanMath.Papers.DampedNewton
open Function Filter
open scoped Topology

def damping (a t : ℝ) := if t = 0 then 1 else min 1 (a*t)⁻¹

theorem damping_pos (a t : ℝ) (ha : 0 < a) (ht : 0 ≤ t) : 0 < damping a t := by
  unfold damping
  split_ifs with hz
  · norm_num
  · exact lt_min zero_lt_one (inv_pos.mpr (mul_pos ha (lt_of_le_of_ne ht (Ne.symm hz))))

theorem damping_le_one (a t : ℝ) : damping a t ≤ 1 := by
  unfold damping
  split_ifs <;> simp [min_le_left]

theorem damping_budget (a t : ℝ) (ha : 0 < a) (ht : 0 ≤ t) : damping a t * (a*t) ≤ 1 := by
  by_cases hz : t = 0
  · simp [hz,damping]
  have hp : 0 < a*t := mul_pos ha (lt_of_le_of_ne ht (Ne.symm hz))
  have hle : damping a t ≤ (a*t)⁻¹ := by simp only [damping,if_neg hz]; exact min_le_right _ _
  have h := mul_le_mul_of_nonneg_right hle hp.le
  simpa only [inv_mul_cancel₀ hp.ne'] using h

theorem damping_lower_on_sublevel (a t t₀ : ℝ) (ha : 0 < a) (ht : 0 ≤ t)
    (ht₀ : 0 < t₀) (hle : t ≤ t₀) : damping a t₀ ≤ damping a t := by
  by_cases hz : t = 0
  · simpa [hz,damping] using damping_le_one a t₀
  have hp : 0 < t := lt_of_le_of_ne ht (Ne.symm hz)
  simp only [damping,if_neg hz,if_neg ht₀.ne']
  apply min_le_min_left
  exact inv_anti₀ (mul_pos ha hp) (mul_le_mul_of_nonneg_left hle ha.le)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- One-step descent for the explicit damping. The quadratic Taylor remainder is
stated at the actual damped trial, so its domain and constant are visible. -/
theorem residual_descent (R : E → E) (J : E →L[ℝ] E) (x s : E) (H K : ℝ)
    (hH : 0 < H) (hK : 0 < K) (hNewton : J s = -R x)
    (hs : ‖s‖ ≤ K * ‖R x‖)
    (hrem : let lam := damping (H*K^2) ‖R x‖
      ‖R (x+lam • s)-R x-lam • J s‖ ≤ (H/2)*lam^2*‖s‖^2) :
    let lam := damping (H*K^2) ‖R x‖
    ‖R (x+lam • s)‖ ≤ (1-lam/2)*‖R x‖ := by
  let lam := damping (H*K^2) ‖R x‖
  have ha : 0 < H*K^2 := mul_pos hH (sq_pos_of_pos hK)
  have hl := (damping_pos (H*K^2) ‖R x‖ ha (norm_nonneg _)).le
  have hl1 := damping_le_one (H*K^2) ‖R x‖
  have hb := damping_budget (H*K^2) ‖R x‖ ha (norm_nonneg _)
  change 0 ≤ lam at hl
  change lam ≤ 1 at hl1
  change lam * (H*K^2*‖R x‖) ≤ 1 at hb
  change ‖R (x+lam • s)-R x-lam • J s‖ ≤ (H/2)*lam^2*‖s‖^2 at hrem
  have he : R (x+lam • s) = (R (x+lam • s)-R x-lam • J s) + (1-lam) • R x := by
    rw [hNewton, smul_neg, sub_smul, one_smul]
    abel
  have hs2 : ‖s‖^2 ≤ K^2 * ‖R x‖^2 := by nlinarith [norm_nonneg s]
  have hr : (H/2)*lam^2*‖s‖^2 ≤ (H/2)*lam^2*(K^2*‖R x‖^2) := by gcongr
  have hb2 := mul_le_mul_of_nonneg_right hb (mul_nonneg hl (norm_nonneg (R x)))
  change ‖R (x+lam • s)‖ ≤ (1-lam/2)*‖R x‖
  calc
    ‖R (x+lam • s)‖ ≤ ‖R (x+lam • s)-R x-lam • J s‖ + ‖(1-lam) • R x‖ := by
      conv_lhs => rw [he]
      exact norm_add_le _ _
    _ ≤ (1-lam/2)*‖R x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hl1)]
      nlinarith

theorem sublevel_factor (r : E → ℝ) (f : E → E) (a t₀ : ℝ)
    (ha : 0 < a) (ht₀ : 0 < t₀) (hr : ∀ x, 0 ≤ r x)
    (hstep : ∀ x, r (f x) ≤ (1-damping a (r x)/2)*r x)
    (x : E) (hx : r x ≤ t₀) :
    r (f x) ≤ (1-damping a t₀/2)*r x := by
  have h := damping_lower_on_sublevel a (r x) t₀ ha (hr x) ht₀ hx
  have hm := mul_le_mul_of_nonneg_right h (hr x)
  nlinarith [hstep x]

theorem orbit_residual_bound (r : E → ℝ) (f : E → E) (a : ℝ) (x₀ : E)
    (ha : 0 < a) (ht₀ : 0 < r x₀) (hr : ∀ x, 0 ≤ r x)
    (hstep : ∀ x, r (f x) ≤ (1-damping a (r x)/2)*r x) (k : ℕ) :
    r (f^[k] x₀) ≤ (1-damping a (r x₀)/2)^k * r x₀ ∧ r (f^[k] x₀) ≤ r x₀ := by
  let q := 1-damping a (r x₀)/2
  have hq : 0 ≤ q := by dsimp [q]; linarith [damping_le_one a (r x₀)]
  have hq1 : q ≤ 1 := by dsimp [q]; linarith [damping_pos a (r x₀) ha ht₀.le]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iterate_succ_apply']
    have hs := sublevel_factor r f a (r x₀) ha ht₀ hr hstep (f^[k] x₀) ih.2
    change r (f (f^[k] x₀)) ≤ q * r (f^[k] x₀) at hs
    have hh := mul_le_mul_of_nonneg_left ih.1 hq
    constructor
    · calc
        _ ≤ q * r (f^[k] x₀) := hs
        _ ≤ q * (q^k * r x₀) := hh
        _ = q^(k+1) * r x₀ := by ring
    · have hh' := mul_le_mul_of_nonneg_right hq1 (hr (f^[k] x₀))
      nlinarith [ih.2]

theorem orbit_converges (r : E → ℝ) (f : E → E) (a σ : ℝ) (x₀ z : E)
    (ha : 0 < a) (hσ : 0 < σ) (ht₀ : 0 < r x₀) (hr : ∀ x, 0 ≤ r x)
    (hstep : ∀ x, r (f x) ≤ (1-damping a (r x)/2)*r x)
    (hlower : ∀ x, σ * ‖x-z‖ ≤ r x) :
    Tendsto (fun k => f^[k] x₀) atTop (𝓝 z) := by
  let q := 1-damping a (r x₀)/2
  have hq : 0 ≤ q := by dsimp [q]; linarith [damping_le_one a (r x₀)]
  have hq1 : q < 1 := by dsimp [q]; linarith [damping_pos a (r x₀) ha ht₀.le]
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1).mul_const (r x₀)
  have he : ∀ᶠ k : ℕ in atTop, q^k * r x₀ < σ*ε :=
    (tendsto_order.mp ht).2 (σ*ε) (by simpa using mul_pos hσ hε)
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  refine ⟨N,fun k hk => ?_⟩
  rw [dist_eq_norm]
  have hb := (orbit_residual_bound r f a x₀ ha ht₀ hr hstep k).1
  have hl := hlower (f^[k] x₀)
  have hh := hN k hk
  nlinarith

def guarded (r : E → ℝ) (N S : E → E) (a : ℝ) (x : E) :=
  if r (N x) ≤ (1-damping a (r x)/2)*r x then N x else S x

theorem guarded_descent (r : E → ℝ) (N S : E → E) (a : ℝ)
    (hS : ∀ x, r (S x) ≤ (1-damping a (r x)/2)*r x) (x : E) :
    r (guarded r N S a x) ≤ (1-damping a (r x)/2)*r x := by
  unfold guarded
  split_ifs with h
  · exact h
  · exact hS x

theorem guarded_accepts_half (r : E → ℝ) (N S : E → E) (a : ℝ) (x : E)
    (hr : 0 ≤ r x) (hN : r (N x) ≤ (1/2:ℝ)*r x) :
    guarded r N S a x = N x := by
  have h := damping_le_one a (r x)
  have hh := mul_le_mul_of_nonneg_right h hr
  unfold guarded
  exact if_pos (by nlinarith)

end LeanMath.Papers.DampedNewton
