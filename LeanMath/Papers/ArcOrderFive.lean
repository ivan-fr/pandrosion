import LeanMath.Papers.NestedOrderNine
import LeanMath.Papers.DecenteredArcGlobal

/-! # Local order five of the decentered-arc iteration (Theorem 3.1, local part)

For every real `p > 2` the logarithmic error of the decentered-arc iteration satisfies
`ê₊ / ê ^ 5 → (p - 2)(p² - 1)(3p + 1) / 1440`. The proof is the one of `NestedOrderNine`, two orders
lower: here `q ^ 2 / t = 1 + a w` exactly, and `Y = 1 + a w + A₂ w² + o (w²)`. -/

noncomputable section
namespace LeanMath.Papers.ArcOrderFive
open Filter Asymptotics
open scoped Topology
open LeanMath.Papers.ContactLimit LeanMath.Papers.NestedOrderNine
open LeanMath.Papers.DecenteredArcGlobal
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

def P2 (h w : ℝ) : ℝ := 1 + aH h * w + A2H h * w ^ 2
def Q5 (h t : ℝ) : ℝ := t ^ 2 + aH h * (t - 1) ^ 2 * t + A2H h * (t - 1) ^ 4

/-- Coefficients of the exponential sum `h² t² (t - θ)² - (1 - h)² t (θ - 1)² Q5 h t`. -/
def L5 (h : ℝ) : List (ℝ × ℕ × ℕ) :=
  [(-(h - 1)^2*(h + 1)*(h + 3)*(2*h - 1)/720, 5, 2),
    ((h - 1)^2*(h + 1)*(h + 3)*(2*h - 1)/360, 5, 1),
    (-(h - 1)^2*(h + 1)*(h + 3)*(2*h - 1)/720, 5, 0),
    ((h - 1)^2*(2*h - 1)*(h^2 + 4*h + 18)/180, 4, 2),
    (-(h - 1)^2*(2*h - 1)*(h^2 + 4*h + 18)/90, 4, 1),
    ((h + 1)*(2*h^4 + h^3 + 19*h^2 + 86*h - 18)/180, 4, 0),
    (-(h - 1)^2*(2*h^3 + 7*h^2 + 42*h + 97)/120, 3, 2),
    ((2*h - 1)*(h^4 + 2*h^3 + 16*h^2 - 42*h - 97)/60, 3, 1),
    (-(h - 1)^2*(2*h^3 + 7*h^2 + 42*h + 97)/120, 3, 0),
    ((h + 1)*(2*h^4 + h^3 + 19*h^2 + 86*h - 18)/180, 2, 2),
    (-(h - 1)^2*(2*h - 1)*(h^2 + 4*h + 18)/90, 2, 1),
    ((h - 1)^2*(2*h - 1)*(h^2 + 4*h + 18)/180, 2, 0),
    (-(h - 1)^2*(h + 1)*(h + 3)*(2*h - 1)/720, 1, 2),
    ((h - 1)^2*(h + 1)*(h + 3)*(2*h - 1)/360, 1, 1),
    (-(h - 1)^2*(h + 1)*(h + 3)*(2*h - 1)/720, 1, 0)]

theorem L5_poly (h x : ℝ) :
    monoSum h (L5 h) x
      = h ^ 2 * Real.exp x ^ 2 * (Real.exp x - Real.exp (h * x)) ^ 2
        - (1 - h) ^ 2 * Real.exp x * (Real.exp (h * x) - 1) ^ 2 * Q5 h (Real.exp x) := by
  simp only [monoSum, L5, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Q5, aH, A2H]
  ring

theorem L5_moments (h : ℝ) : ∀ n < 8, moment (toExp h (L5 h)) n = 0 := by
  intro n hn
  interval_cases n <;>
    simp only [moment, toExp, L5, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] <;>
    push_cast <;> ring

theorem exp_ne (h x : ℝ) (hh0 : h ≠ 0) (hx : x ≠ 0) : Real.exp (h * x) - 1 ≠ 0 := by
  intro h0
  have : Real.exp (h * x) = Real.exp 0 := by rw [Real.exp_zero]; linarith
  have := Real.exp_injective this
  rcases mul_eq_zero.mp this with h' | h'
  · exact hh0 h'
  · exact hx h'

theorem Y_sub_P2 (h x : ℝ) (hh1 : h ≠ 1) (hx : x ≠ 0) (hh0 : h ≠ 0) :
    Yx h x - P2 h (wx x)
      = monoSum h (L5 h) x
        / ((1 - h) ^ 2 * (Real.exp (h * x) - 1) ^ 2 * Real.exp x ^ 3) := by
  have hE : Real.exp x ≠ 0 := (Real.exp_pos x).ne'
  have h1 : (1 - h) ≠ 0 := sub_ne_zero.mpr (Ne.symm hh1)
  have hT := exp_ne h x hh0 hx
  rw [L5_poly]
  unfold Yx P2 Q5 wx NestedRadicalReal.width
  field_simp

/-- `Y - (1 + a w + A₂ w²) = o (w ^ 2)`. -/
theorem Y_limit2 (h : ℝ) (hh0 : 0 < h) (hh1 : h < 1) :
    Tendsto (fun x : ℝ => (Yx h x - P2 h (wx x)) / wx x ^ 2) (𝓝[≠] 0) (𝓝 0) := by
  have hH := expSum_tendsto_zero (toExp h (L5 h)) 8 6 (by norm_num) (L5_moments h)
  have hT := tendsto_exp_scaled h
  have hE := tendsto_exp_sub_one_div
  have hE1 : Tendsto (fun x : ℝ => Real.exp x) (𝓝[≠] 0) (𝓝 1) := by
    simpa using tendsto_exp_one 1
  have hden := ((tendsto_const_nhds (x := (1 - h) ^ 2)).mul (hT.pow 2)).mul hE1 |>.mul (hE.pow 4)
  have hne : (1 - h) ^ 2 * h ^ 2 * 1 * 1 ^ 4 ≠ 0 := by
    have : (1 - h) ≠ 0 := by linarith
    positivity
  have hq := hH.div hden hne
  rw [zero_div] at hq
  refine hq.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := hx
  have hEne : Real.exp x ≠ 0 := (Real.exp_pos x).ne'
  have hE1ne : Real.exp x - 1 ≠ 0 := by
    intro h0
    have : Real.exp x = Real.exp 0 := by rw [Real.exp_zero]; linarith
    exact hx0 (Real.exp_injective this)
  have hTne := exp_ne h x hh0.ne' hx0
  have h1 : (1 - h) ≠ 0 := by linarith
  rw [Y_sub_P2 h x hh1.ne hx0 hh0.ne']
  simp only [Pi.div_apply, wx, NestedRadicalReal.width]
  rw [← monoSum_eq]
  field_simp

/-- The arc radicand is exactly linear in `w`: `q ^ 2 = t (1 + a w)`. -/
theorem rad_eq (p x : ℝ) (hp : 2 < p) :
    rad p (Real.exp x) = Real.exp x * (1 + aH (1 / p) * wx x) := by
  have hp0 : p ≠ 0 := by linarith
  have hE : Real.exp x ≠ 0 := (Real.exp_pos x).ne'
  unfold rad wx NestedRadicalReal.width aH
  field_simp
  ring

def kappa5 (p x : ℝ) : ℝ := 1 + (p - 1) * support p (Real.exp x)

/-- The decentered-arc support has contact of order four with the exact support. -/
theorem contact_five (p : ℝ) (hp : 2 < p) :
    Tendsto (fun x : ℝ => (kappa5 p x - kappaStarX p x) / x ^ 4) (𝓝[≠] 0)
      (𝓝 ((p - 1) * (-A2H (1 / p)) / 2)) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hh0 : (0 : ℝ) < 1 / p := by positivity
  have hh1 : (1 : ℝ) / p < 1 := by
    rw [div_lt_one hp0]
    linarith
  have hRY : Tendsto (fun x : ℝ => (1 + aH (1 / p) * wx x - Yx (1 / p) x) / wx x ^ 2)
      (𝓝[≠] 0) (𝓝 (-A2H (1 / p))) := by
    have h := (tendsto_const_nhds (x := -A2H (1 / p))).sub (Y_limit2 (1 / p) hh0 hh1)
    rw [sub_zero] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hw := (wx_pos x hx).ne'
    unfold P2
    field_simp
    ring
  have hE1 : Tendsto (fun x : ℝ => Real.exp x) (𝓝[≠] 0) (𝓝 1) := by
    simpa using tendsto_exp_one 1
  have hs : Tendsto (fun x : ℝ => support p (Real.exp x)) (𝓝[≠] 0) (𝓝 1) := by
    have hc : ContinuousAt (support p) 1 := (hasDerivAt_support p 1 hp one_pos).continuousAt
    have := hc.tendsto.comp hE1
    rwa [support_one p hp] at this
  have hks := tendsto_kappaStarX p hp0
  have hstar : ∀ x : ℝ, x ≠ 0 → kappaStarX p x = 1 + (p - 1) * qStar p x := by
    intro x hx
    have hT := exp_scaled_ne p x hp0 hx
    have e : x / p = 1 / p * x := by ring
    unfold kappaStarX qStar
    rw [e]
    generalize Real.exp (1 / p * x) = T at hT ⊢
    field_simp
    ring
  have hq : Tendsto (qStar p) (𝓝[≠] 0) (𝓝 1) := by
    have := (hks.sub_const 1).div_const (p - 1)
    rw [div_self hp1.ne'] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [hstar x hx]
    field_simp
    ring
  have hwx : Tendsto (fun x : ℝ => wx x / x ^ 2) (𝓝[≠] 0) (𝓝 1) := by
    have := (tendsto_exp_sub_one_div.pow 2).div hE1 one_ne_zero
    simp only [one_pow, div_one] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := hx
    have hE := (Real.exp_pos x).ne'
    try simp only [Pi.div_apply]
    simp only [wx, NestedRadicalReal.width]
    field_simp
  have hmain := (((hE1.const_mul (p - 1)).mul hRY).mul (hwx.pow 2)).div (hs.add hq)
    (by norm_num)
  have e : (p - 1) * 1 * -A2H (1 / p) * 1 ^ 2 / (1 + 1) = (p - 1) * (-A2H (1 / p)) / 2 := by ring
  rw [e] at hmain
  refine hmain.congr' ?_
  have hsne : ∀ᶠ x in 𝓝[≠] 0, support p (Real.exp x) + qStar p x ≠ 0 :=
    (hs.add hq).eventually_ne (by norm_num)
  filter_upwards [self_mem_nhdsWithin, hsne] with x hx hsq
  have hx0 : x ≠ 0 := hx
  have hEpos := Real.exp_pos x
  have hwpos := wx_pos x hx0
  have hT := exp_scaled_ne p x hp0 hx0
  have hs2 := support_square p (Real.exp x) hp hEpos
  have hpp : (1 : ℝ) - 1 / p ≠ 0 := by linarith
  have hq2 : qStar p x ^ 2 = Real.exp x * Yx (1 / p) x := by
    unfold qStar Yx
    field_simp
  have key : (support p (Real.exp x) - qStar p x) * (support p (Real.exp x) + qStar p x)
      = Real.exp x * (1 + aH (1 / p) * wx x - Yx (1 / p) x) := by
    have hr := rad_eq p x hp
    linear_combination hs2 + hr - hq2
  try simp only [Pi.div_apply, Pi.mul_apply, Pi.add_apply, Pi.pow_apply]
  rw [hstar x hx0]
  unfold kappa5
  have h1 : (p - 1) * Real.exp x * ((1 + aH (1 / p) * wx x - Yx (1 / p) x) / wx x ^ 2)
      * (wx x / x ^ 2) ^ 2
      = (p - 1) * ((support p (Real.exp x) - qStar p x)
          * (support p (Real.exp x) + qStar p x)) / x ^ 4 := by
    rw [key]
    field_simp
  rw [h1]
  field_simp
  ring

theorem correction_eq_kappa (p x : ℝ) :
    correction p (Real.exp x) = (kappa5 p x - 1 + Real.exp x) / kappa5 p x := by
  have : kappa5 p x - 1 + Real.exp x = Real.exp x + (p - 1) * support p (Real.exp x) := by
    unfold kappa5
    ring
  rw [this]
  rfl

/-- **Theorem 3.1, local part.** For every real `p > 2`, the logarithmic error of the decentered-arc
iteration satisfies `ê₊ / ê ^ 5 → (p - 2)(p² - 1)(3p + 1) / 1440`. -/
theorem order_five (p : ℝ) (hp : 2 < p) :
    Tendsto (fun e : ℝ => (e + Real.log (correction p (Real.exp (-p * e)))) / e ^ 5) (𝓝[≠] 0)
      (𝓝 ((p - 2) * (p ^ 2 - 1) * (3 * p + 1) / 1440)) := by
  have hp0 : p ≠ 0 := by linarith
  have hx := contact_limit (kappa5 p) p (by linarith) 4 (by norm_num) _ (contact_five p hp)
  have hsub : Tendsto (fun e : ℝ => -p * e) (𝓝[≠] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hc : Continuous fun e : ℝ => -p * e := by fun_prop
      simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
    · filter_upwards [self_mem_nhdsWithin] with e he
      have he0 : e ≠ 0 := he
      exact mul_ne_zero (neg_ne_zero.mpr hp0) he0
  have h := (hx.comp hsub).const_mul ((-p) ^ 5)
  have e5 : (-p) ^ 5 * (-((p - 1) * (-A2H (1 / p)) / 2) / p ^ 2)
      = (p - 2) * (p ^ 2 - 1) * (3 * p + 1) / 1440 := by
    unfold A2H
    field_simp
    ring
  rw [e5] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with e he
  have he0 : e ≠ 0 := he
  simp only [Function.comp]
  rw [correction_eq_kappa]
  field_simp
  ring

/-- The quantity in `order_five` is the logarithmic error of one step of the iteration. -/
theorem log_error_step (p X r e : ℝ) (hp : 2 < p) (hr : 0 < r) (hX : r ^ p = X) :
    Real.log (step p X (r * Real.exp e) / r)
      = e + Real.log (correction p (Real.exp (-p * e))) := by
  have hXpos : 0 < X := by rw [← hX]; exact Real.rpow_pos_of_pos hr p
  have ht : X / (r * Real.exp e) ^ p = Real.exp (-p * e) := by
    rw [Real.mul_rpow hr.le (Real.exp_pos e).le, hX, ← Real.exp_mul, div_mul_eq_div_div,
      div_self hXpos.ne', one_div, ← Real.exp_neg]
    congr 1
    ring
  have hc := correction_positive p (Real.exp (-p * e)) hp (Real.exp_pos _)
  unfold step
  rw [ht]
  have : r * Real.exp e * correction p (Real.exp (-p * e)) / r
      = Real.exp e * correction p (Real.exp (-p * e)) := by
    field_simp
  rw [this, Real.log_mul (Real.exp_pos e).ne' hc.ne', Real.log_exp]

end LeanMath.Papers.ArcOrderFive
