import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic

/-! # Exponential sums and the contact lemma (Lemma 2.1)

Two analytic tools, both stated in the variable `x = log t`.

* `expSum_isBigO`: a finite sum `∑ c_j exp (λ_j x)` whose first `N` moments `∑ c_j λ_j ^ n` vanish
  is `O (x ^ N)` at zero.
* `contact_limit`: Lemma 2.1 of the paper. If a support `κ` has contact of order `ω ≥ 1` with the
  exact support `kappaStarX`, with constant `C`, then the logarithmic error of the update satisfies
  `gap / x ^ (ω + 1) → -C / p ^ 2`. -/

noncomputable section
namespace LeanMath.Papers.ContactLimit
open Filter Asymptotics Finset
open scoped Topology

/-! ## Exponential sums -/

def taylorExp (N : ℕ) (y : ℝ) : ℝ := ∑ i ∈ range N, y ^ i / (i.factorial : ℝ)

theorem exp_scaled_isBigO (lam : ℝ) (N : ℕ) :
    (fun x : ℝ => Real.exp (lam * x) - taylorExp N (lam * x)) =O[𝓝 0] (fun x => x ^ N) := by
  have h0 : Tendsto (fun x : ℝ => lam * x) (𝓝 0) (𝓝 0) := by
    have hc : Continuous fun x : ℝ => lam * x := by fun_prop
    simpa using hc.tendsto 0
  have h1 := (Real.exp_sub_sum_range_isBigO_pow N).comp_tendsto h0
  have h2 : (fun x : ℝ => (lam * x) ^ N) =O[𝓝 0] (fun x => x ^ N) := by
    simp_rw [mul_pow]
    exact isBigO_const_mul_self (lam ^ N) _ _
  exact h1.trans h2

def expSum (l : List (ℝ × ℝ)) (x : ℝ) : ℝ := (l.map fun cl => cl.1 * Real.exp (cl.2 * x)).sum
def moment (l : List (ℝ × ℝ)) (n : ℕ) : ℝ := (l.map fun cl => cl.1 * cl.2 ^ n).sum
def remSum (l : List (ℝ × ℝ)) (N : ℕ) (x : ℝ) : ℝ :=
  (l.map fun cl => cl.1 * (Real.exp (cl.2 * x) - taylorExp N (cl.2 * x))).sum
def taySum (l : List (ℝ × ℝ)) (N : ℕ) (x : ℝ) : ℝ :=
  (l.map fun cl => cl.1 * taylorExp N (cl.2 * x)).sum

theorem expSum_split (l : List (ℝ × ℝ)) (N : ℕ) (x : ℝ) :
    expSum l x = remSum l N x + taySum l N x := by
  unfold expSum remSum taySum
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    ring

theorem taySum_eq (l : List (ℝ × ℝ)) (N : ℕ) (x : ℝ) :
    taySum l N x = ∑ i ∈ range N, moment l i * (x ^ i / (i.factorial : ℝ)) := by
  unfold taySum moment
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih, taylorExp, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_pow]
    ring

theorem remSum_isBigO (l : List (ℝ × ℝ)) (N : ℕ) :
    (remSum l N) =O[𝓝 0] (fun x => x ^ N) := by
  unfold remSum
  induction l with
  | nil => simpa using isBigO_zero (fun x : ℝ => x ^ N) (𝓝 (0 : ℝ))
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons]
    exact ((exp_scaled_isBigO hd.2 N).const_mul_left hd.1).add ih

/-- A finite exponential sum with `N` vanishing moments is `O (x ^ N)` at zero. -/
theorem expSum_isBigO (l : List (ℝ × ℝ)) (N : ℕ) (h : ∀ n < N, moment l n = 0) :
    (expSum l) =O[𝓝 0] (fun x => x ^ N) := by
  have hz : ∀ x, taySum l N x = 0 := by
    intro x
    rw [taySum_eq]
    apply Finset.sum_eq_zero
    intro i hi
    rw [h i (Finset.mem_range.mp hi), zero_mul]
  have he : expSum l = remSum l N := by
    funext x
    rw [expSum_split l N x, hz x, add_zero]
  rw [he]
  exact remSum_isBigO l N

/-- Consequence used below: divided by a lower power the sum tends to zero. -/
theorem expSum_tendsto_zero (l : List (ℝ × ℝ)) (N M : ℕ) (hMN : M < N)
    (h : ∀ n < N, moment l n = 0) :
    Tendsto (fun x : ℝ => expSum l x / x ^ M) (𝓝[≠] 0) (𝓝 0) := by
  have h1 := (expSum_isBigO l N h).trans_isLittleO (isLittleO_pow_pow hMN)
  exact h1.tendsto_div_nhds_zero.mono_left nhdsWithin_le_nhds

/-! ## Elementary limits at zero -/

theorem tendsto_exp_scaled (c : ℝ) :
    Tendsto (fun x : ℝ => (Real.exp (c * x) - 1) / x) (𝓝[≠] 0) (𝓝 c) := by
  have hd : HasDerivAt (fun x : ℝ => Real.exp (c * x)) c 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).const_mul c).exp
    simpa using this
  have := hasDerivAt_iff_tendsto_slope.mp hd
  refine this.congr fun x => ?_
  simp [slope_def_field]

theorem tendsto_exp_sub_one_div :
    Tendsto (fun x : ℝ => (Real.exp x - 1) / x) (𝓝[≠] 0) (𝓝 1) := by
  simpa using tendsto_exp_scaled 1

theorem tendsto_pow_zero (n : ℕ) (hn : 1 ≤ n) :
    Tendsto (fun x : ℝ => x ^ n) (𝓝[≠] 0) (𝓝 0) := by
  have := ((continuous_pow n : Continuous fun x : ℝ => x ^ n).tendsto 0).mono_left
    (nhdsWithin_le_nhds (s := {0}ᶜ))
  simpa [zero_pow (by omega : n ≠ 0)] using this

theorem tendsto_exp_one (c : ℝ) :
    Tendsto (fun x : ℝ => Real.exp (c * x)) (𝓝[≠] 0) (𝓝 1) := by
  have hc : Continuous fun x : ℝ => Real.exp (c * x) := by fun_prop
  have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
  simpa using this

/-! ## The contact lemma -/

/-- The exact support in the variable `x = log t`: `(t - 1) / (t ^ (1/p) - 1)`. -/
def kappaStarX (p x : ℝ) : ℝ := (Real.exp x - 1) / (Real.exp (x / p) - 1)

theorem tendsto_kappaStarX (p : ℝ) (hp : 0 < p) :
    Tendsto (kappaStarX p) (𝓝[≠] 0) (𝓝 p) := by
  have h1 := tendsto_exp_sub_one_div
  have h2 := tendsto_exp_scaled (1 / p)
  have hne : (1 / p : ℝ) ≠ 0 := by positivity
  have h3 := h1.div h2 hne
  have e : (1 : ℝ) / (1 / p) = p := by field_simp
  rw [e] at h3
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := hx
  unfold kappaStarX
  have : 1 / p * x = x / p := by ring
  simp only [Pi.div_apply, this]
  field_simp

/-- Lemma 2.1. Let `κ` be a support, given as a function of `x = log t`, with
`(κ - kappaStarX) / x ^ ω → C` for some `ω ≥ 1`. Then the logarithmic error of the update
`u ↦ u (κ - 1 + t) / κ`, namely `log ((κ - 1 + t) / κ) - x / p`, divided by `x ^ (ω + 1)`, tends to
`-C / p ^ 2`. -/
theorem contact_limit (κ : ℝ → ℝ) (p : ℝ) (hp : 0 < p) (ω : ℕ) (hω : 1 ≤ ω) (C : ℝ)
    (hκ : Tendsto (fun x : ℝ => (κ x - kappaStarX p x) / x ^ ω) (𝓝[≠] 0) (𝓝 C)) :
    Tendsto (fun x : ℝ => (Real.log ((κ x - 1 + Real.exp x) / κ x) - x / p) / x ^ (ω + 1))
      (𝓝[≠] 0) (𝓝 (-C / p ^ 2)) := by
  have hks := tendsto_kappaStarX p hp
  have hpow := tendsto_pow_zero ω hω
  -- κ - κ* → 0 and κ → p
  have hdiff : Tendsto (fun x : ℝ => κ x - kappaStarX p x) (𝓝[≠] 0) (𝓝 0) := by
    have := hκ.mul hpow
    rw [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := hx
    have : x ^ ω ≠ 0 := pow_ne_zero _ hx0
    field_simp
  have hκp : Tendsto κ (𝓝[≠] 0) (𝓝 p) := by
    have := hdiff.add hks
    rw [zero_add] at this
    refine this.congr fun x => ?_
    ring
  have hΘ : Tendsto (fun x : ℝ => Real.exp (x / p)) (𝓝[≠] 0) (𝓝 1) := by
    refine (tendsto_exp_one (1 / p)).congr fun x => ?_
    congr 1
    ring
  -- the relative defect y
  set y : ℝ → ℝ := fun x =>
    -((Real.exp x - 1) * (κ x - kappaStarX p x)) / (κ x * kappaStarX p x * Real.exp (x / p))
    with hy
  have hyq : Tendsto (fun x : ℝ => y x / x ^ (ω + 1)) (𝓝[≠] 0) (𝓝 (-C / p ^ 2)) := by
    have hden : Tendsto (fun x : ℝ => κ x * kappaStarX p x * Real.exp (x / p)) (𝓝[≠] 0)
        (𝓝 (p * p * 1)) := (hκp.mul hks).mul hΘ
    have hnum := (tendsto_exp_sub_one_div.mul hκ).neg
    have hq := hnum.div hden (by positivity)
    have e : -(1 * C) / (p * p * 1) = -C / p ^ 2 := by ring
    rw [e] at hq
    refine hq.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := hx
    simp only [hy, Pi.div_apply, pow_succ]
    have hxw : x ^ ω ≠ 0 := pow_ne_zero _ hx0
    field_simp
  have hy0 : Tendsto y (𝓝[≠] 0) (𝓝 0) := by
    have := hyq.mul (tendsto_pow_zero (ω + 1) (by omega))
    rw [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := hx
    have : x ^ (ω + 1) ≠ 0 := pow_ne_zero _ hx0
    field_simp
  -- log (1 + y) = y * L y with L continuous at 0, L 0 = 1
  set f : ℝ → ℝ := fun z => Real.log (1 + z) with hf
  have hfd : HasDerivAt f 1 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).const_add 1).log (by norm_num)
    simpa using this
  have hLc : ContinuousAt (dslope f 0) 0 := continuousAt_dslope_same.mpr hfd.differentiableAt
  have hL0 : dslope f 0 0 = 1 := by rw [dslope_same, hfd.deriv]
  have hL : Tendsto (fun x : ℝ => dslope f 0 (y x)) (𝓝[≠] 0) (𝓝 1) := by
    have := hLc.tendsto.comp hy0
    rwa [hL0] at this
  have hlog : ∀ z : ℝ, Real.log (1 + z) = z * dslope f 0 z := by
    intro z
    have := sub_smul_dslope f 0 z
    simp only [hf, sub_zero, smul_eq_mul, add_zero, Real.log_one] at this
    linarith
  have hmain := hL.mul hyq
  rw [one_mul] at hmain
  refine hmain.congr' ?_
  -- eventually the update factor is exp (x / p) * (1 + y)
  have hκne : ∀ᶠ x in 𝓝[≠] 0, κ x ≠ 0 := hκp.eventually_ne hp.ne'
  have hksne : ∀ᶠ x in 𝓝[≠] 0, kappaStarX p x ≠ 0 := hks.eventually_ne hp.ne'
  have hypos : ∀ᶠ x in 𝓝[≠] 0, -1 < y x := hy0.eventually (lt_mem_nhds (by norm_num))
  filter_upwards [self_mem_nhdsWithin, hκne, hksne, hypos] with x hx hk hks' hy1
  have hx0 : x ≠ 0 := hx
  have hE : Real.exp x - 1 ≠ 0 := by
    intro h0
    have : Real.exp x = Real.exp 0 := by rw [Real.exp_zero]; linarith
    exact hx0 (Real.exp_injective this)
  have hT : Real.exp (x / p) - 1 ≠ 0 := by
    intro h0
    have : Real.exp (x / p) = Real.exp 0 := by rw [Real.exp_zero]; linarith
    have := Real.exp_injective this
    exact hx0 (by field_simp at this; linarith)
  have hΘpos := Real.exp_pos (x / p)
  have hfac : (κ x - 1 + Real.exp x) / κ x = Real.exp (x / p) * (1 + y x) := by
    have hstar : kappaStarX p x * (Real.exp (x / p) - 1) = Real.exp x - 1 := by
      unfold kappaStarX
      field_simp
    simp only [hy]
    field_simp
    linear_combination (-(κ x)) * hstar
  have h1y : 0 < 1 + y x := by linarith
  rw [hfac, Real.log_mul hΘpos.ne' h1y.ne', Real.log_exp, hlog (y x)]
  ring

end LeanMath.Papers.ContactLimit
