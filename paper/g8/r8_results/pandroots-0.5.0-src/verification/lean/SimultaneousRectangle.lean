import Mathlib

/-! # The simultaneous rectangle (note G8): algebra of the step

For approximations `z₁, …, z_m` of the roots of a polynomial `S`, the function deflated for the index
`k` is `F_k(w) = S(w) / ∏_{l ≠ k} (w - y_l)`.  With `A = F_k'/F_k` and `B = -(F_k'/F_k)'` at `z_k`, the
rectangle step of degree `p` and support value `q` is `z_k - p / (A (1 + (p-1) q))`, the cursor being
`t = (p B - A²) / ((p-1) A²)`.

* `cursor_deflated`, `step_AK`: Proposition 2.2 (the cursor; the line `AK` gives the Ehrlich–Aberth step);
* `cursor_error`, `error_AK`, `error_support`: the exact identities of Theorem 3.1, with `A = (1+x)/e`
  and `B = (1+v)/e²` (`e` the error, `x = δ₁ e`, `v = δ₂ e²`);
* `denominator_split`: for a support `q = 1 + (t-1)/2 + r`, the denominator is
  `p (1 + (x²+v)/(2(1+x))) + (p-1)(1+x) r`: the term in `x` alone cancels for every support whose
  slope at `1` is `1/2`, and the support enters through the remainder `r` only;
* `error_AD`, `error_AD_bound`: the line `AD` (`r = 0`) exactly, `e⁺ = e (x²+v)/(2+2x+x²+v)`, and a
  quantitative form of the order four;
* `trap_step`, `trap_cube`: Proposition 7.1, the Ehrlich–Aberth step on the symmetric trap is conjugate
  to the cube. -/

namespace LeanMath.Papers.SimultaneousRectangle

section Field
variable {K : Type*} [Field K]

/-- Proposition 2.2.  With `N = 1/A` and `L = 1 - B/A²` (the Newton quotient and `F F''/F'²` of the
deflated function), the cursor `1 - p/(p-1) · L` is `(p B - A²)/((p-1) A²)`. -/
theorem cursor_deflated (A B p : K) (hA : A ≠ 0) (hp : p - 1 ≠ 0) :
    1 - p / (p - 1) * (1 - B / A ^ 2) = (p * B - A ^ 2) / ((p - 1) * A ^ 2) := by
  field_simp
  ring

/-- Proposition 2.2.  With the line `AK` (`q = 1`) the step `p / (A (1 + (p-1) q))` is `1/A`: the
Ehrlich–Aberth step. -/
theorem step_AK (A p : K) (hA : A ≠ 0) (hp : p ≠ 0) :
    p / (A * (1 + (p - 1) * 1)) = 1 / A := by
  have h : (1 : K) + (p - 1) * 1 = p := by ring
  rw [h]
  field_simp

/-- Theorem 3.1.  If `A = (1+x)/e` and `B = (1+v)/e²`, the cursor satisfies
`t - 1 = p (v - 2x - x²) / ((p-1)(1+x)²)`. -/
theorem cursor_error (e x v p : K) (he : e ≠ 0) (hx : 1 + x ≠ 0) (hp : p - 1 ≠ 0) :
    (p * ((1 + v) / e ^ 2) - ((1 + x) / e) ^ 2) / ((p - 1) * ((1 + x) / e) ^ 2) - 1
      = p * (v - 2 * x - x ^ 2) / ((p - 1) * (1 + x) ^ 2) := by
  field_simp
  ring

/-- Theorem 3.1, line `AK`.  The new error `e - 1/A` is `e · x/(1+x)`. -/
theorem error_AK (e x : K) (he : e ≠ 0) (hx : 1 + x ≠ 0) :
    e - 1 / ((1 + x) / e) = e * (x / (1 + x)) := by
  field_simp
  ring

/-- Theorem 3.1, any support value `q`.  The new error `e - p/(A (1 + (p-1) q))` is
`e (1 - p / ((1+x)(1 + (p-1) q)))`. -/
theorem error_support (e x p q : K) (he : e ≠ 0) (hx : 1 + x ≠ 0)
    (hq : 1 + (p - 1) * q ≠ 0) :
    e - p / ((1 + x) / e * (1 + (p - 1) * q))
      = e * (1 - p / ((1 + x) * (1 + (p - 1) * q))) := by
  field_simp

/-- Theorem 3.1, the cancellation.  Write the support as `q = 1 + (t-1)/2 + r` with
`t - 1 = p (v - 2x - x²)/((p-1)(1+x)²)`.  Then
`(1+x)(1 + (p-1) q) = p (1 + (x²+v)/(2(1+x))) + (p-1)(1+x) r`: no term in `x` alone, and the
support is seen through `r` only. -/
theorem denominator_split (x v p r : K) (hx : 1 + x ≠ 0) (hp : p - 1 ≠ 0) (h2 : (2 : K) ≠ 0) :
    (1 + x) * (1 + (p - 1) * (1 + p * (v - 2 * x - x ^ 2) / ((p - 1) * (1 + x) ^ 2) / 2 + r))
      = p * (1 + (x ^ 2 + v) / (2 * (1 + x))) + (p - 1) * (1 + x) * r := by
  field_simp
  ring

/-- The line `AD` exactly (`r = 0`): the new error is `e (x² + v)/(2 + 2x + x² + v)`. -/
theorem error_AD (e x v p : K) (hx : 1 + x ≠ 0) (hp : p - 1 ≠ 0) (hp0 : p ≠ 0)
    (h2 : (2 : K) ≠ 0) (hd : 2 + 2 * x + x ^ 2 + v ≠ 0) :
    e * (1 - p / ((1 + x) * (1 + (p - 1) *
        (1 + p * (v - 2 * x - x ^ 2) / ((p - 1) * (1 + x) ^ 2) / 2))))
      = e * ((x ^ 2 + v) / (2 + 2 * x + x ^ 2 + v)) := by
  have h := denominator_split x v p 0 hx hp h2
  simp only [add_zero, mul_zero] at h
  rw [h]
  have h3 : p * (1 + (x ^ 2 + v) / (2 * (1 + x))) = p * ((2 + 2 * x + x ^ 2 + v) / (2 * (1 + x))) := by
    field_simp
    ring
  have h4 : p / (p * ((2 + 2 * x + x ^ 2 + v) / (2 * (1 + x)))) = 2 * (1 + x) / (2 + 2 * x + x ^ 2 + v) := by
    rw [← div_div, div_self hp0, one_div_div]
  rw [h3, h4]
  congr 1
  rw [eq_div_iff hd, sub_mul, one_mul, div_mul_cancel₀ _ hd]
  ring

/-- Proposition 7.1.  Two real roots `x ± d`, a point at `x + w` and its mirror at `x - w`, the other
approximations on the other roots: the Ehrlich–Aberth denominator at the first point is
`1/(w-d) + 1/(w+d) - 1/(2w)` and the step sends `w` to `w (w² + 3d²)/(3w² + d²)`.
(On the trap `w = i y`: `i y ↦ i y (3d² - y²)/(d² - 3y²)`.) -/
theorem trap_step (w d : K) (hw : w ≠ 0) (h1 : w - d ≠ 0) (h2 : w + d ≠ 0)
    (h3 : 3 * w ^ 2 + d ^ 2 ≠ 0) (two : (2 : K) ≠ 0) :
    w - 1 / (1 / (w - d) + 1 / (w + d) - 1 / (2 * w)) = w * (w ^ 2 + 3 * d ^ 2) / (3 * w ^ 2 + d ^ 2) := by
  have hA : 1 / (w - d) + 1 / (w + d) - 1 / (2 * w)
      = (3 * w ^ 2 + d ^ 2) / (2 * w * ((w - d) * (w + d))) := by
    field_simp
    ring
  rw [hA, one_div_div, eq_div_iff h3, sub_mul, div_mul_cancel₀ _ h3]
  ring

/-- Proposition 7.1, the structure of the trap: in the coordinate `(w - d)/(w + d)` the step is the
cube.  For `w = i y` this coordinate has modulus one: the angle is tripled. -/
theorem trap_cube (w d : K) (h2 : w + d ≠ 0) (h3 : 3 * w ^ 2 + d ^ 2 ≠ 0) :
    (w * (w ^ 2 + 3 * d ^ 2) / (3 * w ^ 2 + d ^ 2) - d) / (w * (w ^ 2 + 3 * d ^ 2) / (3 * w ^ 2 + d ^ 2) + d)
      = ((w - d) / (w + d)) ^ 3 := by
  have hn : w * (w ^ 2 + 3 * d ^ 2) / (3 * w ^ 2 + d ^ 2) - d = (w - d) ^ 3 / (3 * w ^ 2 + d ^ 2) := by
    rw [eq_div_iff h3, sub_mul, div_mul_cancel₀ _ h3]
    ring
  have hp : w * (w ^ 2 + 3 * d ^ 2) / (3 * w ^ 2 + d ^ 2) + d = (w + d) ^ 3 / (3 * w ^ 2 + d ^ 2) := by
    rw [eq_div_iff h3, add_mul, div_mul_cancel₀ _ h3]
    ring
  rw [hn, hp, div_pow]
  generalize 3 * w ^ 2 + d ^ 2 = D at h3
  have h23 : (w + d) ^ 3 ≠ 0 := pow_ne_zero 3 h2
  field_simp

end Field

/-! ### The three means satisfy the hypotheses of Theorem 3.1 -/

/-- The coefficients of the three-mean support of degree `p`, `q(t) = μ (1+t) + γ √t - ν √(t + δ (t-1)²)`,
satisfy `2 μ + γ - ν = 1`: this one identity gives both `q(1) = 1` and `q'(1) = 1/2`. -/
theorem three_mean_normalisation (p : ℝ) (hp : p ≠ 0) (h4 : 4 * p ^ 2 - 1 ≠ 0) :
    2 * ((p - 2) * (47 * p ^ 2 + 21 * p + 4) / (60 * p * (4 * p ^ 2 - 1)))
      + 16 * (p + 1) * (4 * p ^ 2 - 1) / (15 * p * (5 * p ^ 2 + 4))
      - 49 * p * (p + 1) * (p ^ 2 - 4) / (10 * (4 * p ^ 2 - 1) * (5 * p ^ 2 + 4)) = 1 := by
  have h5 : 5 * p ^ 2 + 4 ≠ 0 := by positivity
  generalize hD : 4 * p ^ 2 - 1 = D at h4 ⊢
  generalize hE : 5 * p ^ 2 + 4 = E at h5 ⊢
  field_simp
  subst hD hE
  ring

/-- The second-order coefficient of the three means at `1`: `-γ/8 + ν/8 - ν δ/2 = -(p+1)/(12 p)`, the
value of the exact support `((1-t)/(1-t^{1/p}) - 1)/(p-1)`. -/
theorem three_mean_second_order (p : ℝ) (hp : p ≠ 0) (h4 : 4 * p ^ 2 - 1 ≠ 0) :
    -(16 * (p + 1) * (4 * p ^ 2 - 1) / (15 * p * (5 * p ^ 2 + 4))) / 8
      + 49 * p * (p + 1) * (p ^ 2 - 4) / (10 * (4 * p ^ 2 - 1) * (5 * p ^ 2 + 4)) / 8
      - 49 * p * (p + 1) * (p ^ 2 - 4) / (10 * (4 * p ^ 2 - 1) * (5 * p ^ 2 + 4))
          * ((5 * p ^ 2 + 4) / (84 * p ^ 2)) / 2
      = -(p + 1) / (12 * p) := by
  have h5 : 5 * p ^ 2 + 4 ≠ 0 := by positivity
  generalize hD : 4 * p ^ 2 - 1 = D at h4 ⊢
  generalize hE : 5 * p ^ 2 + 4 = E at h5 ⊢
  field_simp
  subst hD hE
  ring

/-- With `q₂ = -(p+1)/(12p)` the second coefficient of Theorem 3.1, `1/2 + 4 p q₂/(p-1)`, is
`(p-5)/(6(p-1))`: it vanishes for the degree five. -/
theorem second_coefficient_three_mean (p : ℝ) (hp : p ≠ 0) (hp1 : p - 1 ≠ 0) :
    1 / 2 + 4 * p * (-(p + 1) / (12 * p)) / (p - 1) = (p - 5) / (6 * (p - 1)) := by
  field_simp
  ring

/-- A support `μ (1+t) + γ √t - ν √(t + δ (t-1)²)` has value `2μ + γ - ν` and derivative
`μ + γ/2 - ν/2` at `t = 1`.  With `three_mean_normalisation`: `q(1) = 1` and `q'(1) = 1/2` for the
three means of every degree. -/
theorem three_mean_value_and_slope (μ γ ν δ : ℝ) :
    (μ * (1 + 1) + γ * Real.sqrt 1 - ν * Real.sqrt (1 + δ * (1 - 1) ^ 2) = 2 * μ + γ - ν) ∧
    HasDerivAt (fun t : ℝ => μ * (1 + t) + γ * Real.sqrt t - ν * Real.sqrt (t + δ * (t - 1) ^ 2))
      (μ + γ / 2 - ν / 2) 1 := by
  constructor
  · norm_num
    ring
  · have h1 : HasDerivAt (fun t : ℝ => μ * (1 + t)) μ 1 :=
      (((hasDerivAt_id' (1 : ℝ)).const_add 1).const_mul μ).congr_deriv (by ring)
    have h2 : HasDerivAt (fun t : ℝ => γ * Real.sqrt t) (γ / 2) 1 :=
      ((Real.hasDerivAt_sqrt (one_ne_zero)).const_mul γ).congr_deriv (by norm_num; ring)
    have hin : HasDerivAt (fun t : ℝ => t + δ * (t - 1) ^ 2) 1 1 :=
      ((hasDerivAt_id' (1 : ℝ)).add ((((hasDerivAt_id' (1 : ℝ)).sub_const 1).pow 2).const_mul δ)).congr_deriv
        (by norm_num)
    have h3 : HasDerivAt (fun t : ℝ => ν * Real.sqrt (t + δ * (t - 1) ^ 2)) (ν / 2) 1 :=
      ((hin.sqrt (by norm_num)).const_mul ν).congr_deriv (by norm_num; ring)
    exact (h1.add h2).sub h3

/-- A quantitative form of the order four for the line `AD`: if `‖x‖ ≤ 1/4` and `‖v‖ ≤ 1/4`, the
factor `(x² + v)/(2 + 2x + x² + v)` of the new error is at most `‖x‖² + ‖v‖` in modulus.  Since
`x = δ₁ e` and `v = δ₂ e²`, the new error is `O(‖e‖³ (‖δ₁‖² ‖e‖⁰ + ‖δ₂‖))`. -/
theorem error_AD_bound (x v : ℂ) (hx : ‖x‖ ≤ 1 / 4) (hv : ‖v‖ ≤ 1 / 4) :
    ‖(x ^ 2 + v) / (2 + 2 * x + x ^ 2 + v)‖ ≤ ‖x‖ ^ 2 + ‖v‖ := by
  have hnum : ‖x ^ 2 + v‖ ≤ ‖x‖ ^ 2 + ‖v‖ := by
    calc ‖x ^ 2 + v‖ ≤ ‖x ^ 2‖ + ‖v‖ := norm_add_le _ _
      _ = ‖x‖ ^ 2 + ‖v‖ := by rw [norm_pow]
  have hx2 : ‖x‖ ^ 2 ≤ 1 / 16 := by
    have h0 : 0 ≤ ‖x‖ := norm_nonneg x
    nlinarith
  have hden : (1 : ℝ) ≤ ‖2 + 2 * x + x ^ 2 + v‖ := by
    have h : ‖(2 : ℂ)‖ - ‖2 * x + x ^ 2 + v‖ ≤ ‖2 + (2 * x + x ^ 2 + v)‖ := by
      have := norm_sub_norm_le (2 : ℂ) (-(2 * x + x ^ 2 + v))
      rwa [norm_neg, sub_neg_eq_add] at this
    have hs : ‖2 * x + x ^ 2 + v‖ ≤ 2 * ‖x‖ + ‖x‖ ^ 2 + ‖v‖ := by
      calc ‖2 * x + x ^ 2 + v‖ ≤ ‖2 * x + x ^ 2‖ + ‖v‖ := norm_add_le _ _
        _ ≤ ‖2 * x‖ + ‖x ^ 2‖ + ‖v‖ := by gcongr; exact norm_add_le _ _
        _ = 2 * ‖x‖ + ‖x‖ ^ 2 + ‖v‖ := by rw [norm_mul, norm_pow]; norm_num
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    have e : (2 : ℂ) + 2 * x + x ^ 2 + v = 2 + (2 * x + x ^ 2 + v) := by ring
    rw [e]
    linarith
  rw [norm_div]
  have hpos : (0 : ℝ) < ‖2 + 2 * x + x ^ 2 + v‖ := by linarith
  rw [div_le_iff₀ hpos]
  have hnn : 0 ≤ ‖x‖ ^ 2 + ‖v‖ := by positivity
  nlinarith

end LeanMath.Papers.SimultaneousRectangle
