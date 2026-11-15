import Mathlib

/-! # Evaluation through a scaled variable, and the disc of a cluster (pandroots 0.8.0)

**Scaled variable.**  A point `z` outside the unit disc that has few bits is written `z = c t` with
`c = 2^e` and `|t| ≤ 1`, and `S(z)`, `S'(z)`, `S''(z)` are obtained from the polynomial `T(t) = S(c t)`,
whose coefficients are those of `S` multiplied by powers of `c`:

* `coeff_scaled`: the coefficient of degree `n` of `T` is `c^n` times that of `S`;
* `eval_scaled`, `eval_derivative_scaled`, `eval_derivative2_scaled`: `T(t) = S(c t)`,
  `T'(t) = c S'(c t)`, `T''(t) = c² S''(c t)`;
* `leadingCoeff_scaled`: the leading coefficient of `T` is `c^m` times that of `S` (`m` the degree);
* `newton_scaled`: the Newton correction `N = S/S'` at `z` is `c` times that of `T` at `t`;
* `beta_scaled`: `β = S S''/S'²` is the same for `S` at `z` and for `T` at `t`.

**Disc of a cluster.**  With `Options::isolate = false` a connected component of Smith discs is returned
as one disc centred at its first point:

* `smith_disc_subset`: a disc of radius `R ≥ dist(z₀, z_l) + r_l` centred at `z₀` contains the disc
  `D(z_l, r_l)`; hence the enclosing disc contains every Smith disc of the component, and with them the
  roots that Smith's theorem places in the component.

Not formalised: the Rust code, the ball evaluation itself, and the second half of Smith's theorem (a
component of `q` discs contains exactly `q` roots), on which the count of a cluster rests since 0.1.0. -/

namespace LeanMath.Papers.ScaledVariable
open Polynomial

variable {K : Type*} [Field K]

/-- `T = S(c X)`. -/
noncomputable def scaled (S : K[X]) (c : K) : K[X] := S.comp (C c * X)

theorem eval_scaled (S : K[X]) (c t : K) : (scaled S c).eval t = S.eval (c * t) := by
  simp [scaled, eval_comp]

theorem derivative_scaled (S : K[X]) (c : K) :
    derivative (scaled S c) = C c * scaled (derivative S) c := by
  unfold scaled
  have h : derivative (C c * X : K[X]) = C c := by
    rw [derivative_C_mul, derivative_X, mul_one]
  rw [derivative_comp, h]

theorem eval_derivative_scaled (S : K[X]) (c t : K) :
    (derivative (scaled S c)).eval t = c * (derivative S).eval (c * t) := by
  rw [derivative_scaled, eval_mul, eval_C, eval_scaled]

theorem eval_derivative2_scaled (S : K[X]) (c t : K) :
    (derivative (derivative (scaled S c))).eval t = c ^ 2 * (derivative (derivative S)).eval (c * t) := by
  rw [derivative_scaled, derivative_mul, derivative_C, zero_mul, zero_add, derivative_scaled,
    eval_mul, eval_C, eval_mul, eval_C, eval_scaled]
  ring

theorem coeff_scaled (S : K[X]) (c : K) (n : ℕ) : (scaled S c).coeff n = S.coeff n * c ^ n := by
  unfold scaled
  rw [comp_C_mul_X_coeff]

theorem leadingCoeff_scaled (S : K[X]) {c : K} (hc : c ≠ 0) :
    (scaled S c).leadingCoeff = S.leadingCoeff * c ^ S.natDegree := by
  have hdeg : (scaled S c).natDegree = S.natDegree := by
    unfold scaled
    rw [natDegree_comp, natDegree_C_mul_X c hc, mul_one]
  rw [leadingCoeff, hdeg, coeff_scaled, leadingCoeff]

/-- The Newton correction at `z = c t` from the scaled polynomial. -/
theorem newton_scaled (S : K[X]) {c : K} (hc : c ≠ 0) (t : K) :
    c * ((scaled S c).eval t / (derivative (scaled S c)).eval t)
      = S.eval (c * t) / (derivative S).eval (c * t) := by
  rw [eval_scaled, eval_derivative_scaled]
  by_cases h : (derivative S).eval (c * t) = 0
  · simp [h]
  · field_simp

/-- `β = S S''/S'²` is unchanged. -/
theorem beta_scaled (S : K[X]) {c : K} (hc : c ≠ 0) (t : K) :
    (scaled S c).eval t * (derivative (derivative (scaled S c))).eval t
        / (derivative (scaled S c)).eval t ^ 2
      = S.eval (c * t) * (derivative (derivative S)).eval (c * t) / (derivative S).eval (c * t) ^ 2 := by
  rw [eval_scaled, eval_derivative_scaled, eval_derivative2_scaled]
  by_cases h : (derivative S).eval (c * t) = 0
  · simp [h]
  · field_simp

/-- The enclosing disc of a component contains each of its Smith discs. -/
theorem smith_disc_subset {z₀ z : ℂ} {r R : ℝ} (h : dist z z₀ + r ≤ R) :
    Metric.closedBall z r ⊆ Metric.closedBall z₀ R :=
  Metric.closedBall_subset_closedBall' (by linarith)

end LeanMath.Papers.ScaledVariable
