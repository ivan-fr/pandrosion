import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Calculus.DiffContOnCl
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! # Complex Pandrosion supports

Formal support for the complex-plane companion of *Geometric Root Calculators*.

* algebra of the update `u ↦ u * corr p q (X / u ^ p)` over `ℂ`: residual update, rotation
  equivariance, exact support, reciprocity, the conic family (Laguerre, Halley), degree two;
* real degrees: determinations of the root, the logarithmic chart, rational reduction, degree
  doubling, perturbation of the degree;
* a Schwarz lemma of order `m` on the unit disk and the Cayley bound for the right half-plane;
* the real-variable core of the boundary inequality for the decentered arc.

The complex-analytic assembly (Phragmén–Lindelöf on the strip, the transfer to the half-plane) and
the interval-arithmetic certificate for the nested support are not formalized here. -/

noncomputable section
namespace LeanMath.Papers.ComplexRoots

open Metric Filter Topology

/-! ## Algebra of the update -/

/-- Correction factor of a support with normalized value `q = (κ - 1) / (p - 1)`. -/
def corr (p q t : ℂ) : ℂ := (t + (p - 1) * q) / (1 + (p - 1) * q)

/-- One step on the direct state, for a support `q` evaluated at the residual `t = X / u ^ p`. -/
def step (p : ℕ) (q : ℂ → ℂ) (X u : ℂ) : ℂ := u * corr p (q (X / u ^ p)) (X / u ^ p)

/-- The residual `t = X / u ^ p` is updated by `t ↦ t / c ^ p` when `u ↦ u * c`. -/
theorem residual_update (p : ℕ) (X u c : ℂ) : X / (u * c) ^ p = X / u ^ p / c ^ p := by
  rw [mul_pow, div_div]

/-- The step commutes with multiplication by a `p`-th root of unity. -/
theorem step_rotation (p : ℕ) (q : ℂ → ℂ) (X u ω : ℂ) (hω : ω ^ p = 1) :
    step p q X (ω * u) = ω * step p q X u := by
  unfold step
  rw [mul_pow, hω, one_mul]
  ring

/-- The exact support: if `c ^ p = t`, the value `q = (t - c) / ((p - 1) (c - 1))` returns `c`. -/
theorem corr_exact (p c t : ℂ) (hp : p - 1 ≠ 0) (hc : c - 1 ≠ 0) (ht : t - 1 ≠ 0) :
    corr p ((t - c) / ((p - 1) * (c - 1))) t = c := by
  have h : (p - 1) * ((t - c) / ((p - 1) * (c - 1))) = (t - c) / (c - 1) := by field_simp
  have h1 : t + (t - c) / (c - 1) = c * (t - 1) / (c - 1) := by field_simp; ring
  have h2 : 1 + (t - c) / (c - 1) = (t - 1) / (c - 1) := by field_simp; ring
  unfold corr
  rw [h, h1, h2]
  field_simp

/-- Reciprocity: a support with `q (1 / t) = q t / t` has `φ (1 / t) = 1 / φ t`. -/
theorem corr_reciprocal (p q t : ℂ) (ht : t ≠ 0) (h1 : 1 + (p - 1) * q ≠ 0)
    (h2 : t + (p - 1) * q ≠ 0) : corr p (q / t) t⁻¹ = (corr p q t)⁻¹ := by
  have h3 : (1 : ℂ) + (p - 1) * (q / t) = (t + (p - 1) * q) / t := by field_simp
  have h4 : t⁻¹ + (p - 1) * (q / t) = (1 + (p - 1) * q) / t := by field_simp
  unfold corr
  rw [inv_div, h3, h4]
  field_simp

/-- On the unit circle of the residual plane a reciprocal support with real coefficients has a
correction of modulus one: the circle `|u| = |X| ^ (1 / p)` is invariant. -/
theorem corr_unit_circle (p : ℝ) (q t : ℂ) (ht : ‖t‖ = 1)
    (hq : (starRingEnd ℂ) q = q / t) (h1 : 1 + ((p : ℂ) - 1) * q ≠ 0)
    (h2 : t + ((p : ℂ) - 1) * q ≠ 0) : ‖corr p q t‖ = 1 := by
  have ht0 : t ≠ 0 := by
    intro h; rw [h, norm_zero] at ht; exact zero_ne_one ht
  have hct : (starRingEnd ℂ) t = t⁻¹ := by
    have h : t * (starRingEnd ℂ) t = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ht]; norm_num
    exact eq_inv_of_mul_eq_one_right h
  have hconj : (starRingEnd ℂ) (corr p q t) = (corr p q t)⁻¹ := by
    rw [← corr_reciprocal p q t ht0 h1 h2]
    unfold corr
    simp only [map_div₀, map_add, map_mul, map_sub, map_one, Complex.conj_ofReal, hq, hct]
  have hne : corr p q t ≠ 0 := div_ne_zero h2 h1
  have hpos : 0 < ‖corr p q t‖ := norm_pos_iff.mpr hne
  have h3 : ‖corr p q t‖ = ‖corr p q t‖⁻¹ := by
    have := congrArg norm hconj
    simpa using this
  have h4 : ‖corr p q t‖ * ‖corr p q t‖ = 1 := by
    nth_rewrite 2 [h3]; exact mul_inv_cancel₀ hpos.ne'
  nlinarith [hpos, h4]

/-! ## The conic family `q ^ 2 = t + a (t - 1) ^ 2` -/

/-- Halley's support `q = (1 + t) / 2` is the member `a = 1 / 4`. -/
theorem halley_conic (t : ℂ) : ((1 + t) / 2) ^ 2 = t + 1 / 4 * (t - 1) ^ 2 := by ring

/-- Halley's correction is a Möbius map of the residual. -/
theorem halley_corr (p t : ℂ) (h : (p - 1) * t + (p + 1) ≠ 0) :
    corr p ((1 + t) / 2) t = ((p + 1) * t + (p - 1)) / ((p - 1) * t + (p + 1)) := by
  have h' : 1 + (p - 1) * ((1 + t) / 2) ≠ 0 := by
    intro h0; apply h; linear_combination 2 * h0
  unfold corr
  rw [div_eq_div_iff h' h]; ring

/-- Laguerre's iteration for `z ^ (k + 1) - X` is the member `a = 0`: its support is a square root
`r` of the residual. -/
theorem laguerre_eq_corr (k : ℕ) (X u r : ℂ) (hu : u ≠ 0) (hr : r ^ 2 = X / u ^ (k + 1))
    (hd : 1 + (((k + 1 : ℕ) : ℂ) - 1) * r ≠ 0) :
    u - (u ^ (k + 1) - X) / (u ^ k * (1 + (((k + 1 : ℕ) : ℂ) - 1) * r))
      = u * corr ((k + 1 : ℕ) : ℂ) r (X / u ^ (k + 1)) := by
  have hX : X = r ^ 2 * u ^ (k + 1) := by rw [hr]; field_simp
  rw [← hr]
  subst hX
  generalize (((k + 1 : ℕ) : ℂ)) = c at hd ⊢
  unfold corr
  generalize hdd : 1 + (c - 1) * r = d at hd ⊢
  have hc : (c - 1) * r = d - 1 := by rw [← hdd]; ring
  have hk : u ^ k ≠ 0 := pow_ne_zero k hu
  rw [hc, pow_succ]
  field_simp
  ring

/-! ## Degree two: exact conjugacies -/

theorem newton_two_sub (u r : ℂ) (hu : u ≠ 0) :
    u * corr 2 1 (r ^ 2 / u ^ 2) - r = (u - r) ^ 2 / (2 * u) := by
  have h : corr 2 1 (r ^ 2 / u ^ 2) = (r ^ 2 / u ^ 2 + 1) / 2 := by unfold corr; norm_num
  rw [h]; field_simp; ring

theorem newton_two_add (u r : ℂ) (hu : u ≠ 0) :
    u * corr 2 1 (r ^ 2 / u ^ 2) + r = (u + r) ^ 2 / (2 * u) := by
  have h : corr 2 1 (r ^ 2 / u ^ 2) = (r ^ 2 / u ^ 2 + 1) / 2 := by unfold corr; norm_num
  rw [h]; field_simp; ring

theorem halley_two_corr (u r : ℂ) (hu : u ≠ 0) (h : r ^ 2 + 3 * u ^ 2 ≠ 0) :
    corr 2 ((1 + r ^ 2 / u ^ 2) / 2) (r ^ 2 / u ^ 2) = (3 * r ^ 2 + u ^ 2) / (r ^ 2 + 3 * u ^ 2) := by
  have hden : ((2 : ℂ) - 1) * (r ^ 2 / u ^ 2) + (2 + 1) = (r ^ 2 + 3 * u ^ 2) / u ^ 2 := by
    field_simp; ring
  have ht : ((2 : ℂ) - 1) * (r ^ 2 / u ^ 2) + (2 + 1) ≠ 0 := by
    rw [hden]; exact div_ne_zero h (pow_ne_zero 2 hu)
  rw [halley_corr 2 _ ht, hden]
  field_simp; ring

theorem halley_two_sub (u r : ℂ) (hu : u ≠ 0) (h : r ^ 2 + 3 * u ^ 2 ≠ 0) :
    u * corr 2 ((1 + r ^ 2 / u ^ 2) / 2) (r ^ 2 / u ^ 2) - r
      = (u - r) ^ 3 / (r ^ 2 + 3 * u ^ 2) := by
  rw [halley_two_corr u r hu h, eq_div_iff h, sub_mul, ← mul_div_assoc, div_mul_cancel₀ _ h]
  ring

theorem halley_two_add (u r : ℂ) (hu : u ≠ 0) (h : r ^ 2 + 3 * u ^ 2 ≠ 0) :
    u * corr 2 ((1 + r ^ 2 / u ^ 2) / 2) (r ^ 2 / u ^ 2) + r
      = (u + r) ^ 3 / (r ^ 2 + 3 * u ^ 2) := by
  rw [halley_two_corr u r hu h, eq_div_iff h, add_mul, ← mul_div_assoc, div_mul_cancel₀ _ h]
  ring

/-- Normalized projective support. -/
def qProj (p t : ℂ) : ℂ := ((4 * p + 1) * t + 2 * p - 1) / ((p + 1) * t + 5 * p - 1)

theorem proj_two_corr (t : ℂ) (h3 : t + 3 ≠ 0) (h1 : t + 1 ≠ 0) :
    corr 2 (qProj 2 t) t = (t ^ 2 + 6 * t + 1) / (4 * (t + 1)) := by
  have h9 : ((2 : ℂ) + 1) * t + 5 * 2 - 1 ≠ 0 := by
    intro h0; apply h3; linear_combination (1 / 3 : ℂ) * h0
  have hq : qProj 2 t = (3 * t + 1) / (t + 3) := by
    unfold qProj; rw [div_eq_div_iff h9 h3]; ring
  have hn : t + (2 - 1) * ((3 * t + 1) / (t + 3)) = (t ^ 2 + 6 * t + 1) / (t + 3) := by
    field_simp; ring
  have hd : 1 + (2 - 1) * ((3 * t + 1) / (t + 3)) = 4 * (t + 1) / (t + 3) := by
    field_simp; ring
  rw [hq]; unfold corr; rw [hn, hd]; field_simp

theorem proj_two_sub (u r : ℂ) (hu : u ≠ 0) (h3 : r ^ 2 + 3 * u ^ 2 ≠ 0)
    (h1 : r ^ 2 + u ^ 2 ≠ 0) :
    u * corr 2 (qProj 2 (r ^ 2 / u ^ 2)) (r ^ 2 / u ^ 2) - r
      = (u - r) ^ 4 / (4 * u * (r ^ 2 + u ^ 2)) := by
  have e3 : r ^ 2 / u ^ 2 + 3 = (r ^ 2 + 3 * u ^ 2) / u ^ 2 := by field_simp
  have e1 : r ^ 2 / u ^ 2 + 1 = (r ^ 2 + u ^ 2) / u ^ 2 := by field_simp
  have k3 : r ^ 2 / u ^ 2 + 3 ≠ 0 := by rw [e3]; exact div_ne_zero h3 (pow_ne_zero 2 hu)
  have k1 : r ^ 2 / u ^ 2 + 1 ≠ 0 := by rw [e1]; exact div_ne_zero h1 (pow_ne_zero 2 hu)
  rw [proj_two_corr _ k3 k1, e1]; field_simp; ring

theorem proj_two_add (u r : ℂ) (hu : u ≠ 0) (h3 : r ^ 2 + 3 * u ^ 2 ≠ 0)
    (h1 : r ^ 2 + u ^ 2 ≠ 0) :
    u * corr 2 (qProj 2 (r ^ 2 / u ^ 2)) (r ^ 2 / u ^ 2) + r
      = (u + r) ^ 4 / (4 * u * (r ^ 2 + u ^ 2)) := by
  have e3 : r ^ 2 / u ^ 2 + 3 = (r ^ 2 + 3 * u ^ 2) / u ^ 2 := by field_simp
  have e1 : r ^ 2 / u ^ 2 + 1 = (r ^ 2 + u ^ 2) / u ^ 2 := by field_simp
  have k3 : r ^ 2 / u ^ 2 + 3 ≠ 0 := by rw [e3]; exact div_ne_zero h3 (pow_ne_zero 2 hu)
  have k1 : r ^ 2 / u ^ 2 + 1 ≠ 0 := by rw [e1]; exact div_ne_zero h1 (pow_ne_zero 2 hu)
  rw [proj_two_corr _ k3 k1, e1]; field_simp; ring

/-- In degree two the radical supports are exact: a square root `q` of the residual is returned. -/
theorem radical_two_exact (q t : ℂ) (hq : q ^ 2 = t) (h : 1 + q ≠ 0) : corr 2 q t = q := by
  have h' : (1 : ℂ) + (2 - 1) * q = 1 + q := by ring
  unfold corr
  rw [h', div_eq_iff h, ← hq]; ring

/-! ## Real degrees: determinations and the logarithmic chart

For a real degree `p` the state is a logarithm `ℓ` of `u` (the point together with a winding), the
radicand is `X = exp L`, the residual is `t = exp (L - p ℓ)` and one step is `ℓ ↦ ℓ + log φ`. -/

/-- Each `ℓ = (L + 2 π i k) / p` is a logarithm of a `p`-th root of `X = exp L`. -/
theorem determination_root (p : ℝ) (hp : p ≠ 0) (L : ℂ) (k : ℤ) :
    Complex.exp ((p : ℂ) * ((L + 2 * Real.pi * Complex.I * k) / p)) = Complex.exp L := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  have e : (p : ℂ) * ((L + 2 * Real.pi * Complex.I * k) / p)
      = L + (k : ℂ) * (2 * Real.pi * Complex.I) := by field_simp
  rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Rational degree `p = μ / ν`: every determination of `X ^ (1 / p)` is a `μ`-th root of
`X ^ ν`. -/
theorem determination_rational (μ ν : ℕ) (hμ : μ ≠ 0) (L : ℂ) (k : ℤ) :
    Complex.exp ((ν : ℂ) * (L + 2 * Real.pi * Complex.I * k) / μ) ^ μ = Complex.exp L ^ ν := by
  have hμ' : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ
  have e : (μ : ℂ) * ((ν : ℂ) * (L + 2 * Real.pi * Complex.I * k) / μ)
      = (ν : ℂ) * L + ((ν * k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; field_simp
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, e, Complex.exp_add,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Degree doubling: a root of degree `p` is the `2 ^ j`-th power of a root of degree `2 ^ j p`. -/
theorem determination_doubling (p : ℝ) (hp : p ≠ 0) (j : ℕ) (ℓ : ℂ) :
    Complex.exp (ℓ / ((2 : ℂ) ^ j * p)) ^ (2 ^ j) = Complex.exp (ℓ / p) := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

/-- Negative degrees: `X ^ (1 / p) = (1 / X) ^ (1 / (-p))`. -/
theorem determination_neg (p : ℝ) (L : ℂ) :
    Complex.exp (-L / ((-p : ℝ) : ℂ)) = Complex.exp (L / p) := by
  push_cast; rw [neg_div_neg_eq]

/-- The logarithmic step projects to `u ↦ u * c`. -/
theorem log_chart_state (ℓ c : ℂ) (hc : c ≠ 0) :
    Complex.exp (ℓ + Complex.log c) = Complex.exp ℓ * c := by
  rw [Complex.exp_add, Complex.exp_log hc]

/-- Residual update in the logarithmic chart, for a real degree. -/
theorem log_chart_residual (p : ℝ) (L ℓ c : ℂ) :
    Complex.exp (L - p * (ℓ + Complex.log c))
      = Complex.exp (L - p * ℓ) * Complex.exp (-(p * Complex.log c)) := by
  rw [← Complex.exp_add]; congr 1; ring

/-- For an integer degree the residual update is `t ↦ t / c ^ n`, as in `residual_update`. -/
theorem log_chart_residual_nat (n : ℕ) (L ℓ c : ℂ) (hc : c ≠ 0) :
    Complex.exp (L - n * (ℓ + Complex.log c)) = Complex.exp (L - n * ℓ) / c ^ n := by
  have e : L - n * (ℓ + Complex.log c) = (L - n * ℓ) + -(n * Complex.log c) := by ring
  rw [e, Complex.exp_add, Complex.exp_neg, Complex.exp_nat_mul, Complex.exp_log hc, div_eq_mul_inv]

/-- The state is recovered from the lifted residual `x = L - p ℓ + 2 π i k`: the error to the
`k`-th determination is `-x / p`. -/
theorem log_chart_error (p : ℝ) (hp : p ≠ 0) (L ℓ : ℂ) (k : ℤ) :
    ℓ = (L + 2 * Real.pi * Complex.I * k) / p
        - (L - p * ℓ + 2 * Real.pi * Complex.I * k) / p := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  field_simp
  ring

/-- The lifted residual is updated by `x ↦ x - p log φ`, whatever the determination. -/
theorem log_chart_conjugacy (p : ℝ) (L ℓ c : ℂ) (k : ℤ) :
    L - p * (ℓ + Complex.log c) + 2 * Real.pi * Complex.I * k
      = (L - p * ℓ + 2 * Real.pi * Complex.I * k) - p * Complex.log c := by ring

/-- The strips `|Im ℓ - (α + 2 π k) / p| < π / (2 p)` around distinct determinations are
disjoint. -/
theorem strips_disjoint (p α y : ℝ) (hp : 0 < p) (k k' : ℤ)
    (h : |y - (α + 2 * Real.pi * k) / p| < Real.pi / (2 * p))
    (h' : |y - (α + 2 * Real.pi * k') / p| < Real.pi / (2 * p)) : k = k' := by
  by_contra hne
  have hπ := Real.pi_pos
  have h1 : (1 : ℝ) ≤ |(k : ℝ) - k'| := by
    have := Int.one_le_abs (sub_ne_zero.mpr hne)
    exact_mod_cast this
  have h2 : |(α + 2 * Real.pi * k) / p - (α + 2 * Real.pi * k') / p| < Real.pi / p := by
    have e0 : Real.pi / (2 * p) + Real.pi / (2 * p) = Real.pi / p := by field_simp; ring
    calc |(α + 2 * Real.pi * k) / p - (α + 2 * Real.pi * k') / p|
        ≤ |(α + 2 * Real.pi * k) / p - y| + |y - (α + 2 * Real.pi * k') / p| := abs_sub_le _ _ _
      _ < Real.pi / (2 * p) + Real.pi / (2 * p) := by rw [abs_sub_comm] at h; linarith
      _ = Real.pi / p := e0
  have e : (α + 2 * Real.pi * k) / p - (α + 2 * Real.pi * k') / p
      = 2 * Real.pi / p * ((k : ℝ) - k') := by field_simp; ring
  have hc : 0 < 2 * Real.pi / p := by positivity
  rw [e, abs_mul, abs_of_pos hc] at h2
  have h4 : 2 * Real.pi / p * 1 ≤ 2 * Real.pi / p * |(k : ℝ) - k'| :=
    mul_le_mul_of_nonneg_left h1 hc.le
  have h5 : Real.pi / p < 2 * Real.pi / p * 1 := by
    rw [mul_one]; exact div_lt_div_of_pos_right (by linarith) hp
  linarith

/-- Replacing a degree `p` by a nearby degree `p'` (for instance a rational one) moves the principal
determination by a controlled amount. -/
theorem degree_perturbation (L : ℂ) (p p' : ℝ) (h : ‖L‖ * |1 / p' - 1 / p| ≤ 1) :
    ‖Complex.exp (L / p') - Complex.exp (L / p)‖
      ≤ 2 * ‖Complex.exp (L / p)‖ * (‖L‖ * |1 / p' - 1 / p|) := by
  have e : L / (p' : ℂ) = L / p + L * ((1 / p' - 1 / p : ℝ) : ℂ) := by push_cast; ring
  have hz : ‖L * ((1 / p' - 1 / p : ℝ) : ℂ)‖ = ‖L‖ * |1 / p' - 1 / p| := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 : ‖L * ((1 / p' - 1 / p : ℝ) : ℂ)‖ ≤ 1 := by rw [hz]; exact h
  have h2 := Complex.norm_exp_sub_one_le h1
  rw [e, Complex.exp_add, ← mul_sub_one, norm_mul]
  calc ‖Complex.exp (L / p)‖ * ‖Complex.exp (L * ((1 / p' - 1 / p : ℝ) : ℂ)) - 1‖
      ≤ ‖Complex.exp (L / p)‖ * (2 * ‖L * ((1 / p' - 1 / p : ℝ) : ℂ)‖) :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = 2 * ‖Complex.exp (L / p)‖ * (‖L‖ * |1 / p' - 1 / p|) := by rw [hz]; ring

/-! ## Schwarz lemma of order `m` and the Cayley bound -/

/-- If `f = z ^ m * g` maps the unit disk into the closed unit disk, with `g` holomorphic, then
`‖f z‖ ≤ ‖z‖ ^ m`. -/
theorem schwarz_order (m : ℕ) (f g : ℂ → ℂ) (hg : DifferentiableOn ℂ g (ball 0 1))
    (hfg : ∀ z ∈ ball (0 : ℂ) 1, f z = z ^ m * g z) (hf : ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ 1) :
    ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ ‖z‖ ^ m := by
  intro z hz
  have hz1 : ‖z‖ < 1 := by simpa using hz
  have key : ∀ r : ℝ, ‖z‖ < r → r < 1 → ‖g z‖ * r ^ m ≤ 1 := by
    intro r hzr hr1
    have hr0 : 0 < r := lt_of_le_of_lt (norm_nonneg z) hzr
    have hsub : closedBall (0 : ℂ) r ⊆ ball 0 1 := closedBall_subset_ball hr1
    have hd : DiffContOnCl ℂ g (ball 0 r) := (hg.mono hsub).diffContOnCl_ball subset_rfl
    have hb : ∀ w ∈ frontier (ball (0 : ℂ) r), ‖g w‖ ≤ 1 / r ^ m := by
      intro w hw
      rw [frontier_ball (0 : ℂ) hr0.ne'] at hw
      have hwr : ‖w‖ = r := by simpa using hw
      have hw1 : w ∈ ball (0 : ℂ) 1 := by simpa [hwr] using hr1
      have h1 := hf w hw1
      rw [hfg w hw1, norm_mul, norm_pow, hwr] at h1
      rw [le_div_iff₀ (pow_pos hr0 m)]
      linarith [mul_comm (‖g w‖) (r ^ m)]
    have hzc : z ∈ closure (ball (0 : ℂ) r) := subset_closure (by simpa using hzr)
    have h2 := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd hb hzc
    rwa [le_div_iff₀ (pow_pos hr0 m)] at h2
  have hlim : Tendsto (fun r : ℝ => ‖g z‖ * r ^ m) (𝓝[<] 1) (𝓝 (‖g z‖ * 1 ^ m)) :=
    ((continuous_const.mul (continuous_pow m)).tendsto 1).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ r in 𝓝[<] (1 : ℝ), ‖g z‖ * r ^ m ≤ 1 := by
    filter_upwards [Ioo_mem_nhdsLT hz1] with r hr using key r hr.1 hr.2
  have hg1 : ‖g z‖ ≤ 1 := by simpa using le_of_tendsto hlim hev
  rw [hfg z hz, norm_mul, norm_pow]
  calc ‖z‖ ^ m * ‖g z‖ ≤ ‖z‖ ^ m * 1 := by gcongr
    _ = ‖z‖ ^ m := mul_one _

/-- The Cayley coordinate `η = (t - 1) / (t + 1)` of a point of the right half-plane lies in the
unit disk. -/
theorem cayley_norm_lt_one (t : ℂ) (ht : 0 < t.re) : ‖(t - 1) / (t + 1)‖ < 1 := by
  have h1 : t + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  rw [norm_div, div_lt_one (norm_pos_iff.mpr h1)]
  have h2 : ‖t - 1‖ ^ 2 < ‖t + 1‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp
    nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h2

/-! ## Real-variable core of the boundary inequality for the decentered arc

On the boundary `t = i y` of the right half-plane write `m = m₁ + i m₂` for the principal square
root of `1 + a w`, `w = -2 + i ν`, and `g = g₁ + i g₂` for that of `w + 4 = 2 + i ν`. With
`R = Re (m g)`, `R' = Re (conj m * g)` and `s = |m| ^ 2`, the inequality `arg φ ≤ π / p` reads
`1 + (p - 1) R ≤ tan (π / p) * ((p - 1) ^ 2 s + (p - 1) R')`. -/

/-- Sign, positivity and size of `R = m₁ g₁ - m₂ g₂`. -/
theorem arc_R_bounds {a m₁ m₂ g₁ g₂ ν : ℝ} (ha : 0 < a) (ha' : a ≤ 1 / 4) (hm₁ : 0 < m₁)
    (hg₁ : 0 < g₁) (hm : m₁ ^ 2 - m₂ ^ 2 = 1 - 2 * a) (hm' : 2 * m₁ * m₂ = a * ν)
    (hg : g₁ ^ 2 - g₂ ^ 2 = 2) (hg' : 2 * g₁ * g₂ = ν) :
    0 ≤ m₂ * g₂ ∧ 0 < m₁ * g₁ - m₂ * g₂ ∧
      (m₁ * g₁ - m₂ * g₂) ^ 2 ≤ (m₁ ^ 2 + m₂ ^ 2) / (2 * a) := by
  have hA : 0 ≤ 1 - 2 * a := by linarith
  have hpos : 0 < m₁ * g₁ := mul_pos hm₁ hg₁
  have hsign : 0 ≤ m₂ * g₂ := by
    have h4 : 0 ≤ (m₁ * g₁) * (m₂ * g₂) := by
      have e : 4 * ((m₁ * g₁) * (m₂ * g₂)) = a * ν ^ 2 := by
        calc 4 * ((m₁ * g₁) * (m₂ * g₂)) = (2 * m₁ * m₂) * (2 * g₁ * g₂) := by ring
          _ = a * ν * ν := by rw [hm', hg']
          _ = a * ν ^ 2 := by ring
      have h0 := mul_nonneg ha.le (sq_nonneg ν)
      linarith
    by_contra hneg
    have hneg' : m₂ * g₂ < 0 := lt_of_not_ge hneg
    have h5 := mul_pos hpos (neg_pos.mpr hneg')
    have e5 : (m₁ * g₁) * (-(m₂ * g₂)) = -((m₁ * g₁) * (m₂ * g₂)) := by ring
    linarith
  have hm2 : |m₂| < m₁ := abs_lt_of_sq_lt_sq (by linarith) hm₁.le
  have hg2 : |g₂| < g₁ := abs_lt_of_sq_lt_sq (by linarith) hg₁.le
  have hRpos : 0 < m₁ * g₁ - m₂ * g₂ := by
    have h1 : m₂ * g₂ ≤ |m₂| * |g₂| := by rw [← abs_mul]; exact le_abs_self _
    have h2 : |m₂| * |g₂| < m₁ * g₁ :=
      mul_lt_mul'' hm2 hg2 (abs_nonneg _) (abs_nonneg _)
    linarith
  refine ⟨hsign, hRpos, ?_⟩
  have hs2 : (m₁ ^ 2 + m₂ ^ 2) ^ 2 = (1 - 2 * a) ^ 2 + a ^ 2 * ν ^ 2 := by
    have e : (m₁ ^ 2 + m₂ ^ 2) ^ 2 = (m₁ ^ 2 - m₂ ^ 2) ^ 2 + (2 * m₁ * m₂) ^ 2 := by ring
    rw [e, hm, hm']; ring
  have hγ2 : (g₁ ^ 2 + g₂ ^ 2) ^ 2 = 4 + ν ^ 2 := by
    have e : (g₁ ^ 2 + g₂ ^ 2) ^ 2 = (g₁ ^ 2 - g₂ ^ 2) ^ 2 + (2 * g₁ * g₂) ^ 2 := by ring
    rw [e, hg, hg']; ring
  have hs0 : 0 ≤ m₁ ^ 2 + m₂ ^ 2 := by positivity
  have haγ : a * (g₁ ^ 2 + g₂ ^ 2) ≤ m₁ ^ 2 + m₂ ^ 2 := by
    by_contra hlt
    have hlt' : m₁ ^ 2 + m₂ ^ 2 < a * (g₁ ^ 2 + g₂ ^ 2) := lt_of_not_ge hlt
    have h6 := pow_lt_pow_left₀ hlt' hs0 two_ne_zero
    have e1 : (a * (g₁ ^ 2 + g₂ ^ 2)) ^ 2 = 4 * a ^ 2 + a ^ 2 * ν ^ 2 := by
      rw [mul_pow, hγ2]; ring
    have h4a : 4 * a ^ 2 ≤ (1 - 2 * a) ^ 2 := by nlinarith
    linarith
  have hprod : (m₁ * g₁ - m₂ * g₂) * (m₁ * g₁ + m₂ * g₂)
      = (1 - 2 * a) * (g₁ ^ 2 + g₂ ^ 2) / 2 + (m₁ ^ 2 + m₂ ^ 2) := by
    have e : (m₁ * g₁ - m₂ * g₂) * (m₁ * g₁ + m₂ * g₂)
        = ((m₁ ^ 2 - m₂ ^ 2) * (g₁ ^ 2 + g₂ ^ 2) + (m₁ ^ 2 + m₂ ^ 2) * (g₁ ^ 2 - g₂ ^ 2)) / 2 := by
      ring
    rw [e, hm, hg]; ring
  have hsq : (m₁ * g₁ - m₂ * g₂) ^ 2
      ≤ (1 - 2 * a) * (g₁ ^ 2 + g₂ ^ 2) / 2 + (m₁ ^ 2 + m₂ ^ 2) := by
    have h7 := mul_nonneg hRpos.le hsign
    have e7 : (m₁ * g₁ - m₂ * g₂) * (m₁ * g₁ + m₂ * g₂) - (m₁ * g₁ - m₂ * g₂) ^ 2
        = 2 * ((m₁ * g₁ - m₂ * g₂) * (m₂ * g₂)) := by ring
    linarith
  have h2a : 0 < 2 * a := by linarith
  rw [le_div_iff₀ h2a]
  have h8 := mul_le_mul_of_nonneg_right hsq h2a.le
  have h9 := mul_le_mul_of_nonneg_left haγ hA
  have e9 : ((1 - 2 * a) * (g₁ ^ 2 + g₂ ^ 2) / 2 + (m₁ ^ 2 + m₂ ^ 2)) * (2 * a)
      = (1 - 2 * a) * (a * (g₁ ^ 2 + g₂ ^ 2)) + 2 * a * (m₁ ^ 2 + m₂ ^ 2) := by ring
  have e10 : (1 - 2 * a) * (m₁ ^ 2 + m₂ ^ 2) + 2 * a * (m₁ ^ 2 + m₂ ^ 2) = m₁ ^ 2 + m₂ ^ 2 := by
    ring
  linarith

theorem poly_U0 (p : ℝ) (hp : 3 ≤ p) : 0 < (p - 1) ^ 2 * (5 * p + 2) - 2 * p ^ 2 := by
  obtain ⟨r, rfl⟩ : ∃ r, p = 3 + r := ⟨p - 3, by ring⟩
  have hr : 0 ≤ r := by linarith
  have e : (3 + r - 1) ^ 2 * (5 * (3 + r) + 2) - 2 * (3 + r) ^ 2
      = 5 * r ^ 3 + 35 * r ^ 2 + 76 * r + 50 := by ring
  rw [e]; positivity

theorem poly_E (p : ℝ) (hp : 3 ≤ p) :
    0 ≤ 5 * p ^ 7 + 2 * p ^ 6 - 66 * p ^ 5 + 84 * p ^ 4 - 27 * p ^ 3 + 10 * p ^ 2 - 4 * p - 8 := by
  obtain ⟨r, rfl⟩ : ∃ r, p = 3 + r := ⟨p - 3, by ring⟩
  have hr : 0 ≤ r := by linarith
  have e : 5 * (3 + r) ^ 7 + 2 * (3 + r) ^ 6 - 66 * (3 + r) ^ 5 + 84 * (3 + r) ^ 4
        - 27 * (3 + r) ^ 3 + 10 * (3 + r) ^ 2 - 4 * (3 + r) - 8
      = 5 * r ^ 7 + 107 * r ^ 6 + 915 * r ^ 5 + 4089 * r ^ 4 + 10296 * r ^ 3 + 14428 * r ^ 2
        + 10100 * r + 2500 := by ring
  rw [e]; positivity

theorem poly_E2 (p : ℝ) (hp : 3 ≤ p) :
    0 ≤ 6 * p ^ 6 - 28 * p ^ 5 + 44 * p ^ 4 - 28 * p ^ 3 - 2 * p ^ 2 + 16 * p - 8 := by
  obtain ⟨r, rfl⟩ : ∃ r, p = 3 + r := ⟨p - 3, by ring⟩
  have hr : 0 ≤ r := by linarith
  have e : 6 * (3 + r) ^ 6 - 28 * (3 + r) ^ 5 + 44 * (3 + r) ^ 4 - 28 * (3 + r) ^ 3
        - 2 * (3 + r) ^ 2 + 16 * (3 + r) - 8
      = 6 * r ^ 6 + 80 * r ^ 5 + 434 * r ^ 4 + 1220 * r ^ 3 + 1852 * r ^ 2 + 1408 * r + 400 := by
    ring
  rw [e]; positivity

/-- The quadratic inequality in `k = sqrt (s / (2 a))` at the worst slope `τ = 3 / p`. -/
theorem final_poly (p k : ℝ) (hp : 3 ≤ p) (hk : 0 ≤ k) (hK : 5 * p + 2 ≤ (p - 2) * k ^ 2) :
    2 * p * (p - 3) * (p - 1) * k + 2 * p ^ 2 ≤ (p - 2) * (p - 1) ^ 2 * k ^ 2 := by
  have hp2 : 0 < p - 2 := by linarith
  have hU := poly_U0 p hp
  have hE := poly_E p hp
  have hE2 := poly_E2 p hp
  have hz0 : 0 ≤ (p - 2) * k ^ 2 - (5 * p + 2) := by linarith
  have hu : (p - 2) * (p - 1) ^ 2 * k ^ 2 - 2 * p ^ 2
      = (p - 1) ^ 2 * ((p - 2) * k ^ 2 - (5 * p + 2)) + ((p - 1) ^ 2 * (5 * p + 2) - 2 * p ^ 2) := by
    ring
  have hu0 : 0 ≤ (p - 2) * (p - 1) ^ 2 * k ^ 2 - 2 * p ^ 2 := by
    rw [hu]; have := mul_nonneg (sq_nonneg (p - 1)) hz0; linarith
  have hv0 : 0 ≤ 2 * p * (p - 3) * (p - 1) * k := by
    have h1 : 0 ≤ 2 * p := by linarith
    have h2 : 0 ≤ p - 3 := by linarith
    have h3 : 0 ≤ p - 1 := by linarith
    exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) hk
  have hsq : (2 * p * (p - 3) * (p - 1) * k) ^ 2
      ≤ ((p - 2) * (p - 1) ^ 2 * k ^ 2 - 2 * p ^ 2) ^ 2 := by
    have h1 : (p - 2) * ((p - 2) * (p - 1) ^ 2 * k ^ 2 - 2 * p ^ 2) ^ 2
          - (p - 2) * (2 * p * (p - 3) * (p - 1) * k) ^ 2
        = (p - 2) * (p - 1) ^ 4 * ((p - 2) * k ^ 2 - (5 * p + 2)) ^ 2
          + (6 * p ^ 6 - 28 * p ^ 5 + 44 * p ^ 4 - 28 * p ^ 3 - 2 * p ^ 2 + 16 * p - 8)
            * ((p - 2) * k ^ 2 - (5 * p + 2))
          + (5 * p ^ 7 + 2 * p ^ 6 - 66 * p ^ 5 + 84 * p ^ 4 - 27 * p ^ 3 + 10 * p ^ 2
            - 4 * p - 8) := by ring
    have h2 : 0 ≤ (p - 2) * (p - 1) ^ 4 * ((p - 2) * k ^ 2 - (5 * p + 2)) ^ 2 :=
      mul_nonneg (mul_nonneg hp2.le (by positivity)) (sq_nonneg _)
    have h3 := mul_nonneg hE2 hz0
    have h4 : (p - 2) * (2 * p * (p - 3) * (p - 1) * k) ^ 2
        ≤ (p - 2) * ((p - 2) * (p - 1) ^ 2 * k ^ 2 - 2 * p ^ 2) ^ 2 := by linarith
    exact le_of_mul_le_mul_left h4 hp2
  have := (pow_le_pow_iff_left₀ hv0 hu0 two_ne_zero).mp hsq
  linarith

/-- Boundary inequality for the decentered arc, in real form: any slope `τ ≥ 3 / p` (in particular
`τ = tan (π / p) ≥ π / p`) dominates. Here `a = (p - 2) / (12 p)`, so `1 - 2 a = (5 p + 2) / (6 p)`
and `s / (2 a) = 6 p s / (p - 2)`. -/
theorem arc_boundary_core (p s R R' τ : ℝ) (hp : 2 < p) (hτ : 3 / p ≤ τ)
    (hs : (5 * p + 2) / (6 * p) ≤ s) (hR0 : 0 ≤ R) (hRR' : R ≤ R')
    (hR2 : R ^ 2 ≤ 6 * p * s / (p - 2)) :
    1 + (p - 1) * R ≤ τ * ((p - 1) ^ 2 * s + (p - 1) * R') := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hp2 : 0 < p - 2 := by linarith
  have hτ0 : 0 < τ := lt_of_lt_of_le (by positivity) hτ
  have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs
  have hR'0 : 0 ≤ R' := hR0.trans hRR'
  have hbr : 0 ≤ (p - 1) ^ 2 * s + (p - 1) * R' := by
    have h1 := mul_nonneg (sq_nonneg (p - 1)) hs0.le
    have h2 := mul_nonneg hp1.le hR'0
    linarith
  have hmul : (p - 1) * R ≤ (p - 1) * R' := mul_le_mul_of_nonneg_left hRR' hp1.le
  by_cases h1 : 1 ≤ τ
  · have hA : 1 ≤ (p - 1) ^ 2 * s := by
      have h6 : 1 ≤ (p - 1) ^ 2 * ((5 * p + 2) / (6 * p)) := by
        rw [← mul_div_assoc, le_div_iff₀ (by positivity)]
        nlinarith [mul_nonneg hp2.le (by nlinarith : (0 : ℝ) ≤ 5 * p ^ 2 + 2 * p - 1)]
      exact h6.trans (mul_le_mul_of_nonneg_left hs (sq_nonneg _))
    calc 1 + (p - 1) * R ≤ 1 * ((p - 1) ^ 2 * s + (p - 1) * R') := by linarith
      _ ≤ τ * ((p - 1) ^ 2 * s + (p - 1) * R') := mul_le_mul_of_nonneg_right h1 hbr
  · push Not at h1
    have hp3 : 3 < p := by
      by_contra h
      push Not at h
      have : 1 ≤ 3 / p := by rw [le_div_iff₀ hp0]; linarith
      linarith
    have hquo : 0 ≤ 6 * p * s / (p - 2) := div_nonneg (by positivity) hp2.le
    set k := Real.sqrt (6 * p * s / (p - 2)) with hk
    have hk0 : 0 ≤ k := Real.sqrt_nonneg _
    have hk2 : k ^ 2 = 6 * p * s / (p - 2) := Real.sq_sqrt hquo
    have hRk : R ≤ k := (le_abs_self R).trans (Real.abs_le_sqrt hR2)
    have hks : (p - 2) * k ^ 2 = 6 * p * s := by rw [hk2]; field_simp
    have hK : 5 * p + 2 ≤ (p - 2) * k ^ 2 := by
      rw [hks]; rw [div_le_iff₀ (by positivity)] at hs; linarith
    have hfin := final_poly p k hp3.le hk0 hK
    have hs_eq : s = (p - 2) * k ^ 2 / (6 * p) := by rw [hks]; field_simp
    have hQ : 0 ≤ (p - 1) ^ 2 * s + (p - 1) * k := by
      have h2 := mul_nonneg (sq_nonneg (p - 1)) hs0.le
      have h3 := mul_nonneg hp1.le hk0
      linarith
    have hbase : 1 + (1 - 3 / p) * (p - 1) * k ≤ 3 / p * (p - 1) ^ 2 * s := by
      have e : 3 / p * (p - 1) ^ 2 * s - (1 + (1 - 3 / p) * (p - 1) * k)
          = ((p - 2) * (p - 1) ^ 2 * k ^ 2 - (2 * p * (p - 3) * (p - 1) * k + 2 * p ^ 2))
            / (2 * p ^ 2) := by
        rw [hs_eq]; field_simp; ring
      have h5 : 0 ≤ ((p - 2) * (p - 1) ^ 2 * k ^ 2
          - (2 * p * (p - 3) * (p - 1) * k + 2 * p ^ 2)) / (2 * p ^ 2) :=
        div_nonneg (by linarith) (by positivity)
      linarith
    have hstep : 1 + (1 - τ) * (p - 1) * k ≤ τ * (p - 1) ^ 2 * s := by
      have hmono := mul_nonneg (sub_nonneg.mpr hτ) hQ
      have e2 : τ * (p - 1) ^ 2 * s - (1 + (1 - τ) * (p - 1) * k)
          = (3 / p * (p - 1) ^ 2 * s - (1 + (1 - 3 / p) * (p - 1) * k))
            + (τ - 3 / p) * ((p - 1) ^ 2 * s + (p - 1) * k) := by ring
      linarith
    have h4 : (1 - τ) * (p - 1) * R ≤ (1 - τ) * (p - 1) * k :=
      mul_le_mul_of_nonneg_left hRk (mul_nonneg (by linarith) hp1.le)
    have h5 : τ * ((p - 1) * R) ≤ τ * ((p - 1) * R') := mul_le_mul_of_nonneg_left hmul hτ0.le
    nlinarith [h4, h5, hstep]

/-- Halley's boundary slope: `(p + 1) ^ 2 > (p - 1) ^ 2`, the determinant of the Möbius correction
is positive. -/
theorem halley_det (p : ℝ) (hp : 0 < p) : 0 < (p + 1) ^ 2 - (p - 1) ^ 2 := by nlinarith

end LeanMath.Papers.ComplexRoots
