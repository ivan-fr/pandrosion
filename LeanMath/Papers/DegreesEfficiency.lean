import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

/-! # Degrees, efficiency and constants (Geometric Root Calculators, V28)

Formal statements for the results added in version 28 of the paper.

* Section 2.3 / Lemma 2.1: the exact support `kappaStar` and the exact contact identity
  (the algebraic part of the contact lemma; the asymptotic expansion is not formalized).
* Theorem 4.1: the polynomial `N9`, the constant `c9`, its positivity for `p > 2`, its value
  `7/648` at `p = 3` and its relation to the coefficient `D4` (the limit itself is not formalized).
* Proposition 4.5: rational degrees.
* Proposition 4.7: irrational degrees by rational approximation.
* Propositions 5.1 and 5.2: trace totals and the efficiency ordering, with the crossover at 13.
* Proposition 6.2: the subdivision invariant for every positive real degree.

No statement here concerns floating-point arithmetic or a physical drawing. -/

noncomputable section
namespace LeanMath.Papers.DegreesEfficiency
open Real

/-! ## The exact support and the contact identity (Section 2.3, Lemma 2.1) -/

/-- The exact normalized support slope, written with `θ = t ^ (1 / p)`. -/
def kappaStar (t θ : ℝ) : ℝ := (t - 1) / (θ - 1)

theorem kappaStar_denominator (t θ : ℝ) (hθ : θ ≠ 1) :
    kappaStar t θ - 1 + t = (t - 1) * θ / (θ - 1) := by
  unfold kappaStar
  have h1 : θ - 1 ≠ 0 := sub_ne_zero.mpr hθ
  field_simp
  ring

theorem kappaStar_denominator_ne_zero (t θ : ℝ) (hθ : θ ≠ 1) (hθ0 : θ ≠ 0) (ht : t ≠ 1) :
    kappaStar t θ - 1 + t ≠ 0 := by
  rw [kappaStar_denominator t θ hθ]
  exact div_ne_zero (mul_ne_zero (sub_ne_zero.mpr ht) hθ0) (sub_ne_zero.mpr hθ)

/-- Equation (2.4): the support `kappaStar` makes the update exact, because the correction factor
is `1 / θ = t ^ (-1 / p)`. -/
theorem exact_support (t θ : ℝ) (hθ : θ ≠ 1) (hθ0 : θ ≠ 0) (ht : t ≠ 1) :
    kappaStar t θ / (kappaStar t θ - 1 + t) = 1 / θ := by
  rw [kappaStar_denominator t θ hθ]
  unfold kappaStar
  have h1 : θ - 1 ≠ 0 := sub_ne_zero.mpr hθ
  have h2 : t - 1 ≠ 0 := sub_ne_zero.mpr ht
  field_simp

/-- Exact contact identity: the difference of two correction factors is the difference of the two
supports times `(t - 1)` over the product of the denominators. -/
theorem contact_identity (t κ κ' : ℝ) (h : κ - 1 + t ≠ 0) (h' : κ' - 1 + t ≠ 0) :
    κ / (κ - 1 + t) - κ' / (κ' - 1 + t)
      = (t - 1) * (κ - κ') / ((κ - 1 + t) * (κ' - 1 + t)) := by
  field_simp
  ring

/-- The error of one step, `s₊ - α` with `α = s / θ`, in terms of the support error
`κ - kappaStar`. This is the exact form of Lemma 2.1: a support error of order `ω` in `t - 1`
gives an update error of order `ω + 1`. -/
theorem update_error (s t θ κ : ℝ) (hθ : θ ≠ 1) (hθ0 : θ ≠ 0) (ht : t ≠ 1)
    (h : κ - 1 + t ≠ 0) :
    s * (κ / (κ - 1 + t)) - s / θ
      = s * ((t - 1) * (κ - kappaStar t θ)
          / ((κ - 1 + t) * (kappaStar t θ - 1 + t))) := by
  rw [← contact_identity t κ (kappaStar t θ) h
    (kappaStar_denominator_ne_zero t θ hθ hθ0 ht), exact_support t θ hθ hθ0 ht]
  ring

/-! ## The ninth-order constant (Theorem 4.1) -/

/-- The sextic of Theorem 4.1. -/
def N9 (p : ℝ) : ℝ :=
  21311 * p ^ 6 + 1650 * p ^ 5 - 21679 * p ^ 4 - 15532 * p ^ 3 - 4411 * p ^ 2 - 526 * p - 29

/-- The ninth-order error constant of the nested-radical iteration. -/
def c9 (p : ℝ) : ℝ :=
  (p ^ 2 - 1) * (p - 2) * N9 p / (2 ^ 11 * 3 ^ 4 * 5 ^ 3 * 7 ^ 2 * (3 * p + 1))

/-- The first unmatched coefficient of `q9 ^ 2 / t - Y` in powers of `w`, as a function of
`h = 1 / p` (equation (4.9)). -/
def D4 (h : ℝ) : ℝ :=
  (1 - 2 * h) * (1 + h)
      * (21311 + 1650 * h - 21679 * h ^ 2 - 15532 * h ^ 3 - 4411 * h ^ 4 - 526 * h ^ 5
          - 29 * h ^ 6)
    / (2 ^ 10 * 3 ^ 4 * 5 ^ 3 * 7 ^ 2 * (h + 3))

theorem N9_shift (ρ : ℝ) :
    N9 (2 + ρ) = 21311 * ρ ^ 6 + 257382 * ρ ^ 5 + 1273481 * ρ ^ 4 + 3286796 * ρ ^ 3
      + 4628741 * ρ ^ 2 + 3325430 * ρ + 926859 := by
  unfold N9
  ring

theorem N9_pos {p : ℝ} (hp : 2 < p) : 0 < N9 p := by
  obtain ⟨ρ, hρ, rfl⟩ : ∃ ρ : ℝ, 0 < ρ ∧ p = 2 + ρ := ⟨p - 2, by linarith, by ring⟩
  rw [N9_shift]
  positivity

/-- Theorem 4.1, positivity: the constant is positive for every real degree greater than two. -/
theorem c9_pos {p : ℝ} (hp : 2 < p) : 0 < c9 p := by
  unfold c9
  have h1 : 0 < N9 p := N9_pos hp
  have h2 : 0 < p ^ 2 - 1 := by nlinarith
  have h3 : 0 < p - 2 := by linarith
  have h4 : 0 < 3 * p + 1 := by linarith
  exact div_pos (mul_pos (mul_pos h2 h3) h1) (mul_pos (by norm_num) h4)

theorem N9_three : N9 3 = 13720000 := by
  unfold N9
  norm_num

/-- Theorem 4.1, cubic value: `c9 3 = 7 / 648`, in agreement with the cubic certificate. -/
theorem c9_three : c9 3 = 7 / 648 := by
  unfold c9 N9
  norm_num

/-- Theorem 4.1, proof step: `c9 p = (p - 1) p ^ 7 D4 (1 / p) / 2`. -/
theorem c9_eq_D4 {p : ℝ} (hp : 2 < p) : c9 p = (p - 1) * p ^ 7 * D4 (1 / p) / 2 := by
  unfold c9 D4 N9
  have hp0 : p ≠ 0 := by linarith
  have h3 : 3 * p + 1 ≠ 0 := by linarith
  have h4 : 1 / p + 3 ≠ 0 := by
    have : 0 < 1 / p := by positivity
    linarith
  field_simp
  ring

/-! ## Rational degrees (Proposition 4.5) -/

/-- `(X ^ ν) ^ (1 / μ) = X ^ (ν / μ)`. -/
theorem rational_degree_root {X : ℝ} (hX : 0 < X) (μ ν : ℕ) :
    (X ^ ν) ^ ((1 : ℝ) / μ) = X ^ ((ν : ℝ) / μ) := by
  rw [← Real.rpow_natCast X ν, ← Real.rpow_mul hX.le]
  congr 1
  ring

/-- For `p = μ / ν`, the root `X ^ (1 / p)` is the `μ`-th root of `X ^ ν`. -/
theorem rational_degree_eq {X : ℝ} (hX : 0 < X) (μ ν : ℕ) :
    (X ^ ν) ^ ((1 : ℝ) / μ) = X ^ ((1 : ℝ) / ((μ : ℝ) / ν)) := by
  rw [rational_degree_root hX μ ν, one_div_div]

/-- The root of a rational degree solves a polynomial equation with integer exponents. -/
theorem rational_degree_power {X : ℝ} (hX : 0 < X) {μ : ℕ} (hμ : 0 < μ) (ν : ℕ) :
    (X ^ ((ν : ℝ) / μ)) ^ μ = X ^ ν := by
  have hμ' : (μ : ℝ) ≠ 0 := by exact_mod_cast hμ.ne'
  have e : (ν : ℝ) / μ * μ = ν := by field_simp
  rw [← Real.rpow_natCast (X ^ ((ν : ℝ) / μ)) μ, ← Real.rpow_mul hX.le, e, Real.rpow_natCast]

/-- Proposition 4.5 (i), in abstract form. Let `F p X` be any family of iterations which, for every
real degree `p > 2`, every positive input and every positive start, converges to `X ^ (1 / p)`
(this is Theorem 4.4 for the nested-radical map and Theorem 3.1 for the decentered arc). Then, run
with the integer degree `μ ≥ 3` on the input `X ^ ν`, it converges to `X ^ (1 / p)` for the rational
degree `p = μ / ν`. Only integer powers `u ^ μ` and the fixed input `X ^ ν` are needed. -/
theorem rational_degree_convergence
    (F : ℝ → ℝ → ℝ → ℝ)
    (hF : ∀ p X u₀ : ℝ, 2 < p → 0 < X → 0 < u₀ →
      Filter.Tendsto (fun n : ℕ => (F p X)^[n] u₀) Filter.atTop (nhds (X ^ ((1 : ℝ) / p))))
    {X u₀ : ℝ} (hX : 0 < X) (hu : 0 < u₀) {μ : ℕ} (hμ : 3 ≤ μ) (ν : ℕ) :
    Filter.Tendsto (fun n : ℕ => (F (μ : ℝ) (X ^ ν))^[n] u₀) Filter.atTop
      (nhds (X ^ ((1 : ℝ) / ((μ : ℝ) / ν)))) := by
  have hμ2 : (2 : ℝ) < (μ : ℝ) := by exact_mod_cast (show 2 < μ by omega)
  have h := hF (μ : ℝ) (X ^ ν) u₀ hμ2 (pow_pos hX ν) hu
  rwa [rational_degree_eq hX μ ν] at h

/-! ## Irrational degrees by rational approximation (Proposition 4.7) -/

theorem abs_exp_sub_one_le (y : ℝ) : |Real.exp y - 1| ≤ Real.exp |y| - 1 := by
  have h1 := Real.add_one_le_exp y
  have h2 := Real.add_one_le_exp (-y)
  rcases le_total 0 y with hy | hy
  · have e1 : |y| = y := abs_of_nonneg hy
    rw [e1, abs_le]
    constructor <;> linarith
  · have e1 : |y| = -y := abs_of_nonpos hy
    have e2 : Real.exp y ≤ 1 := Real.exp_le_one_iff.mpr hy
    rw [e1, abs_le]
    constructor <;> linarith

/-- Two powers of the same base with close exponents are close in relative terms. -/
theorem rpow_ratio_bound {X : ℝ} (hX : 0 < X) {a b η : ℝ} (h : |a - b| ≤ η) :
    |X ^ a / X ^ b - 1| ≤ Real.exp (η * |Real.log X|) - 1 := by
  rw [← Real.rpow_sub hX, Real.rpow_def_of_pos hX]
  have hy : |Real.log X * (a - b)| ≤ η * |Real.log X| := by
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right h (abs_nonneg _)
  have h1 := abs_exp_sub_one_le (Real.log X * (a - b))
  have h2 := Real.exp_le_exp.mpr hy
  linarith

/-- Proposition 4.7, first bound: replacing the exponent `1 / p` by a rational `ν / μ` within `η`
changes the root by a relative amount at most `exp (η |log X|) - 1`. -/
theorem irrational_degree_bound {X : ℝ} (hX : 0 < X) {p η : ℝ} {μ ν : ℕ}
    (h : |(ν : ℝ) / μ - 1 / p| ≤ η) :
    |X ^ ((ν : ℝ) / μ) / X ^ ((1 : ℝ) / p) - 1| ≤ Real.exp (η * |Real.log X|) - 1 :=
  rpow_ratio_bound hX h

/-- Composition of two relative errors. -/
theorem compose_relative_error {q ρ A ε₁ : ℝ} (hq : |q - 1| ≤ ε₁) (hρ : |ρ - 1| ≤ A - 1)
    (hρ0 : 0 ≤ ρ) : |q * ρ - 1| ≤ (1 + ε₁) * A - 1 := by
  have hε : 0 ≤ ε₁ := le_trans (abs_nonneg _) hq
  have hA : 1 ≤ A := by linarith [abs_nonneg (ρ - 1)]
  obtain ⟨hq1, hq2⟩ := abs_le.mp hq
  obtain ⟨hρ1, hρ2⟩ := abs_le.mp hρ
  have u1 : q * ρ ≤ (1 + ε₁) * ρ := mul_le_mul_of_nonneg_right (by linarith) hρ0
  have u2 : (1 + ε₁) * ρ ≤ (1 + ε₁) * A := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have l1 : (1 - ε₁) * ρ ≤ q * ρ := mul_le_mul_of_nonneg_right (by linarith) hρ0
  rw [abs_le]
  constructor
  · rcases le_total ε₁ 1 with hε1 | hε1
    · have l2 : (1 - ε₁) * (2 - A) ≤ (1 - ε₁) * ρ :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      nlinarith [mul_nonneg hε (sub_nonneg.mpr hA)]
    · have l2 : (1 - ε₁) * A ≤ (1 - ε₁) * ρ :=
        mul_le_mul_of_nonpos_left (by linarith) (by linarith)
      nlinarith
  · linarith

/-- Proposition 4.7, second bound: an approximation `ũ` of the rational-degree root `X ^ (ν / μ)`
with relative error `ε₁` approximates `X ^ (1 / p)` with relative error at most
`(1 + ε₁) exp (η |log X|) - 1`. -/
theorem irrational_degree_total {X : ℝ} (hX : 0 < X) {p η ε₁ u : ℝ} {μ ν : ℕ}
    (h : |(ν : ℝ) / μ - 1 / p| ≤ η) (hu : |u / X ^ ((ν : ℝ) / μ) - 1| ≤ ε₁) :
    |u / X ^ ((1 : ℝ) / p) - 1| ≤ (1 + ε₁) * Real.exp (η * |Real.log X|) - 1 := by
  have hr' : 0 < X ^ ((ν : ℝ) / μ) := Real.rpow_pos_of_pos hX _
  have hr : 0 < X ^ ((1 : ℝ) / p) := Real.rpow_pos_of_pos hX _
  have e : u / X ^ ((1 : ℝ) / p)
      = u / X ^ ((ν : ℝ) / μ) * (X ^ ((ν : ℝ) / μ) / X ^ ((1 : ℝ) / p)) := by
    field_simp
  rw [e]
  exact compose_relative_error hu (irrational_degree_bound hX h) (div_pos hr' hr).le

/-! ## Trace totals (Proposition 5.1) -/

/-- The ten rows of Table 4 add up to `32 j + (2p+3) p + 12 c`, and with a parallel counted as
`2 j + 3 c` this is `10 p + 59` traces. -/
theorem nested_inventory_total (p : ℕ) :
    (1 + 2 + 5 + 9 + 2 + 7 + 2 + 2 + 1 + 1 = 32) ∧
    ((2 * p - 1) + 1 + 1 + 2 = 2 * p + 3 ∨ p = 0) ∧
    (2 + 2 + 3 + 1 + 3 + 1 = 12) ∧
    (32 + 2 * (2 * p + 3)) + (12 + 3 * (2 * p + 3)) = 10 * p + 59 := by
  refine ⟨by norm_num, ?_, by norm_num, by ring⟩
  rcases Nat.eq_zero_or_pos p with h | h
  · exact Or.inr h
  · left
    omega

/-- The direct enclosure costs `15 n + 63` traces (Table 9). -/
theorem subdivision_inventory_total (n : ℕ) :
    (5 + 4 * n + (2 * n + 2) + 49 + 2 * n) + (4 * n + 7 + 3 * n) = 15 * n + 63 := by
  ring

/-! ## Efficiency index (Proposition 5.2) -/

/-- Logarithm of the efficiency index of an iteration of order `ρ` costing `N` traces per step. -/
def effIndex (ρ N : ℝ) : ℝ := Real.log ρ / N

theorem log_two_lt_log_three : Real.log 2 < Real.log 3 :=
  Real.log_lt_log (by norm_num) (by norm_num)

theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem log_nine : Real.log 9 = 2 * Real.log 3 := by
  have : (9 : ℝ) = 3 ^ 2 := by norm_num
  rw [this, Real.log_pow]
  norm_num

theorem log_four : Real.log 4 = 2 * Real.log 2 := by
  have : (4 : ℝ) = 2 ^ 2 := by norm_num
  rw [this, Real.log_pow]
  norm_num

/-- `2 ^ 39 < 3 ^ 37`, in logarithmic form. -/
theorem log_ineq_AK : 39 * Real.log 2 < 37 * Real.log 3 := by
  have h : Real.log ((2 : ℝ) ^ 39) < Real.log ((3 : ℝ) ^ 37) :=
    Real.log_lt_log (by positivity) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  exact_mod_cast h

/-- `9 ^ 129 < 5 ^ 179`, in logarithmic form. -/
theorem log_ineq_twelve : 129 * Real.log 9 < 179 * Real.log 5 := by
  have h : Real.log ((9 : ℝ) ^ 129) < Real.log ((5 : ℝ) ^ 179) :=
    Real.log_lt_log (by positivity) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  exact_mod_cast h

/-- `5 ^ 189 < 9 ^ 139`, in logarithmic form. -/
theorem log_ineq_thirteen : 189 * Real.log 5 < 139 * Real.log 9 := by
  have h : Real.log ((5 : ℝ) ^ 189) < Real.log ((9 : ℝ) ^ 139) :=
    Real.log_lt_log (by positivity) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  exact_mod_cast h

/-- `2 ^ 139 < 3 ^ 89`, in logarithmic form. -/
theorem log_ineq_eight : 139 * Real.log 2 < 89 * Real.log 3 := by
  have h : Real.log ((2 : ℝ) ^ 139) < Real.log ((3 : ℝ) ^ 89) :=
    Real.log_lt_log (by positivity) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  exact_mod_cast h

theorem log_five_lt_log_nine : Real.log 5 < Real.log 9 :=
  Real.log_lt_log (by norm_num) (by norm_num)

theorem log_five_pos : 0 < Real.log 5 := Real.log_pos (by norm_num)

/-- AK (order 2, `10p+7` traces) is less efficient than AD (order 3, `10p+9` traces). -/
theorem effIndex_AK_lt_AD {p : ℝ} (hp : 3 ≤ p) :
    effIndex 2 (10 * p + 7) < effIndex 3 (10 * p + 9) := by
  unfold effIndex
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  have h1 := log_ineq_AK
  have h2 := log_two_lt_log_three
  have h3 : 3 * (Real.log 3 - Real.log 2) ≤ p * (Real.log 3 - Real.log 2) :=
    mul_le_mul_of_nonneg_right hp (by linarith)
  nlinarith

/-- At equal cost the index increases with the order: AD < projective AD < decentered AD. -/
theorem effIndex_AD_lt_proj {p : ℝ} (hp : 0 < p) :
    effIndex 3 (10 * p + 9) < effIndex 4 (10 * p + 9) := by
  unfold effIndex
  exact div_lt_div_of_pos_right (Real.log_lt_log (by norm_num) (by norm_num)) (by linarith)

theorem effIndex_proj_lt_dec {p : ℝ} (hp : 0 < p) :
    effIndex 4 (10 * p + 9) < effIndex 5 (10 * p + 9) := by
  unfold effIndex
  exact div_lt_div_of_pos_right (Real.log_lt_log (by norm_num) (by norm_num)) (by linarith)

/-- The crossover degree of Proposition 5.2. -/
def crossover : ℝ :=
  (59 * Real.log 5 - 9 * Real.log 9) / (10 * (Real.log 9 - Real.log 5))

theorem crossover_eq :
    crossover = (59 * Real.log 5 - 9 * Real.log 9) / (10 * Real.log (9 / 5)) := by
  unfold crossover
  rw [Real.log_div (by norm_num) (by norm_num)]

/-- Proposition 5.2: the nested support (order 9, `10p+59` traces) is more efficient than the
decentered arc (order 5, `10p+9` traces) exactly above the crossover degree. -/
theorem effIndex_nest_gt_dec_iff {p : ℝ} (hp : 0 < p) :
    effIndex 5 (10 * p + 9) < effIndex 9 (10 * p + 59) ↔ crossover < p := by
  have hd : 0 < 10 * (Real.log 9 - Real.log 5) := by linarith [log_five_lt_log_nine]
  unfold effIndex crossover
  rw [div_lt_div_iff₀ (by linarith) (by linarith), div_lt_iff₀ hd]
  constructor <;> intro h <;> nlinarith

/-- The crossover lies strictly between 12 and 13. -/
theorem crossover_bounds : 12 < crossover ∧ crossover < 13 := by
  have hd : 0 < 10 * (Real.log 9 - Real.log 5) := by linarith [log_five_lt_log_nine]
  have h12 := log_ineq_twelve
  have h13 := log_ineq_thirteen
  unfold crossover
  rw [lt_div_iff₀ hd, div_lt_iff₀ hd]
  constructor <;> linarith

/-- Proposition 5.2 for integer degrees: the nested support wins if and only if `p ≥ 13`. -/
theorem effIndex_nest_gt_dec_nat {p : ℕ} (hp : 0 < p) :
    effIndex 5 (10 * (p : ℝ) + 9) < effIndex 9 (10 * (p : ℝ) + 59) ↔ 13 ≤ p := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  rw [effIndex_nest_gt_dec_iff hp']
  obtain ⟨h1, h2⟩ := crossover_bounds
  constructor
  · intro h
    have : (12 : ℝ) < p := lt_trans h1 h
    exact_mod_cast this
  · intro h
    have : (13 : ℝ) ≤ p := by exact_mod_cast h
    linarith

/-- The nested support is more efficient than AD (order 3) exactly when `10 p > 41`. -/
theorem effIndex_nest_gt_AD_iff {p : ℝ} (hp : 0 < p) :
    effIndex 3 (10 * p + 9) < effIndex 9 (10 * p + 59) ↔ 41 < 10 * p := by
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  unfold effIndex
  rw [div_lt_div_iff₀ (by linarith) (by linarith), log_nine]
  constructor <;> intro h <;> nlinarith

/-- The nested support is more efficient than projective AD (order 4) for every `p ≥ 8`. -/
theorem effIndex_nest_gt_proj {p : ℝ} (hp : 8 ≤ p) :
    effIndex 4 (10 * p + 9) < effIndex 9 (10 * p + 59) := by
  unfold effIndex
  rw [div_lt_div_iff₀ (by linarith) (by linarith), log_nine, log_four]
  have h1 := log_ineq_eight
  have h2 := log_two_lt_log_three
  have h3 : 8 * (Real.log 3 - Real.log 2) ≤ p * (Real.log 3 - Real.log 2) :=
    mul_le_mul_of_nonneg_right hp (by linarith)
  nlinarith

/-- `3 ^ 79 < 2 ^ 129`, in logarithmic form. -/
theorem log_ineq_seven : 79 * Real.log 3 < 129 * Real.log 2 := by
  have h : Real.log ((3 : ℝ) ^ 79) < Real.log ((2 : ℝ) ^ 129) :=
    Real.log_lt_log (by positivity) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  exact_mod_cast h

/-- Conversely, projective AD is more efficient than the nested support for every `p ≤ 7`. -/
theorem effIndex_proj_gt_nest {p : ℝ} (hp0 : 0 < p) (hp : p ≤ 7) :
    effIndex 9 (10 * p + 59) < effIndex 4 (10 * p + 9) := by
  unfold effIndex
  rw [div_lt_div_iff₀ (by linarith) (by linarith), log_nine, log_four]
  have h1 := log_ineq_seven
  have h2 := log_two_lt_log_three
  have h3 : p * (Real.log 3 - Real.log 2) ≤ 7 * (Real.log 3 - Real.log 2) :=
    mul_le_mul_of_nonneg_right hp (by linarith)
  nlinarith

/-! ## Subdivision for every positive real degree (Proposition 6.2) -/

/-- Proposition 6.2 (i): starting the subdivision from `a = X ^ k`, `b = X ^ (k+1)` and weight
`λ = 1 / p - k`, with `k ≤ 1 / p < k + 1`, the invariant `r = a ^ (1 - λ) b ^ λ` and the gap
`b / a = X` are those of the case `p ≥ 1`. -/
theorem subdivision_start {X : ℝ} (hX : 0 < X) (p : ℝ) (k : ℕ)
    (hk : (k : ℝ) ≤ 1 / p) (hk1 : 1 / p < (k : ℝ) + 1) :
    0 ≤ 1 / p - k ∧ 1 / p - k < 1 ∧
      (X ^ k) ^ (1 - (1 / p - k)) * (X ^ (k + 1)) ^ (1 / p - k) = X ^ ((1 : ℝ) / p) ∧
      X ^ (k + 1) / X ^ k = X := by
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · have e1 : (X ^ k) ^ (1 - (1 / p - k)) = X ^ ((k : ℝ) * (1 - (1 / p - k))) := by
      rw [← Real.rpow_natCast X k, ← Real.rpow_mul hX.le]
    have e2 : (X ^ (k + 1)) ^ (1 / p - k) = X ^ (((k : ℝ) + 1) * (1 / p - k)) := by
      rw [← Real.rpow_natCast X (k + 1), ← Real.rpow_mul hX.le]
      push_cast
      rfl
    rw [e1, e2, ← Real.rpow_add hX]
    congr 1
    ring
  · have hk0 : X ^ k ≠ 0 := (pow_pos hX k).ne'
    rw [pow_succ]
    field_simp

/-- Proposition 6.2 (i) with the canonical choice `k = ⌊1 / p⌋`. -/
theorem subdivision_start_floor {X : ℝ} (hX : 0 < X) {p : ℝ} (hp : 0 < p) :
    0 ≤ 1 / p - (⌊1 / p⌋₊ : ℝ) ∧ 1 / p - (⌊1 / p⌋₊ : ℝ) < 1 ∧
      (X ^ ⌊1 / p⌋₊) ^ (1 - (1 / p - (⌊1 / p⌋₊ : ℝ)))
          * (X ^ (⌊1 / p⌋₊ + 1)) ^ (1 / p - (⌊1 / p⌋₊ : ℝ)) = X ^ ((1 : ℝ) / p) ∧
      X ^ (⌊1 / p⌋₊ + 1) / X ^ ⌊1 / p⌋₊ = X :=
  subdivision_start hX p ⌊1 / p⌋₊ (Nat.floor_le (by positivity)) (Nat.lt_floor_add_one _)

/-- Proposition 6.2 (ii), (iii): inversion maps an enclosure `[L, U]` to `[1 / U, 1 / L]` with the
same ratio, hence the same relative width. -/
theorem inverted_enclosure {L U r : ℝ} (hL : 0 < L) (hr : 0 < r) (h1 : L ≤ r) (h2 : r ≤ U) :
    1 / U ≤ 1 / r ∧ 1 / r ≤ 1 / L ∧ (1 / L) / (1 / U) = U / L := by
  have hU : 0 < U := lt_of_lt_of_le hr h2
  refine ⟨one_div_le_one_div_of_le hr h2, one_div_le_one_div_of_le hL h1, ?_⟩
  field_simp

/-- Negative degrees: `X ^ (1 / p)` for `p < 0` is the inverse of the root of degree `-p`. -/
theorem negative_degree {X : ℝ} (hX : 0 < X) (p : ℝ) :
    X ^ ((1 : ℝ) / p) = (X ^ ((1 : ℝ) / (-p)))⁻¹ := by
  rw [← Real.rpow_neg hX.le]
  congr 1
  rw [one_div, one_div, inv_neg, neg_neg]

end LeanMath.Papers.DegreesEfficiency
