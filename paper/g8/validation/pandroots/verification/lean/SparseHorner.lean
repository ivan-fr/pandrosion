import Mathlib

/-! # Horner's rule over runs of zero coefficients (pandroots 0.13.0)

In double precision the program evaluates `S`, `S'` and `S''/2` together: one step of Horner's rule is

  `(p₀, p₁, p₂) ↦ (p₀ x + c, p₁ x + p₀, p₂ x + p₁)`.

For a polynomial with few terms, a run of `g - 1` zero coefficients followed by a coefficient `c` is `g`
such steps, the first `g - 1` with nothing to add.  Since version 0.13.0 they are made at once,

  `p₀ ← p₀ x^g + c`,  `p₁ ← p₁ x^g + g p₀ x^(g-1)`,  `p₂ ← p₂ x^g + g p₁ x^(g-1) + g (g-1)/2 p₀ x^(g-2)`,

with `x^g` by repeated squaring.

* `zero_steps`, `gap_step`: `n` steps with nothing to add, then one step with `c`, in terms of the two
  sequences `q1 n = n x^(n-1)` and `q2 n = n (n-1)/2 x^(n-2)` defined by their recurrences;
* `q1_succ`, `two_q2`: their closed forms, without subtraction in the exponents;
* `value_alone`: the value of `S` that the three-component rule computes is that of the rule for `S`
  alone (the certificate reads its bound from the evaluation of the sweeps since 0.13.0).

The rounding.  The bound of the certificate counts the products that the value of `S` goes through: `g`
for a run in the dense rule.  With `x^g` computed by repeated squaring it goes through one product by
`x^g`, and `x^g` itself, whatever the order of its products, is a product of `g` factors `x`:

* `Comp`, `comp_bound`: if every product has a relative error at most `u`, a power `x^(k+1)` computed
  with `k` products in any order is within `((1 + u)^k - 1) |x|^(k+1)` of the true one, which is the bound
  of `k` successive products.

Not formalised: the floating-point model itself (that a product of two doubles has a relative error of at
most `u`, away from underflow), the operations that underflow (`Poly::tiny`), and the Rust code. -/

namespace LeanMath.Papers.SparseHorner

section Algebra
variable {R : Type*} [CommRing R]

/-- One step of Horner's rule for `(S, S', S''/2)`. -/
def step (x c : R) (s : R × R × R) : R × R × R :=
  (s.1 * x + c, s.2.1 * x + s.1, s.2.2 * x + s.2.1)

/-- `q1 n = n x^(n-1)`, by its recurrence. -/
def q1 (x : R) : ℕ → R
  | 0 => 0
  | n + 1 => q1 x n * x + x ^ n

/-- `q2 n = n (n-1)/2 x^(n-2)`, by its recurrence. -/
def q2 (x : R) : ℕ → R
  | 0 => 0
  | n + 1 => q2 x n * x + q1 x n

theorem q1_step (x : R) (n : ℕ) : q1 x (n + 1) = q1 x n * x + x ^ n := rfl

theorem q2_step (x : R) (n : ℕ) : q2 x (n + 1) = q2 x n * x + q1 x n := rfl

/-- `n` steps with nothing to add. -/
theorem zero_steps (x p0 p1 p2 : R) (n : ℕ) :
    (step x 0)^[n] (p0, p1, p2)
      = (p0 * x ^ n, p1 * x ^ n + p0 * q1 x n, p2 * x ^ n + p1 * q1 x n + p0 * q2 x n) := by
  induction n with
  | zero => simp [q1, q2]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [step, q1_step, q2_step, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩ <;> ring

/-- A run of `n` zero coefficients and then the coefficient `c`: `n + 1` steps in one. -/
theorem gap_step (x c p0 p1 p2 : R) (n : ℕ) :
    step x c ((step x 0)^[n] (p0, p1, p2))
      = (p0 * x ^ (n + 1) + c, p1 * x ^ (n + 1) + p0 * q1 x (n + 1),
          p2 * x ^ (n + 1) + p1 * q1 x (n + 1) + p0 * q2 x (n + 1)) := by
  rw [zero_steps]
  simp only [step, q1_step, q2_step, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> ring

/-- `q1 (n + 1) = (n + 1) x^n`. -/
theorem q1_succ (x : R) (n : ℕ) : q1 x (n + 1) = ((n + 1 : ℕ) : R) * x ^ n := by
  induction n with
  | zero =>
    rw [q1_step]
    simp [q1]
  | succ n ih =>
    rw [q1_step, ih]
    push_cast
    ring

/-- `2 q2 (n + 2) = (n + 2) (n + 1) x^n`. -/
theorem two_q2 (x : R) (n : ℕ) :
    2 * q2 x (n + 1 + 1) = ((n + 1 + 1 : ℕ) : R) * ((n + 1 : ℕ) : R) * x ^ n := by
  induction n with
  | zero =>
    rw [q2_step, q2_step, q1_step]
    simp [q1, q2]
  | succ n ih =>
    have h1 := q1_succ x (n + 1)
    calc 2 * q2 x (n + 1 + 1 + 1)
        = 2 * q2 x (n + 1 + 1) * x + 2 * q1 x (n + 1 + 1) := by rw [q2_step x (n + 1 + 1)]; ring
      _ = ((n + 1 + 1 : ℕ) : R) * ((n + 1 : ℕ) : R) * x ^ n * x
            + 2 * (((n + 1 + 1 : ℕ) : R) * x ^ (n + 1)) := by rw [ih, h1]
      _ = ((n + 1 + 1 + 1 : ℕ) : R) * ((n + 1 + 1 : ℕ) : R) * x ^ (n + 1) := by push_cast; ring

/-- The value of `S` does not depend on the derivatives being computed with it. -/
theorem value_alone (x : R) (cs : List R) (s : R × R × R) :
    (cs.foldl (fun s c => step x c s) s).1 = cs.foldl (fun p c => p * x + c) s.1 := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih => exact ih (step x c s)

end Algebra

section Rounding

/-- `Comp u x k y`: `y` is a value of `x^(k+1)` computed with `k` products, each one within the relative
error `u` of the product of its two computed factors, in any order (repeated squaring is one). -/
inductive Comp (u : ℝ) (x : ℂ) : ℕ → ℂ → Prop
  | base : Comp u x 0 x
  | mul {a b : ℕ} {ya yb y : ℂ} : Comp u x a ya → Comp u x b yb → ‖y - ya * yb‖ ≤ u * ‖ya * yb‖ →
      Comp u x (a + b + 1) y

/-- A power computed with `k` products is within `((1 + u)^k - 1) |x|^(k+1)` of the true one. -/
theorem comp_bound (u : ℝ) (hu : 0 ≤ u) (x : ℂ) (k : ℕ) (y : ℂ) (h : Comp u x k y) :
    ‖y - x ^ (k + 1)‖ ≤ ((1 + u) ^ k - 1) * ‖x‖ ^ (k + 1) := by
  induction h with
  | base => simp
  | @mul a b ya yb y ha hb hy iha ihb =>
    have h1u : (0 : ℝ) ≤ 1 + u := by linarith
    have hea : (0 : ℝ) ≤ (1 + u) ^ a := pow_nonneg h1u a
    have heb : (0 : ℝ) ≤ (1 + u) ^ b := pow_nonneg h1u b
    have hA : (0 : ℝ) ≤ ‖x‖ ^ (a + 1) := pow_nonneg (norm_nonneg x) _
    have hB : (0 : ℝ) ≤ ‖x‖ ^ (b + 1) := pow_nonneg (norm_nonneg x) _
    have nXa : ‖x ^ (a + 1)‖ = ‖x‖ ^ (a + 1) := norm_pow x _
    have nXb : ‖x ^ (b + 1)‖ = ‖x‖ ^ (b + 1) := norm_pow x _
    -- the computed factors are not larger than (1 + u)^a |x|^(a+1) and (1 + u)^b |x|^(b+1)
    have na : ‖ya‖ ≤ (1 + u) ^ a * ‖x‖ ^ (a + 1) := by
      have t : ‖ya‖ ≤ ‖ya - x ^ (a + 1)‖ + ‖x ^ (a + 1)‖ := by
        have := norm_add_le (ya - x ^ (a + 1)) (x ^ (a + 1))
        simpa using this
      have e : ((1 + u) ^ a - 1) * ‖x‖ ^ (a + 1) + ‖x‖ ^ (a + 1) = (1 + u) ^ a * ‖x‖ ^ (a + 1) := by ring
      linarith
    have nb : ‖yb‖ ≤ (1 + u) ^ b * ‖x‖ ^ (b + 1) := by
      have t : ‖yb‖ ≤ ‖yb - x ^ (b + 1)‖ + ‖x ^ (b + 1)‖ := by
        have := norm_add_le (yb - x ^ (b + 1)) (x ^ (b + 1))
        simpa using this
      have e : ((1 + u) ^ b - 1) * ‖x‖ ^ (b + 1) + ‖x‖ ^ (b + 1) = (1 + u) ^ b * ‖x‖ ^ (b + 1) := by ring
      linarith
    have nab : ‖ya * yb‖ ≤ (1 + u) ^ a * ‖x‖ ^ (a + 1) * ((1 + u) ^ b * ‖x‖ ^ (b + 1)) := by
      rw [norm_mul]
      exact mul_le_mul na nb (norm_nonneg _) (mul_nonneg hea hA)
    -- the product of the computed factors against the product of the true ones
    have split : ya * yb - x ^ (a + 1) * x ^ (b + 1)
        = (ya - x ^ (a + 1)) * yb + x ^ (a + 1) * (yb - x ^ (b + 1)) := by ring
    have t1 : ‖(ya - x ^ (a + 1)) * yb‖
        ≤ ((1 + u) ^ a - 1) * ‖x‖ ^ (a + 1) * ((1 + u) ^ b * ‖x‖ ^ (b + 1)) := by
      rw [norm_mul]
      exact mul_le_mul iha nb (norm_nonneg _) (le_trans (norm_nonneg _) iha)
    have t2 : ‖x ^ (a + 1) * (yb - x ^ (b + 1))‖
        ≤ ‖x‖ ^ (a + 1) * (((1 + u) ^ b - 1) * ‖x‖ ^ (b + 1)) := by
      rw [norm_mul, nXa]
      exact mul_le_mul_of_nonneg_left ihb hA
    have t3 : ‖ya * yb - x ^ (a + 1) * x ^ (b + 1)‖
        ≤ ((1 + u) ^ a - 1) * ‖x‖ ^ (a + 1) * ((1 + u) ^ b * ‖x‖ ^ (b + 1))
          + ‖x‖ ^ (a + 1) * (((1 + u) ^ b - 1) * ‖x‖ ^ (b + 1)) := by
      rw [split]
      exact le_trans (norm_add_le _ _) (add_le_add t1 t2)
    have t4 : u * ‖ya * yb‖ ≤ u * ((1 + u) ^ a * ‖x‖ ^ (a + 1) * ((1 + u) ^ b * ‖x‖ ^ (b + 1))) :=
      mul_le_mul_of_nonneg_left nab hu
    -- together
    have split2 : y - x ^ (a + b + 1 + 1) = (y - ya * yb) + (ya * yb - x ^ (a + 1) * x ^ (b + 1)) := by ring
    have t5 : ‖y - x ^ (a + b + 1 + 1)‖ ≤ ‖y - ya * yb‖ + ‖ya * yb - x ^ (a + 1) * x ^ (b + 1)‖ := by
      rw [split2]
      exact norm_add_le _ _
    have e : ((1 + u) ^ (a + b + 1) - 1) * ‖x‖ ^ (a + b + 1 + 1)
        = u * ((1 + u) ^ a * ‖x‖ ^ (a + 1) * ((1 + u) ^ b * ‖x‖ ^ (b + 1)))
          + (((1 + u) ^ a - 1) * ‖x‖ ^ (a + 1) * ((1 + u) ^ b * ‖x‖ ^ (b + 1))
            + ‖x‖ ^ (a + 1) * (((1 + u) ^ b - 1) * ‖x‖ ^ (b + 1))) := by ring
    linarith [e, t5, hy, t4, t3]

end Rounding

end LeanMath.Papers.SparseHorner
