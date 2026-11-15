import Mathlib

/-! # The step of a cluster (pandroots 0.9.0)

Seen from a distance much larger than its width, a cluster of `K` roots is a shifted power
`f(w) = (w - g)^K - a`.  The solver takes the function deflated of the points outside the cluster, reads
`A = f'/f` and `B = (f'² - f f'')/f²` at one point `z`, and applies the step of degree `p = K` of the
rectangle:

  `t = (K B - A²) / ((K - 1) A²)`,   `u = K / (A (1 - t))`,   new points `z - u + u ω`, `ω^K = t`.

For the shifted power itself this is exact:

* `eval_shifted`, `eval_derivative_shifted`, `eval_derivative2_shifted`: the values of `f`, `f'`, `f''`;
* `cursor`: the cursor is `t = a / u^K`, with `u = z - g`;
* `anchor`: `K / (A (1 - t)) = u`, so `z - u` is the centre `g` (the virtual anchor);
* `model_root`: every `ω` with `ω^K = t` gives a root `g + u ω` of `f`: the `K` roots, in one step.

This is the statement that the exact support of the `p`-th root returns `t^(1/p)` in one step, read on
the function `(w - g)^p - a`.  Not formalised: how close a cluster is to a shifted power (the roots of a
general cluster are not on a circle; for `K = 2` every quadratic is a shifted power), the Rust code, and
the choice of the points where the step is used.  The discs returned are certified after the move. -/

namespace LeanMath.Papers.ClusterStep
open Polynomial

/-- `f = (X - g)^(n+2) - a`: a cluster of `K = n + 2` roots. -/
noncomputable def shifted (g a : ℂ) (n : ℕ) : ℂ[X] := (X - C g) ^ (n + 2) - C a

theorem eval_shifted (g a z : ℂ) (n : ℕ) : (shifted g a n).eval z = (z - g) ^ (n + 2) - a := by
  simp [shifted]

theorem eval_derivative_shifted (g a z : ℂ) (n : ℕ) :
    (derivative (shifted g a n)).eval z = ((n : ℂ) + 2) * (z - g) ^ (n + 1) := by
  simp [shifted, derivative_pow]

theorem eval_derivative2_shifted (g a z : ℂ) (n : ℕ) :
    (derivative (derivative (shifted g a n))).eval z
      = ((n : ℂ) + 2) * ((n : ℂ) + 1) * (z - g) ^ n := by
  simp [shifted, derivative_pow]
  ring

/-- The cursor of the step of degree `K = n + 2` is `a / u^K`. -/
theorem cursor (u a : ℂ) (n : ℕ) (hu : u ≠ 0) (hf : u ^ (n + 2) - a ≠ 0) :
    let F := u ^ (n + 2) - a
    let F1 := ((n : ℂ) + 2) * u ^ (n + 1)
    let F2 := ((n : ℂ) + 2) * ((n : ℂ) + 1) * u ^ n
    let A := F1 / F
    let B := (F1 ^ 2 - F * F2) / F ^ 2
    (((n : ℂ) + 2) * B - A ^ 2) / (((n : ℂ) + 1) * A ^ 2) = a / u ^ (n + 2) := by
  intro F F1 F2 A B
  have hn2 : ((n : ℂ) + 2) ≠ 0 := by
    have : ((n + 2 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simpa using this
  have hn1 : ((n : ℂ) + 1) ≠ 0 := by
    have : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simpa using this
  have hun : u ^ n ≠ 0 := pow_ne_zero _ hu
  simp only [A, B, F, F1, F2]
  field_simp
  ring

/-- The anchor: `K / (A (1 - t)) = u`. -/
theorem anchor (u a : ℂ) (n : ℕ) (hu : u ≠ 0) (hf : u ^ (n + 2) - a ≠ 0) :
    ((n : ℂ) + 2) / ((((n : ℂ) + 2) * u ^ (n + 1) / (u ^ (n + 2) - a)) * (1 - a / u ^ (n + 2))) = u := by
  have hn2 : ((n : ℂ) + 2) ≠ 0 := by
    have : ((n + 2 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simpa using this
  have hun : u ^ (n + 2) ≠ 0 := pow_ne_zero _ hu
  have h1 : (1 - a / u ^ (n + 2)) = (u ^ (n + 2) - a) / u ^ (n + 2) := by
    field_simp
  rw [h1]
  field_simp
  ring

/-- The `K` roots of the model: `g + u ω` for every `ω` with `ω^K = a / u^K`. -/
theorem model_root (g a u ω : ℂ) (n : ℕ) (hu : u ≠ 0) (hω : ω ^ (n + 2) = a / u ^ (n + 2)) :
    (shifted g a n).eval (g + u * ω) = 0 := by
  have hun : u ^ (n + 2) ≠ 0 := pow_ne_zero _ hu
  rw [eval_shifted]
  have : g + u * ω - g = u * ω := by ring
  rw [this, mul_pow, hω]
  field_simp
  ring

end LeanMath.Papers.ClusterStep
