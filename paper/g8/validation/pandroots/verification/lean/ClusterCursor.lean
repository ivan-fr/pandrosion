import Mathlib

/-! # The cursor of a cluster in multiprecision (pandroots 0.10.0)

The step of a cluster (`ClusterStep`) reads `A = F'/F` and `B = (F'² - F F'')/F²` for the polynomial `F`
deflated of the points outside the cluster.  Version 0.10.0 computes them from the two numbers that the
ball evaluation returns in multiprecision, `N = S/S'` and `β = S S''/S'²`, and from the sums over the
points outside, after a scaling by a power of two that brings every number to size one:

* `logder_of_parts`: `S'/S = 1/N` and `(S'² - S S'')/S² = (1 - β)/N²`;
* `cursor_forms`: the cursor `(K B - A²)/((K - 1) A²)` is `(K (B/A²) - 1)/(K - 1)`, the form in which
  it is computed (`K B/A²` is `1 + (K - 1) t`: the cursor is what is left of a number close to one);
* `cursor_scaled`, `anchor_scaled`: with `A` replaced by `s A` and `B` by `s² B` the cursor is the same
  and `u = K/(A (1 - t))` is `s` times the scaled quotient;
* `value_shrinks`: a point brought from the distance `r` of the centre of a shifted power to the
  distance `q r` sees `(w - g)^K` multiplied by `q^K`: the next evaluation needs `K log₂(1/q)` more bits.

Not formalised: the rounding of the fixed-point arithmetic (the cursor is used only above the rounding
level that the code estimates, and a wrong estimate would cost time, not correctness: the discs are
certified after the move), and the Rust code. -/

namespace LeanMath.Papers.ClusterCursor

variable {F : Type*} [Field F]

/-- The logarithmic derivative and its derivative from `N = S/S'` and `β = S S''/S'²`. -/
theorem logder_of_parts (S S1 S2 : F) (hS : S ≠ 0) (h1 : S1 ≠ 0) :
    S1 / S = 1 / (S / S1) ∧
      (S1 ^ 2 - S * S2) / S ^ 2 = (1 - S * S2 / S1 ^ 2) / (S / S1) ^ 2 := by
  constructor
  · field_simp
  · field_simp

/-- The two forms of the cursor. -/
theorem cursor_forms (A B k : F) (hA : A ≠ 0) (hk : k - 1 ≠ 0) :
    (k * B - A ^ 2) / ((k - 1) * A ^ 2) = (k * (B / A ^ 2) - 1) / (k - 1) := by
  field_simp

/-- The cursor does not see the scaling. -/
theorem cursor_scaled (A B k s : F) (hA : A ≠ 0) (hs : s ≠ 0) :
    (k * ((s ^ 2 * B) / (s * A) ^ 2) - 1) / (k - 1) = (k * (B / A ^ 2) - 1) / (k - 1) := by
  have h : (s ^ 2 * B) / (s * A) ^ 2 = B / A ^ 2 := by
    field_simp
  rw [h]

/-- The anchor from the scaled numbers. -/
theorem anchor_scaled (A k s t : F) (hA : A ≠ 0) (hs : s ≠ 0) (ht : 1 - t ≠ 0) :
    k / (A * (1 - t)) = s * (k / ((s * A) * (1 - t))) := by
  field_simp

/-- A shifted power at a point brought `q` times closer to its centre. -/
theorem value_shrinks (r q : F) (K : ℕ) : (q * r) ^ K = q ^ K * r ^ K := by
  rw [mul_pow]

end LeanMath.Papers.ClusterCursor
