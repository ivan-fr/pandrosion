import Mathlib

/-! # Fixed-width arithmetic of the ball evaluation (pandroots 0.7.0)

The inner loop of the multiprecision evaluation works on numbers in sign-magnitude form (module `limbs`).
It must return exactly the integers of the `BigInt` loop, whose shifts round towards minus infinity.
Three facts are used:

* `floor_neg_div`: for a negative number `-a`, `floor(-a / k) = -(a / k)`, minus one if the division of
  `a` is not exact (the code shifts the magnitude and adds one when a bit was dropped);
* `floor_shift_neg`: the same for `k = 2^s`, in terms of `Int.shiftRight`;
* `wrapping_sub_of_le`, `neg_wrapping_sub_of_lt`: the difference of two magnitudes below `M = 2^(64 n)`
  computed modulo `M`: it is `p - q` when `q ≤ p`; otherwise (a borrow comes out) its negation modulo `M`
  is `q - p`.

Not formalised: the Rust code itself (limbs, carries, the schoolbook product), which is tested against
`BigInt` on random inputs and on the whole comparison corpus. -/

namespace LeanMath.Papers.FixedWidth

/-- Floor division of a negative number from the division of its magnitude. -/
theorem floor_neg_div (a k : ℕ) (hk : 0 < k) :
    (-(a : ℤ)) / (k : ℤ) = -((a / k : ℕ) : ℤ) - (if a % k = 0 then 0 else 1) := by
  have hk' : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk
  have hdm : (k : ℤ) * ((a / k : ℕ) : ℤ) + ((a % k : ℕ) : ℤ) = (a : ℤ) := by
    exact_mod_cast Nat.div_add_mod a k
  have hlt : ((a % k : ℕ) : ℤ) < (k : ℤ) := by exact_mod_cast Nat.mod_lt a hk
  have hge : (0 : ℤ) ≤ ((a % k : ℕ) : ℤ) := by positivity
  split_ifs with h
  · have h0 : ((a % k : ℕ) : ℤ) = 0 := by exact_mod_cast h
    have : (-(a : ℤ)) = (k : ℤ) * (-((a / k : ℕ) : ℤ)) := by linarith
    rw [this, Int.mul_ediv_cancel_left _ (ne_of_gt hk')]
    ring
  · have hpos : (0 : ℤ) < ((a % k : ℕ) : ℤ) := by
      have : 0 < a % k := Nat.pos_of_ne_zero h
      exact_mod_cast this
    have key := (Int.ediv_emod_unique hk' (a := -(a : ℤ)) (q := -((a / k : ℕ) : ℤ) - 1)
      (r := (k : ℤ) - ((a % k : ℕ) : ℤ))).mpr ⟨by linarith, by linarith, by linarith⟩
    simpa using key.1

/-- The same for a shift: `(-a) >>> s` from `a >>> s`. -/
theorem floor_shift_neg (a s : ℕ) :
    (-(a : ℤ)) >>> s = -((a >>> s : ℕ) : ℤ) - (if a % 2 ^ s = 0 then 0 else 1) := by
  rw [Int.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  have := floor_neg_div a (2 ^ s) (by positivity)
  simpa using this

/-- No borrow: the difference modulo `M` is the difference. -/
theorem wrapping_sub_of_le (p q M : ℕ) (hp : p < M) (h : q ≤ p) : (p + M - q) % M = p - q := by
  have : p + M - q = (p - q) + M := by omega
  rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- A borrow: the difference modulo `M`, negated modulo `M`, is the opposite difference. -/
theorem neg_wrapping_sub_of_lt (p q M : ℕ) (hq : q < M) (h : p < q) :
    (M - (p + M - q) % M) % M = q - p := by
  have h1 : (p + M - q) % M = p + M - q := Nat.mod_eq_of_lt (by omega)
  rw [h1]
  have : M - (p + M - q) = q - p := by omega
  rw [this, Nat.mod_eq_of_lt (by omega)]

end LeanMath.Papers.FixedWidth
