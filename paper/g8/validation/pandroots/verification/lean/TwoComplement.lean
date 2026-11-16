import Mathlib

/-! # Horner's rule on long integers in two's complement (pandroots 0.14.0)

The evaluation in fixed point computes, at each step, `floor((a x_a + b x_b) 2^sh / 2^k) + c` on integers
of a few hundred bits, `x_a` and `x_b` being the 53 bits of the two coordinates of a double precision point
and `2^sh` their common power of two.  Since version 0.14.0 this is done in two's complement and, when the
shift is below one limb, in one pass: each limb of the product completes a limb of the quotient.

* `shift_floor`: the shift that fills with the sign bit is the quotient towards minus infinity, the
  rounding that the error bound of the evaluation assumes (`BigInt >> k`);
* `scaled_shift`: the power of two of the multipliers comes off the shift,
  `floor(T 2^sh / 2^k) = floor(T / 2^(k - sh))` for `sh ≤ k`;
* `limb_of_shift`, `limb_of_shift_pow`: the limb of the quotient from two consecutive limbs of the product:
  with `T = lo + 2^64 hi`, `lo < 2^64` and `s ≤ 64`,
  `floor(T / 2^s) mod 2^64 = floor(lo / 2^s) + (hi mod 2^s) 2^(64 - s)`
  (the program writes `(lo >> s) | (hi << (64 - s))`).

Not formalised: the Rust code (the signed carry of the products, the detection of a result that does not
fit), which is tested against the `BigInt` loop on random inputs and gives the same discs on the corpora. -/

namespace LeanMath.Papers.TwoComplement

/-- The arithmetic shift is the floor of the quotient. -/
theorem shift_floor (t : ℤ) (k : ℕ) : t >>> k = t / 2 ^ k :=
  Int.shiftRight_eq_div_pow t k

/-- The common power of two of the multipliers comes off the shift. -/
theorem scaled_shift (T : ℤ) (sh k : ℕ) (h : sh ≤ k) : T * 2 ^ sh / 2 ^ k = T / 2 ^ (k - sh) := by
  have e : (2 : ℤ) ^ k = 2 ^ (k - sh) * 2 ^ sh := by
    rw [← pow_add, Nat.sub_add_cancel h]
  have hpos : (0 : ℤ) < 2 ^ sh := by positivity
  rw [e]
  exact Int.mul_ediv_mul_of_pos_left T _ hpos

/-- The step of the program: product, shift and sum, with the shift reduced. -/
theorem step_value (T c : ℤ) (sh k : ℕ) (h : sh ≤ k) :
    (T * 2 ^ sh) >>> k + c = T / 2 ^ (k - sh) + c := by
  rw [shift_floor, scaled_shift T sh k h]

/-- A limb of a quotient: for `A < r`, `(A + r h) mod (r m) = A + r (h mod m)`. -/
theorem limb_of_shift (A r m h : ℕ) (hA : A < r) (hm : 0 < m) :
    (A + r * h) % (r * m) = A + r * (h % m) := by
  have h1 : A + r * h = (A + r * (h % m)) + (r * m) * (h / m) := by
    calc A + r * h = A + r * (m * (h / m) + h % m) := by rw [Nat.div_add_mod]
      _ = (A + r * (h % m)) + (r * m) * (h / m) := by ring
  rw [h1, Nat.add_mul_mod_self_left]
  apply Nat.mod_eq_of_lt
  have h2 : h % m + 1 ≤ m := Nat.mod_lt h hm
  have h3 : r * (h % m) + r ≤ r * m := by
    calc r * (h % m) + r = r * (h % m + 1) := by ring
      _ ≤ r * m := Nat.mul_le_mul_left r h2
  linarith

/-- With limbs of 64 bits: the limb of `floor(T / 2^s)` from two consecutive limbs `lo`, `hi` of `T`. -/
theorem limb_of_shift_pow (lo hi s : ℕ) (hs : s ≤ 64) (hlo : lo < 2 ^ 64) :
    (lo + 2 ^ 64 * hi) / 2 ^ s % 2 ^ 64 = lo / 2 ^ s + 2 ^ (64 - s) * (hi % 2 ^ s) := by
  have e : 2 ^ 64 = 2 ^ s * 2 ^ (64 - s) := by
    rw [← pow_add, Nat.add_sub_of_le hs]
  have hpos : 0 < 2 ^ s := by positivity
  have q : (lo + 2 ^ 64 * hi) / 2 ^ s = lo / 2 ^ s + 2 ^ (64 - s) * hi := by
    have e2 : lo + 2 ^ 64 * hi = lo + 2 ^ s * (2 ^ (64 - s) * hi) := by rw [e]; ring
    rw [e2, Nat.add_mul_div_left _ _ hpos]
  have hA : lo / 2 ^ s < 2 ^ (64 - s) := by
    rw [Nat.div_lt_iff_lt_mul hpos]
    calc lo < 2 ^ 64 := hlo
      _ = 2 ^ (64 - s) * 2 ^ s := by rw [e]; ring
  have e3 : 2 ^ 64 = 2 ^ (64 - s) * 2 ^ s := by rw [e]; ring
  rw [q, e3]
  exact limb_of_shift (lo / 2 ^ s) (2 ^ (64 - s)) (2 ^ s) hi hA hpos

end LeanMath.Papers.TwoComplement
