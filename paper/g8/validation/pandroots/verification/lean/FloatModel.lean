import Mathlib

/-! # The floating-point model: rounding to nearest has a relative error of at most `2^-p`

The rounding bounds of pandroots (the bound of Horner's rule behind the certificate, `SparseHorner.comp_bound`)
start from one fact about double precision: the computed product, or sum, of two numbers is the exact one
times `1 + δ` with `|δ| ≤ u = 2^-53`, as long as the result is not in the subnormal range.  This file proves
that fact from a definition of the format, for any precision.

* `Fmt p emin`: the numbers `m 2^e` with `m`, `e` integers, `|m| ≤ 2^p` and `e ≥ emin`.  For `p ≥ 1` these
  are the numbers with a significand of `p` bits and an exponent at least `emin` (`m = ± 2^p` at the
  exponent `e` is `± 2^(p-1)` at the exponent `e + 1`); there is no largest exponent, that is, no overflow.
  Binary64 is `p = 53`, `emin = -1074`.
* `Nearest p emin x y`: `y` is a number of the format nearest to `x` (any rule for ties).
* `exists_close`: a number of the format within half a unit of the last place, `2^e / 2`, of any `x` with
  `|x| ≤ 2^e 2^p`;
* `nearest_error`: so the rounding to nearest is within `2^e / 2`;
* `nearest_rel`: and within `2^-p |x|` when `2^e 2^p ≤ 2 |x|`, written `|x - y| 2^p ≤ |x|`;
* `exists_binade`, `nearest_normal`: every `x` with `|x| ≥ 2^(emin + p - 1)` (the normal range: `2^-1022`
  for binary64) has such an `e`, hence `|x - y| 2^p ≤ |x|`;
* `nearest_small`: below, the error is at most `2^emin / 2` (half the smallest positive number);
* `binary64`: the statement for doubles.
* `cmul_error`: the product of two complex numbers as the program computes it, four real products, one
  difference and one sum, each within the relative error `u`: the result is within `√2 (2 u + u²) |z| |w|`
  of the exact product (stated with squares).

Not formalised: that the arithmetic of the machine is this rounding (IEEE 754, which Rust's `f64` follows
on the supported targets), overflow, and the Rust code. -/

namespace LeanMath.Papers.FloatModel

/-- The triangle inequality, from the cases of the absolute values. -/
theorem abs_add_le' (a b : ℝ) : |a + b| ≤ |a| + |b| := by
  rcases abs_cases (a + b) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases abs_cases a with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    rcases abs_cases b with ⟨h5, h6⟩ | ⟨h5, h6⟩ <;> linarith

theorem abs_sub_le' (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rcases abs_cases (a - b) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases abs_cases a with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    rcases abs_cases b with ⟨h5, h6⟩ | ⟨h5, h6⟩ <;> linarith

/-- The numbers `m 2^e`, `|m| ≤ 2^p`, `e ≥ emin`. -/
def Fmt (p : ℕ) (emin : ℤ) : Set ℝ :=
  {x | ∃ m e : ℤ, |m| ≤ 2 ^ p ∧ emin ≤ e ∧ x = (m : ℝ) * (2 : ℝ) ^ e}

/-- `y` is a number of the format nearest to `x`. -/
def Nearest (p : ℕ) (emin : ℤ) (x y : ℝ) : Prop :=
  y ∈ Fmt p emin ∧ ∀ z ∈ Fmt p emin, |x - y| ≤ |x - z|

/-- A number of the format within `2^e / 2` of `x`, when `|x| ≤ 2^e 2^p`. -/
theorem exists_close (p : ℕ) (emin e : ℤ) (x : ℝ) (he : emin ≤ e) (hx : |x| ≤ (2 : ℝ) ^ e * 2 ^ p) :
    ∃ z ∈ Fmt p emin, |x - z| ≤ (2 : ℝ) ^ e / 2 := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ e := by positivity
  obtain ⟨t, ht⟩ : ∃ t : ℝ, x = t * (2 : ℝ) ^ e := ⟨x / (2 : ℝ) ^ e, by field_simp⟩
  subst ht
  have habs : |t * (2 : ℝ) ^ e| = |t| * (2 : ℝ) ^ e := by rw [abs_mul, abs_of_pos hpos]
  rw [habs] at hx
  have htp : |t| ≤ 2 ^ p := le_of_mul_le_mul_right (by linarith) hpos
  have h1 : |t - (round t : ℝ)| ≤ 1 / 2 := abs_sub_round t
  have hn : |((round t : ℤ) : ℝ)| ≤ 2 ^ p + 1 / 2 := by
    have e1 : ((round t : ℤ) : ℝ) = t - (t - (round t : ℝ)) := by ring
    calc |((round t : ℤ) : ℝ)| = |t - (t - (round t : ℝ))| := by rw [← e1]
      _ ≤ |t| + |t - (round t : ℝ)| := abs_sub_le' _ _
      _ ≤ 2 ^ p + 1 / 2 := by linarith
  have hmant : |round t| ≤ 2 ^ p := by
    by_contra hc
    push_neg at hc
    have h2 : (2 : ℤ) ^ p + 1 ≤ |round t| := hc
    have h3 : ((2 : ℝ) ^ p + 1) ≤ |((round t : ℤ) : ℝ)| := by exact_mod_cast h2
    linarith
  refine ⟨(round t : ℝ) * (2 : ℝ) ^ e, ⟨round t, e, hmant, he, rfl⟩, ?_⟩
  have e2 : t * (2 : ℝ) ^ e - (round t : ℝ) * (2 : ℝ) ^ e = (t - (round t : ℝ)) * (2 : ℝ) ^ e := by ring
  rw [e2, abs_mul, abs_of_pos hpos]
  have := mul_le_mul_of_nonneg_right h1 (le_of_lt hpos)
  linarith

/-- The rounding to nearest is within half a unit of the last place. -/
theorem nearest_error (p : ℕ) (emin e : ℤ) (x y : ℝ) (he : emin ≤ e) (hx : |x| ≤ (2 : ℝ) ^ e * 2 ^ p)
    (h : Nearest p emin x y) : |x - y| ≤ (2 : ℝ) ^ e / 2 := by
  obtain ⟨z, hz, hd⟩ := exists_close p emin e x he hx
  exact le_trans (h.2 z hz) hd

/-- The relative error of the rounding to nearest is at most `2^-p`: `|x - y| 2^p ≤ |x|`. -/
theorem nearest_rel (p : ℕ) (emin e : ℤ) (x y : ℝ) (he : emin ≤ e)
    (hlo : (2 : ℝ) ^ e * 2 ^ p ≤ 2 * |x|) (hhi : |x| ≤ (2 : ℝ) ^ e * 2 ^ p) (h : Nearest p emin x y) :
    |x - y| * 2 ^ p ≤ |x| := by
  have h1 := nearest_error p emin e x y he hhi h
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt hp)
  linarith

/-- Every number of the normal range lies in a binade of the format. -/
theorem exists_binade (p : ℕ) (emin : ℤ) (x : ℝ) (hx : (2 : ℝ) ^ emin * 2 ^ p ≤ 2 * |x|) :
    ∃ e : ℤ, emin ≤ e ∧ (2 : ℝ) ^ e * 2 ^ p ≤ 2 * |x| ∧ |x| ≤ (2 : ℝ) ^ e * 2 ^ p := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hmin : (0 : ℝ) < (2 : ℝ) ^ emin := by positivity
  have hxpos : 0 < |x| := by nlinarith
  -- r = 2 |x| / 2^p lies between 2^L and 2^(L+1)
  have hr : (0 : ℝ) < 2 * |x| / 2 ^ p := by positivity
  have hlow := Int.zpow_log_le_self (b := 2) (by norm_num) hr
  have hupp := Int.lt_zpow_succ_log_self (b := 2) (by norm_num) (2 * |x| / 2 ^ p)
  set L := Int.log 2 (2 * |x| / 2 ^ p) with hL
  have hlow' : (2 : ℝ) ^ L ≤ 2 * |x| / 2 ^ p := by simpa using hlow
  have hupp' : 2 * |x| / 2 ^ p < (2 : ℝ) ^ (L + 1) := by simpa using hupp
  have hsucc : (2 : ℝ) ^ (L + 1) = (2 : ℝ) ^ L * 2 := by
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
  have m1 : (2 : ℝ) ^ L * 2 ^ p ≤ 2 * |x| := by
    have := mul_le_mul_of_nonneg_right hlow' (le_of_lt hp)
    rwa [div_mul_cancel₀ _ (ne_of_gt hp)] at this
  have m2 : 2 * |x| < (2 : ℝ) ^ L * 2 * 2 ^ p := by
    have := mul_lt_mul_of_pos_right hupp' hp
    rw [div_mul_cancel₀ _ (ne_of_gt hp), hsucc] at this
    exact this
  refine ⟨L, ?_, m1, by nlinarith⟩
  -- 2^emin ≤ r < 2^(L+1), so emin ≤ L
  by_contra hc
  push_neg at hc
  have hle : L + 1 ≤ emin := hc
  have hmono : (2 : ℝ) ^ (L + 1) ≤ (2 : ℝ) ^ emin := zpow_le_zpow_right₀ (by norm_num) hle
  rw [hsucc] at hmono
  have : (2 : ℝ) ^ L * 2 * 2 ^ p ≤ (2 : ℝ) ^ emin * 2 ^ p := mul_le_mul_of_nonneg_right hmono (le_of_lt hp)
  linarith

/-- In the normal range, `|x| ≥ 2^(emin + p - 1)`, the relative error is at most `2^-p`. -/
theorem nearest_normal (p : ℕ) (emin : ℤ) (x y : ℝ) (hx : (2 : ℝ) ^ emin * 2 ^ p ≤ 2 * |x|)
    (h : Nearest p emin x y) : |x - y| * 2 ^ p ≤ |x| := by
  obtain ⟨e, he, hlo, hhi⟩ := exists_binade p emin x hx
  exact nearest_rel p emin e x y he hlo hhi h

/-- Below the normal range the error is at most half the smallest positive number. -/
theorem nearest_small (p : ℕ) (emin : ℤ) (x y : ℝ) (hx : |x| ≤ (2 : ℝ) ^ emin * 2 ^ p)
    (h : Nearest p emin x y) : |x - y| ≤ (2 : ℝ) ^ emin / 2 :=
  nearest_error p emin emin x y (le_refl _) hx h

/-- Binary64: a result rounded to nearest that is at least `2^-1022` in modulus (here `2^-1074 2^53 ≤ 2 |x|`)
is within `2^-53 |x|` of the exact one. -/
theorem binary64 (x y : ℝ) (hx : (2 : ℝ) ^ (-1074 : ℤ) * 2 ^ 53 ≤ 2 * |x|)
    (h : Nearest 53 (-1074) x y) : |x - y| * 2 ^ 53 ≤ |x| :=
  nearest_normal 53 (-1074) x y hx h

/-- One coordinate of the complex product: two products and their difference, each within `u`. -/
theorem coord_error (u : ℝ) (hu : 0 ≤ u) (P Q p1 p2 r : ℝ)
    (h1 : |p1 - P| ≤ u * |P|) (h2 : |p2 - Q| ≤ u * |Q|) (hr : |r - (p1 - p2)| ≤ u * |p1 - p2|) :
    |r - (P - Q)| ≤ (2 * u + u ^ 2) * (|P| + |Q|) := by
  have a1 : |p1| ≤ |p1 - P| + |P| := by
    have := abs_add_le' (p1 - P) P
    simpa using this
  have a2 : |p2| ≤ |p2 - Q| + |Q| := by
    have := abs_add_le' (p2 - Q) Q
    simpa using this
  have a3 : |p1 - p2| ≤ |p1| + |p2| := abs_sub_le' p1 p2
  have a4 : |p1 - p2| ≤ (1 + u) * (|P| + |Q|) := by nlinarith
  have a5 : u * |p1 - p2| ≤ u * ((1 + u) * (|P| + |Q|)) := mul_le_mul_of_nonneg_left a4 hu
  have e : r - (P - Q) = (r - (p1 - p2)) + ((p1 - P) - (p2 - Q)) := by ring
  have a6 : |r - (P - Q)| ≤ |r - (p1 - p2)| + (|p1 - P| + |p2 - Q|) := by
    rw [e]
    exact le_trans (abs_add_le' _ _) (by linarith [abs_sub_le' (p1 - P) (p2 - Q)])
  nlinarith

/-- A square from a bound of the absolute value. -/
theorem sq_le_of_abs_le (v B : ℝ) (h : |v| ≤ B) : v ^ 2 ≤ B ^ 2 := by
  have hB : 0 ≤ B := le_trans (abs_nonneg v) h
  have h1 : 0 ≤ (B - |v|) * (B + |v|) := mul_nonneg (sub_nonneg.mpr h) (add_nonneg hB (abs_nonneg v))
  have h2 : |v| ^ 2 = v ^ 2 := sq_abs v
  nlinarith

/-- The complex product `(a + i b)(c + i d)` computed with four products, a difference and a sum, each
within the relative error `u`: `|computed - exact|² ≤ 2 (2 u + u²)² |z|² |w|²`. -/
theorem cmul_error (u : ℝ) (hu : 0 ≤ u) (a b c d p1 p2 p3 p4 r i : ℝ)
    (h1 : |p1 - a * c| ≤ u * |a * c|) (h2 : |p2 - b * d| ≤ u * |b * d|)
    (h3 : |p3 - a * d| ≤ u * |a * d|) (h4 : |p4 - b * c| ≤ u * |b * c|)
    (hr : |r - (p1 - p2)| ≤ u * |p1 - p2|) (hi : |i - (p3 + p4)| ≤ u * |p3 + p4|) :
    (r - (a * c - b * d)) ^ 2 + (i - (a * d + b * c)) ^ 2
      ≤ 2 * (2 * u + u ^ 2) ^ 2 * ((a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2)) := by
  have er := coord_error u hu (a * c) (b * d) p1 p2 r h1 h2 hr
  -- the sum is the difference with the opposite of the second product
  have h4' : |(-p4) - (-(b * c))| ≤ u * |-(b * c)| := by
    have e : (-p4) - (-(b * c)) = -(p4 - b * c) := by ring
    rw [e, abs_neg, abs_neg]
    exact h4
  have hi' : |i - (p3 - (-p4))| ≤ u * |p3 - (-p4)| := by
    have e : p3 - (-p4) = p3 + p4 := by ring
    rw [e]
    exact hi
  have ei := coord_error u hu (a * d) (-(b * c)) p3 (-p4) i h3 h4' hi'
  rw [abs_neg] at ei
  have ei' : |i - (a * d + b * c)| ≤ (2 * u + u ^ 2) * (|a * d| + |b * c|) := by
    have e : i - (a * d + b * c) = i - (a * d - -(b * c)) := by ring
    rw [e]
    exact ei
  have sr := sq_le_of_abs_le _ _ er
  have si := sq_le_of_abs_le _ _ ei'
  have x1 : (|a * c| + |b * d|) ^ 2 ≤ 2 * ((a * c) ^ 2 + (b * d) ^ 2) := by
    nlinarith [sq_nonneg (|a * c| - |b * d|), sq_abs (a * c), sq_abs (b * d)]
  have x2 : (|a * d| + |b * c|) ^ 2 ≤ 2 * ((a * d) ^ 2 + (b * c) ^ 2) := by
    nlinarith [sq_nonneg (|a * d| - |b * c|), sq_abs (a * d), sq_abs (b * c)]
  have hK : 0 ≤ (2 * u + u ^ 2) ^ 2 := sq_nonneg _
  have y1 := mul_le_mul_of_nonneg_left x1 hK
  have y2 := mul_le_mul_of_nonneg_left x2 hK
  have e1 : ((2 * u + u ^ 2) * (|a * c| + |b * d|)) ^ 2 = (2 * u + u ^ 2) ^ 2 * (|a * c| + |b * d|) ^ 2 := by ring
  have e2 : ((2 * u + u ^ 2) * (|a * d| + |b * c|)) ^ 2 = (2 * u + u ^ 2) ^ 2 * (|a * d| + |b * c|) ^ 2 := by ring
  have e3 : 2 * (2 * u + u ^ 2) ^ 2 * ((a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2))
      = (2 * u + u ^ 2) ^ 2 * (2 * ((a * c) ^ 2 + (b * d) ^ 2))
        + (2 * u + u ^ 2) ^ 2 * (2 * ((a * d) ^ 2 + (b * c) ^ 2)) := by ring
  rw [e3]
  linarith

end LeanMath.Papers.FloatModel
