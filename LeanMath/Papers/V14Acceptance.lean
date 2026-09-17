import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/- The checker consumes IEEE positive-finite bit patterns. All arithmetic
   below is exact Nat/Int/Rat arithmetic; the C++ proposal is untrusted. -/
namespace LeanMath.Papers.V14Acceptance

def decode (fractionBits bias : Nat) (b : Nat) : ℚ :=
  let frac := b % 2^fractionBits
  let expo := b / 2^fractionBits
  if expo = 0 then (frac : ℚ) / (2 : ℚ)^(bias + fractionBits - 1)
  else (2^fractionBits + frac : ℚ) * (2 : ℚ)^((expo : ℤ) - bias - fractionBits)

def valid (fractionBits exponentBits : Nat) (b : Nat) : Bool :=
  decide (0 < b ∧ b < (2^exponentBits-1)*2^fractionBits)

def accepts (fractionBits exponentBits bias p xb ub : Nat) : Bool :=
  let x := decode fractionBits bias xb
  let u := decode fractionBits bias ub
  let tol : ℚ := 8 / 2^fractionBits
  valid fractionBits exponentBits xb && valid fractionBits exponentBits ub &&
  decide (0 < p ∧ 0 < x ∧ 0 < u ∧ 0 < tol ∧ tol < 1 ∧
    (u / (1+tol))^p ≤ x ∧ x ≤ (u / (1-tol))^p)

/-- Exact rational power checks imply a real relative-error contract. -/
theorem bracket_sound (x u t : ℚ) (p : ℕ) (r : ℝ)
    (hp : 0 < p) (hu : 0 < u) (ht : 0 < t) (ht1 : t < 1)
    (hr : 0 < r) (hroot : r^p = (x : ℝ))
    (hlo : (u / (1+t))^p ≤ x) (hhi : x ≤ (u / (1-t))^p) :
    |(u : ℝ) / r - 1| ≤ (t : ℝ) := by
  have hu' : (0 : ℝ) < u := by exact_mod_cast hu
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have ht1' : (t : ℝ) < 1 := by exact_mod_cast ht1
  have hlo' : ((u : ℝ) / (1+(t : ℝ)))^p ≤ r^p := by
    rw [hroot]; exact_mod_cast hlo
  have hhi' : r^p ≤ ((u : ℝ) / (1-(t : ℝ)))^p := by
    rw [hroot]; exact_mod_cast hhi
  have hl : (u : ℝ) / (1+(t : ℝ)) ≤ r := by
    by_contra hn
    have : r^p < ((u : ℝ) / (1+(t : ℝ)))^p :=
      pow_lt_pow_left₀ (lt_of_not_ge hn) (le_of_lt hr) (Nat.ne_of_gt hp)
    linarith
  have hh : r ≤ (u : ℝ) / (1-(t : ℝ)) := by
    by_contra hn
    have hnon : (0 : ℝ) ≤ (u : ℝ) / (1-(t : ℝ)) := by positivity
    have : ((u : ℝ) / (1-(t : ℝ)))^p < r^p :=
      pow_lt_pow_left₀ (lt_of_not_ge hn) hnon (Nat.ne_of_gt hp)
    linarith
  have hlm := (div_le_iff₀ (show (0 : ℝ) < 1+(t : ℝ) by linarith)).mp hl
  have hhm := (le_div_iff₀ (show (0 : ℝ) < 1-(t : ℝ) by linarith)).mp hh
  apply abs_le.mpr
  constructor
  · have : (1-(t : ℝ)) ≤ (u : ℝ)/r := (le_div_iff₀ hr).mpr (by nlinarith)
    linarith
  · have : (u : ℝ)/r ≤ 1+(t : ℝ) := (div_le_iff₀ hr).mpr (by nlinarith)
    linarith

/-- Applies to every accepted pair of finite float bit patterns, regardless
    of how the candidate was computed. -/
theorem accepts_sound (f e bias p xb ub : Nat) (r : ℝ)
    (h : accepts f e bias p xb ub = true)
    (hr : 0 < r) (hroot : r^p = (decode f bias xb : ℝ)) :
    |(decode f bias ub : ℝ) / r - 1| ≤ ((8 / 2^f : ℚ) : ℝ) := by
  simp only [accepts, Bool.and_eq_true, decide_eq_true_eq] at h
  exact bracket_sound _ _ _ _ _ h.2.1 h.2.2.2.1 h.2.2.2.2.1
    h.2.2.2.2.2.1 hr hroot h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2

/-- Only accepted bit patterns can inhabit this output type. -/
abbrev Certified (f e bias p xb : Nat) :=
  { ub : Nat // accepts f e bias p xb ub = true }

/-- Executable acceptance gate around an arbitrary floating-point proposal. -/
def certify (f e bias p xb ub : Nat) : Option (Certified f e bias p xb) :=
  if h : accepts f e bias p xb ub = true then some ⟨ub, h⟩ else none

/-- Every value released through the certified interface has the contract. -/
theorem certified_sound (f e bias p xb : Nat) (v : Certified f e bias p xb)
    (r : ℝ) (hr : 0 < r) (hroot : r^p = (decode f bias xb : ℝ)) :
    |(decode f bias v.val : ℝ) / r - 1| ≤ ((8 / 2^f : ℚ) : ℝ) :=
  accepts_sound f e bias p xb v.val r v.property hr hroot

theorem decode32_one : decode 23 127 1065353216 = 1 := by norm_num [decode]
theorem decode64_one : decode 52 1023 4607182418800017408 = 1 := by norm_num [decode]
theorem decode32_subnormal : decode 23 127 1 = (1 : ℚ) / 2^149 := by norm_num [decode]
theorem decode64_subnormal : decode 52 1023 1 = (1 : ℚ) / 2^1074 := by norm_num [decode]


/-- Proposition 14.1. Endpoints may be decoded scaled integer intervals.
Only the enclosure hypotheses, not a computed residual, authorize acceptance. -/
theorem interval_acceptance (p : ℕ) (x u t r Lu Uu Lminus Uminus Lplus Uplus : ℝ)
    (hp : 0 < p) (hu : 0 < u) (hr : 0 < r) (ht : 0 < t) (ht1 : t < 1)
    (hroot : r^p = x)
    (hulo : Lu ≤ u^p) (huhi : u^p ≤ Uu)
    (hminus : x*(1-t)^p ≤ Uminus) (hplus : Lplus ≤ x*(1+t)^p)
    (hacceptlo : Uminus ≤ Lu) (haccepthi : Uu ≤ Lplus) :
    |u/r-1| ≤ t := by
  have hlo : (r*(1-t))^p ≤ u^p := by
    rw [mul_pow,hroot]
    exact hminus.trans (hacceptlo.trans hulo)
  have hhi : u^p ≤ (r*(1+t))^p := by
    rw [mul_pow,hroot]
    exact huhi.trans (haccepthi.trans hplus)
  have hl : r*(1-t) ≤ u := by
    by_contra hn
    have := pow_lt_pow_left₀ (lt_of_not_ge hn) hu.le (Nat.ne_of_gt hp)
    linarith
  have hh : u ≤ r*(1+t) := by
    by_contra hn
    have htpos : 0 ≤ r*(1+t) := by positivity
    have := pow_lt_pow_left₀ (lt_of_not_ge hn) htpos (Nat.ne_of_gt hp)
    linarith
  apply abs_le.mpr
  constructor
  · have h : 1-t ≤ u/r := (le_div_iff₀ hr).mpr (by nlinarith [hl])
    linarith
  · have h : u/r ≤ 1+t := (div_le_iff₀ hr).mpr (by nlinarith [hh])
    linarith

/-- Containment is preserved by positive interval multiplication. -/
theorem positive_interval_mul (a b la ua lb ub : ℚ)
    (hla : 0 ≤ la) (hlb : 0 ≤ lb)
    (ha : la ≤ a ∧ a ≤ ua) (hb : lb ≤ b ∧ b ≤ ub) :
    la*lb ≤ a*b ∧ a*b ≤ ua*ub := by
  have ha0 := hla.trans ha.1
  have hb0 := hlb.trans hb.1
  exact ⟨mul_le_mul ha.1 hb.1 hlb ha0,
    mul_le_mul ha.2 hb.2 hb0 (ha0.trans ha.2)⟩

/-- Outward rounding cannot invalidate an already established interval. -/
theorem outward_enclosure (a l u l' u' : ℚ)
    (h : l ≤ a ∧ a ≤ u) (hl : l' ≤ l) (hu : u ≤ u') :
    l' ≤ a ∧ a ≤ u' := ⟨hl.trans h.1, h.2.trans hu⟩

/-- Integer floor/ceiling on any positive grid provides outward enclosure. -/
theorem floor_ceil_enclosure (a scale : ℚ) (hscale : 0 < scale) :
    (⌊a*scale⌋ : ℚ)/scale ≤ a ∧ a ≤ (⌈a*scale⌉ : ℚ)/scale := by
  constructor
  · exact (div_le_iff₀ hscale).mpr (Int.floor_le (a*scale))
  · exact (le_div_iff₀ hscale).mpr (Int.le_ceil (a*scale))

end LeanMath.Papers.V14Acceptance
