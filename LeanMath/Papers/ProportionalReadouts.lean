import LeanMath.Papers.Bracket
import LeanMath.Papers.Raw

noncomputable section
namespace LeanMath.Papers.ProportionalReadouts

/-- Two algebraic readouts; no claim of reconstructing a particular video. -/
def first (x s : ℝ) := x*s^2
def second (x s : ℝ) := x*s

theorem readout_dependence (x s : ℝ) : second x s ^ 2 = x * first x s := by
  unfold first second; ring

theorem repeated_ratios (x s : ℝ) (hx : 0 < x) (hs : 0 < s) :
    second x s / first x s = s⁻¹ ∧ x / second x s = s⁻¹ := by
  unfold first second
  constructor <;> field_simp

theorem ratio_product (x a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a * (b/a) * (x/b) = x := by field_simp

/-- Harmonic and arithmetic means of R,1,1. -/
def harmonic (R : ℝ) := 3*R/(2*R+1)
def arithmetic (R : ℝ) := (R+2)/3

theorem harmonic_pos (R : ℝ) (hR : 0 < R) : 0 < harmonic R := by
  unfold harmonic; positivity

theorem harmonic_le_root (q : ℝ) (hq : 0 < q) : harmonic (q^3) ≤ q := by
  unfold harmonic
  apply (div_le_iff₀ (by positivity : 0 < 2*q^3+1)).mpr
  have he : q*(2*q^3+1)-3*q^3 = q*(q-1)^2*(2*q+1) := by ring
  have hp : 0 ≤ q*(q-1)^2*(2*q+1) := by positivity
  nlinarith

theorem root_le_arithmetic (q : ℝ) (hq : 0 < q) : q ≤ arithmetic (q^3) := by
  unfold arithmetic
  have he : q^3+2-3*q=(q-1)^2*(q+2) := by ring
  have hp : 0 ≤ (q-1)^2*(q+2) := by positivity
  linarith

theorem certified_pair (x u r : ℝ) (hu : 0 < u) (hr : 0 < r) (hx : r^3=x) :
    u*harmonic (x/u^3) ≤ r ∧ r ≤ u*arithmetic (x/u^3) := by
  have h1 := harmonic_le_root (r/u) (div_pos hr hu)
  have h2 := root_le_arithmetic (r/u) (div_pos hr hu)
  rw [div_pow,hx] at h1 h2
  have he : u*(r/u)=r := by field_simp
  constructor
  · simpa [he] using mul_le_mul_of_nonneg_left h1 hu.le
  · simpa [he] using mul_le_mul_of_nonneg_left h2 hu.le

theorem lower_improvement (R : ℝ) (hR : 0 < R) :
    harmonic R - Bracket.lower 3 R = 3*R*(R-1)^2/((2*R+1)*(R+2)^2) := by
  change 3*R/(2*R+1) - R*(3/(R+3-1))^2 = _
  rw [show R+3-1=R+2 by ring]
  have h1 : 2*R+1 ≠ 0 := by positivity
  have h2 : R+2 ≠ 0 := by positivity
  field_simp
  ring

theorem upper_improvement (R : ℝ) (hR : 0 < R) :
    Bracket.upper 3 R - arithmetic R = (R-1)^2/(9*R) := by
  rw [Bracket.upper_formula]
  norm_num [arithmetic]
  field_simp
  ring

theorem nested_bounds (R : ℝ) (hR : 0 < R) :
    Bracket.lower 3 R ≤ harmonic R ∧ arithmetic R ≤ Bracket.upper 3 R := by
  constructor
  · have he := lower_improvement R hR
    have hp : 0 ≤ 3*R*(R-1)^2/((2*R+1)*(R+2)^2) := by positivity
    linarith
  · have he := upper_improvement R hR
    have hp : 0 ≤ (R-1)^2/(9*R) := by positivity
    linarith

/-- Exact multiplicative width identity: the old ratio is the square of the new. -/
theorem width_ratio_square (R : ℝ) (hR : 0 < R) :
    Bracket.upper 3 R / Bracket.lower 3 R = (arithmetic R / harmonic R)^2 := by
  rw [Bracket.upper_formula]
  norm_num [Bracket.lower,arithmetic,harmonic]
  field_simp
  ring

theorem logarithmic_width_half (R : ℝ) (hR : 0 < R) :
    Real.log (arithmetic R / harmonic R) =
      Real.log (Bracket.upper 3 R / Bracket.lower 3 R) / 2 := by
  rw [width_ratio_square R hR,Real.log_pow]
  norm_num

/-- The arithmetic fusion is exactly the usual Newton update for a cube root. -/
theorem arithmetic_is_newton (x u : ℝ) (hu : 0 < u) :
    u * arithmetic (x/u^3) = (2*u+x/u^2)/3 := by
  unfold arithmetic
  field_simp
  ring

/-- A root interval also certifies the second proportional mean, without another solve. -/
theorem squared_root_certificate (x r l h : ℝ) (hr : 0 < r) (hl : 0 < l)
    (hlo : l ≤ r) (hhi : r ≤ h) (hx : r^3=x) :
    x/h ≤ r^2 ∧ r^2 ≤ x/l := by
  have hh : 0 < h := lt_of_lt_of_le hr hhi
  constructor
  · apply (div_le_iff₀ hh).mpr
    have hp := mul_le_mul_of_nonneg_left hhi (sq_nonneg r)
    nlinarith [hx]
  · apply (le_div_iff₀ hl).mpr
    have hp := mul_le_mul_of_nonneg_left hlo (sq_nonneg r)
    nlinarith [hx]

theorem fixed_readouts (r : ℝ) (hr : 0 < r) :
    first (r^3) r⁻¹ = r ∧ second (r^3) r⁻¹ = r^2 := by
  unfold first second
  constructor <;> field_simp

end LeanMath.Papers.ProportionalReadouts

