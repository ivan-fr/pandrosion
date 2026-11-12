import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic

/-! Algebraic results of Reciprocal Geometry, Sections 6 and Appendix A.
The residual sign below is one ingredient of the comparison proof; it is not
presented as a proof of global convergence or of exact seventh local order. -/

noncomputable section
namespace LeanMath.Papers.Cayley

def chi (R : ℝ) : ℝ := (R - 1) / (R + 1)
def unchi (y : ℝ) : ℝ := (1 + y) / (1 - y)
def a₁ (p : ℝ) : ℝ := 1 / p
def a₃ (p : ℝ) : ℝ := (p ^ 2 - 1) / (3 * p ^ 3)
def a₅ (p : ℝ) : ℝ := (p ^ 2 - 1) * (3 * p ^ 2 - 2) / (15 * p ^ 5)
def P₁ (p y : ℝ) : ℝ := a₁ p * y
def P₃ (p y : ℝ) : ℝ := a₁ p * y + a₃ p * y ^ 3
def P₅ (p y : ℝ) : ℝ := a₁ p * y + a₃ p * y ^ 3 + a₅ p * y ^ 5
def C₃ (p R : ℝ) : ℝ := unchi (P₁ p (chi R))
def C₅ (p R : ℝ) : ℝ := unchi (P₃ p (chi R))
def C₇ (p R : ℝ) : ℝ := unchi (P₅ p (chi R))

theorem chi_inv (R : ℝ) (hR : 0 < R) : chi R⁻¹ = -chi R := by
  unfold chi
  field_simp
  <;> ring

theorem chi_mem (R : ℝ) (hR : 0 < R) : chi R ∈ Set.Ioo (-1) 1 := by
  have hd : 0 < R + 1 := by linarith
  constructor
  · apply (lt_div_iff₀ hd).mpr
    linarith
  · apply (div_lt_iff₀ hd).mpr
    linarith

theorem unchi_neg (y : ℝ) : unchi (-y) = (unchi y)⁻¹ := by
  simp [unchi, inv_div, sub_eq_add_neg, add_comm]

theorem unchi_chi (R : ℝ) (hR : 0 < R) : unchi (chi R) = R := by
  unfold unchi chi
  field_simp
  <;> ring

theorem P₁_odd (p y : ℝ) : P₁ p (-y) = -P₁ p y := by unfold P₁; ring
theorem P₃_odd (p y : ℝ) : P₃ p (-y) = -P₃ p y := by unfold P₃; ring
theorem P₅_odd (p y : ℝ) : P₅ p (-y) = -P₅ p y := by unfold P₅; ring

theorem C₃_reciprocal (p R : ℝ) (hR : 0 < R) : C₃ p R⁻¹ = (C₃ p R)⁻¹ := by
  simp only [C₃, chi_inv R hR, P₁_odd, unchi_neg]
theorem C₅_reciprocal (p R : ℝ) (hR : 0 < R) : C₅ p R⁻¹ = (C₅ p R)⁻¹ := by
  simp only [C₅, chi_inv R hR, P₃_odd, unchi_neg]
theorem C₇_reciprocal (p R : ℝ) (hR : 0 < R) : C₇ p R⁻¹ = (C₇ p R)⁻¹ := by
  simp only [C₇, chi_inv R hR, P₅_odd, unchi_neg]

theorem halley_formula (p R : ℝ) (hp : 1 < p) (hR : 0 < R) :
    C₃ p R = ((p + 1) * R + (p - 1)) / ((p - 1) * R + (p + 1)) := by
  have hp0 : p ≠ 0 := by linarith
  have hr1 : R + 1 ≠ 0 := by linarith
  have hpm : 0 < p - 1 := by linarith
  have hpp : 0 < p + 1 := by linarith
  have hd : (p - 1) * R + (p + 1) ≠ 0 := by positivity
  have he : 1 - 1/p*((R-1)/(R+1)) = ((p-1)*R+(p+1))/(p*(R+1)) := by
    field_simp
    <;> ring
  unfold C₃ unchi P₁ a₁ chi
  rw [he, div_div_eq_mul_div]
  field_simp [hd]
  <;> ring

theorem coefficients_pos (p : ℝ) (hp : 1 < p) :
    0 < a₁ p ∧ 0 < a₃ p ∧ 0 < a₅ p := by
  have hp0 : 0 < p := by linarith
  have hsq : 1 < p ^ 2 := by nlinarith
  have hsq2 : 0 < 3*p^2-2 := by nlinarith
  unfold a₁ a₃ a₅
  exact ⟨by positivity, by positivity, by positivity⟩

theorem truncations_ordered (p y : ℝ) (hp : 1 < p) (hy : 0 < y) :
    0 < P₁ p y ∧ P₁ p y < P₃ p y ∧ P₃ p y < P₅ p y := by
  obtain ⟨h1,h3,h5⟩ := coefficients_pos p hp
  unfold P₁ P₃ P₅
  exact ⟨mul_pos h1 hy, lt_add_of_pos_right _ (by positivity),
    lt_add_of_pos_right _ (by positivity)⟩

def B (p z : ℝ) : ℝ :=
  -225 * p ^ 8 + 265 * p ^ 6 - 85 * p ^ 4 +
  10 * p ^ 2 * (p ^ 2 - 1) * (3 * p ^ 2 - 2) * z +
  (p ^ 2 - 1) * (3 * p ^ 2 - 2) ^ 2 * z ^ 2
def A (p : ℝ) : ℝ := 15 * p ^ 4 - 8 * p ^ 3 - 8 * p ^ 2 + 2 * p + 2
def D (p : ℝ) : ℝ := 15 * p ^ 4 + 8 * p ^ 3 - 8 * p ^ 2 - 2 * p + 2

theorem factor_at_one (p : ℝ) : B p 1 = -(A p * D p) := by
  unfold B A D
  ring

theorem factors_pos (p : ℝ) (hp : 1 < p) : 0 < A p ∧ 0 < D p := by
  have ht : 0 ≤ p - 1 := by linarith
  have ha : A p = 15 * (p-1)^4 + 52 * (p-1)^3 + 58 * (p-1)^2 +
      22 * (p-1) + 3 := by unfold A; ring
  have hd : D p = 15 * (p-1)^4 + 68 * (p-1)^3 + 106 * (p-1)^2 +
      66 * (p-1) + 15 := by unfold D; ring
  rw [ha, hd]
  constructor <;> positivity

theorem B_negative (p z : ℝ) (hp : 1 < p) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    B p z < 0 := by
  have hp0 : 0 < p := by linarith
  have hsq : 1 < p^2 := by nlinarith
  have hsq2 : 0 < 3*p^2-2 := by nlinarith
  have hc₁ : 0 ≤ 10 * p^2 * (p^2-1) * (3*p^2-2) := by positivity
  have hc₂ : 0 ≤ (p^2-1) * (3*p^2-2)^2 := by positivity
  have hzsq : z^2 ≤ 1 := by nlinarith
  have hle : B p z ≤ B p 1 := by
    unfold B
    nlinarith [mul_le_mul_of_nonneg_left hz1 hc₁,
      mul_le_mul_of_nonneg_left hzsq hc₂]
  obtain ⟨ha,hd⟩ := factors_pos p hp
  rw [factor_at_one] at hle
  exact lt_of_le_of_lt hle (neg_neg_of_pos (mul_pos ha hd))

/-- Appendix A, exact identity, before the coefficients are specialized. -/
theorem general_residual_identity (a b c p y : ℝ) (hp : p ≠ 0) :
    (1-y^2) * (a + 3*b*y^2 + 5*c*y^4) - (1/p) * (1-(a*y+b*y^3+c*y^5)^2) =
      (a*p-1)/p + (a^2-a*p+3*b*p)/p*y^2 +
      (2*a*b-3*b*p+5*c*p)/p*y^4 + (2*a*c+b^2-5*c*p)/p*y^6 +
      2*b*c/p*y^8 + c^2/p*y^10 := by
  field_simp
  <;> ring

theorem residual_identity (p y : ℝ) (hp : p ≠ 0) :
    (1-y^2) * (a₁ p + 3*a₃ p*y^2 + 5*a₅ p*y^4) -
      (1/p) * (1-(P₅ p y)^2) = y^6*(p^2-1)/(225*p^11)*B p (y^2) := by
  unfold P₅ a₁ a₃ a₅ B
  field_simp
  <;> ring

/-- Equation (21) has strictly negative right-hand side throughout (0,1). -/
theorem residual_negative (p y : ℝ) (hp : 1 < p) (hy0 : 0 < y) (hy1 : y < 1) :
    (1-y^2) * (a₁ p + 3*a₃ p*y^2 + 5*a₅ p*y^4) -
      (1/p) * (1-(P₅ p y)^2) < 0 := by
  have hp0 : 0 < p := by linarith
  rw [residual_identity p y hp0.ne']
  have hsq : 1 < p^2 := by nlinarith
  exact mul_neg_of_pos_of_neg (by positivity)
    (B_negative p (y^2) hp (sq_nonneg y) (by nlinarith))

/-- The formal derivative really is the polynomial used in the residual. -/
theorem hasDerivAt_P₅ (p y : ℝ) :
    HasDerivAt (P₅ p) (a₁ p + 3*a₃ p*y^2 + 5*a₅ p*y^4) y := by
  convert! (((hasDerivAt_id y).const_mul (a₁ p)).add
    (((hasDerivAt_id y).pow 3).const_mul (a₃ p))).add
    (((hasDerivAt_id y).pow 5).const_mul (a₅ p)) using 1 <;>
    (try simp only [P₅, Pi.add_apply, Nat.reduceSub, mul_one, id_eq]) <;> first | rfl | ring

end LeanMath.Papers.Cayley
