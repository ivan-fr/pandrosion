import research.reciprocal_frontier.EffectiveBounds

/-! Preparation for the uniform-exponent theorem. The finite positive-sum
bounds are unconditional. The bridge to the original polynomials explicitly
assumes the two product identities; those identities are NOT proved here. -/
noncomputable section
namespace LeanMath.Research.UniformTransfer
open Finset Polynomial
open LeanMath.Papers.V14DiagonalPolynomials

def delta (a : ℝ) : ℕ → ℝ
  | 0 => 1
  | k+1 => delta a k * (1-a^2/((k:ℝ)+1)^2)

def weight (d k : ℕ) (R : ℝ) : ℝ :=
  (d.choose k:ℝ)*((d+k).choose k:ℝ)*((2*k).choose k:ℝ)*R^k*(R-1)^(2*(d-k))

def model (a : ℝ) (d : ℕ) (R : ℝ) :=
  ∑ k ∈ range (d+1), weight d k R / delta a k

theorem step_factor (a : ℝ) (ha : -1<a ∧ a<1) (k : ℕ) :
    0<1-a^2/((k:ℝ)+1)^2 ∧ 1-a^2/((k:ℝ)+1)^2≤1 := by
  have hk : (0:ℝ)≤k := Nat.cast_nonneg k
  have has : a^2<1 := by nlinarith [mul_pos (by linarith : 0<1-a) (by linarith : 0<1+a)]
  constructor
  · apply sub_pos.mpr
    apply (div_lt_one (by positivity : 0<((k:ℝ)+1)^2)).mpr
    nlinarith [sq_nonneg (k:ℝ)]
  · exact sub_le_self _ (by positivity)

theorem delta_positive (a : ℝ) (ha : -1<a ∧ a<1) (k : ℕ) : 0<delta a k := by
  induction k with
  | zero => norm_num [delta]
  | succ k ih => exact mul_pos ih (step_factor a ha k).1

theorem delta_antitone (a : ℝ) (ha : -1<a ∧ a<1) : Antitone (delta a) := by
  apply antitone_nat_of_succ_le
  intro k
  exact mul_le_of_le_one_right (delta_positive a ha k).le (step_factor a ha k).2

theorem weight_nonnegative (d k : ℕ) (R : ℝ) (hR : 0≤R) : 0≤weight d k R := by
  dsimp [weight]
  rw [pow_mul]
  positivity

theorem model_bounds (a : ℝ) (ha : -1<a ∧ a<1) (d : ℕ) (R : ℝ) (hR : 0≤R) :
    (∑ k ∈ range (d+1), weight d k R) ≤ model a d R ∧
    model a d R ≤ (∑ k ∈ range (d+1), weight d k R)/delta a d := by
  constructor
  · apply sum_le_sum
    intro k hk
    have hk1 : delta a k≤1 := (delta_antitone a ha (Nat.zero_le k))
    exact (le_div_iff₀ (delta_positive a ha k)).mpr
      (mul_le_of_le_one_right (weight_nonnegative d k R hR) hk1)
  · rw [Finset.sum_div]
    apply sum_le_sum
    intro k hk
    exact div_le_div_of_nonneg_left (weight_nonnegative d k R hR)
      (delta_positive a ha d) (delta_antitone a ha (by have := mem_range.mp hk; omega))

/-- CONDITIONAL bridge: the missing all-degree Bailey product identity is
an explicit hypothesis, not an axiom or an already established theorem. -/
theorem polynomial_bounds_of_product_identity (a : ℝ) (ha : -1<a ∧ a<1)
    (d : ℕ) (R : ℝ) (hR : 0≤R)
    (identityA : (poly a d).eval R*(poly (-a) d).eval R=model a d R)
    (identityZero : ((poly 0 d).eval R)^2=∑ k ∈ range (d+1), weight d k R) :
    ((poly 0 d).eval R)^2 ≤ (poly a d).eval R*(poly (-a) d).eval R ∧
    (poly a d).eval R*(poly (-a) d).eval R ≤ ((poly 0 d).eval R)^2/delta a d := by
  rw [identityA,identityZero]
  exact model_bounds a ha d R hR

end LeanMath.Research.UniformTransfer

#print axioms LeanMath.Research.UniformTransfer.step_factor
#print axioms LeanMath.Research.UniformTransfer.delta_positive
#print axioms LeanMath.Research.UniformTransfer.delta_antitone
#print axioms LeanMath.Research.UniformTransfer.weight_nonnegative
#print axioms LeanMath.Research.UniformTransfer.model_bounds
#print axioms LeanMath.Research.UniformTransfer.polynomial_bounds_of_product_identity
