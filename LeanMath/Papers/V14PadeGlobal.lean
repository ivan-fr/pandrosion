import LeanMath.Papers.V14DiagonalRegularity

/-! Global convergence, directly for the Padé condition and the reciprocal lift of §13. -/
noncomputable section
namespace LeanMath.Papers.V14PadeGlobal
open Real Polynomial Filter Function Asymptotics
open scoped Topology
open LeanMath.Papers.V14PadeTheorem LeanMath.Papers.V14PadeNormalization
open LeanMath.Papers.V14DiagonalRegularity

def step (p : ℝ) (A B : ℝ[X]) (X u : ℝ) := u*(A.eval (X/u^p)/B.eval (X/u^p))

/-- Global convergence of any classical diagonal root Padé pair, for all positive starts. -/
theorem diagonal_global_convergence (p : ℝ) (hp : 1<p) (d : ℕ) (hd : 0<d)
    (A B : ℝ[X]) (hAB : IsDiagonal (1/p) d A B) (X u : ℝ) (hX : 0<X) (hu : 0<u) :
    Tendsto (fun n : ℕ => (step p A B X)^[n] u) atTop (𝓝 (X^(1/p))) := by
  have ha := LeanMath.Papers.V14DiagonalConvergence.reciprocal_exponent p hp
  have ha0 : -1<1/p ∧ 1/p<1 := ⟨by linarith [ha.1],ha.2⟩
  have he : ∀ t : ℝ, 0<t → step p A B X t=LeanMath.Papers.V14DiagonalConvergence.step p d X t := by
    intro t ht
    unfold step LeanMath.Papers.V14DiagonalConvergence.step
    rw [diagonal_value (1/p) ha d A B hAB (X/t^p) (div_pos hX (rpow_pos_of_pos ht p))]
  have hi : ∀ n : ℕ, 0<(LeanMath.Papers.V14DiagonalConvergence.step p d X)^[n] u ∧
      (step p A B X)^[n] u=(LeanMath.Papers.V14DiagonalConvergence.step p d X)^[n] u := by
    intro n
    induction n with
    | zero => exact ⟨hu,rfl⟩
    | succ n ih =>
      rw [iterate_succ_apply',iterate_succ_apply']
      constructor
      · exact mul_pos ih.1 (LeanMath.Papers.V14DiagonalError.correction_pos (1/p) ha0 d _
          (div_pos hX (rpow_pos_of_pos ih.1 p)))
      · rw [ih.2,he _ ih.1]
  exact (LeanMath.Papers.V14DiagonalConvergence.global_convergence p hp d hd X u hX hu).congr'
    (Filter.Eventually.of_forall (fun n => (hi n).2.symm))

/-- The near-balanced bilateral-derived reciprocal lift is globally convergent by itself.
No entry-cell, small-residual, or dyadic-preprocessing hypothesis is needed. -/
theorem near_balanced_global_convergence (p : ℝ) (hp : 1<p) (P Q : ℝ[X]) (m n : ℕ)
    (hP : P.natDegree ≤ m) (hQ : Q.natDegree ≤ n) (hbal : n=m ∨ n=m+1)
    (hQ0 : Q.eval 0≠0)
    (hmatch : (fun z : ℝ => LeanMath.Papers.V14CompressedAnalytic.germ (1/p) z-P.eval z/Q.eval z)
      =O[𝓝 0] (fun z => z^(m+n+1))) (X u : ℝ) (hX : 0<X) (hu : 0<u) :
    Tendsto (fun k : ℕ =>
      (step p (residualNumerator P Q (m+n+1)) (residualDenominator P Q (m+n+1)) X)^[k] u)
      atTop (𝓝 (X^(1/p))) := by
  exact diagonal_global_convergence p hp (m+n+1) (by omega) _ _
    (near_balanced_diagonal (1/p) P Q m n hP hQ hbal hQ0 hmatch).1 X u hX hu

/-- The strict no-crossing enclosure for every diagonal representative. -/
theorem diagonal_step_enclosure (p : ℝ) (hp : 1<p) (d : ℕ) (hd : 0<d)
    (A B : ℝ[X]) (hAB : IsDiagonal (1/p) d A B) (X u : ℝ) (hX : 0<X) (hu : 0<u) :
    (u<X^(1/p) → u<step p A B X u ∧ step p A B X u<X^(1/p)) ∧
    (X^(1/p)<u → X^(1/p)<step p A B X u ∧ step p A B X u<u) := by
  have ha := LeanMath.Papers.V14DiagonalConvergence.reciprocal_exponent p hp
  have he : step p A B X u=LeanMath.Papers.V14DiagonalConvergence.step p d X u := by
    unfold step LeanMath.Papers.V14DiagonalConvergence.step
    rw [diagonal_value (1/p) ha d A B hAB (X/u^p) (div_pos hX (rpow_pos_of_pos hu p))]
  have hr := rpow_pos_of_pos hX (1/p)
  have hx : (X^(1/p))^p=X := by rw [one_div,rpow_inv_rpow hX.le (by linarith : p≠0)]
  rw [he]
  exact ⟨fun h => LeanMath.Papers.V14DiagonalConvergence.step_below p hp d hd X _ u hr hx hu h,
    fun h => LeanMath.Papers.V14DiagonalConvergence.step_above p hp d hd X _ u hr hx h⟩

end LeanMath.Papers.V14PadeGlobal
