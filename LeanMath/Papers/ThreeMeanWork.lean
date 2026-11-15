import LeanMath.Papers.ThreeMeanGlobal
import LeanMath.Papers.DegreesEfficiency

/-! # Work, efficiency and rational degrees for the three-mean support

* the trace total `10 p + 11` of the three-mean inventory;
* the efficiency index of the three-mean support exceeds that of the decentered arc and that of
  the nested support for every positive degree;
* Proposition 4.5 (i) for the three-mean support: rational degrees `p = μ / ν` with `μ ≥ 3`. -/

noncomputable section
namespace LeanMath.Papers.ThreeMeanWork
open Real Filter Function
open scoped Topology
open LeanMath.Papers.ThreeMeanGlobal LeanMath.Papers.DegreesEfficiency

/-- The rows of the three-mean inventory add up to `3 j + (2p+1) p + 3 c`, and with a parallel
counted as `2 j + 3 c` this is `10 p + 11` traces. -/
theorem three_mean_inventory_total (p : ℕ) :
    (1 + 1 + 1 = 3) ∧
    ((2 * p - 1) + 2 = 2 * p + 1 ∨ p = 0) ∧
    (1 + 1 + 1 = 3) ∧
    (3 + 2 * (2 * p + 1)) + (3 + 3 * (2 * p + 1)) = 10 * p + 11 := by
  refine ⟨by norm_num, ?_, by norm_num, by ring⟩
  rcases Nat.eq_zero_or_pos p with h | h
  · exact Or.inr h
  · left
    omega

/-- `5 ^ 11 < 9 ^ 9`, in logarithmic form. -/
theorem log_ineq_mean : 11 * Real.log 5 < 9 * Real.log 9 := by
  have h : Real.log ((5 : ℝ) ^ 11) < Real.log ((9 : ℝ) ^ 9) :=
    Real.log_lt_log (by positivity) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  exact_mod_cast h

/-- The three-mean support (order 9, `10p+11` traces) is more efficient than the decentered arc
(order 5, `10p+9` traces) for every positive degree. -/
theorem effIndex_mean_gt_dec {p : ℝ} (hp : 0 < p) :
    effIndex 5 (10 * p + 9) < effIndex 9 (10 * p + 11) := by
  unfold effIndex
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  have h1 := log_ineq_mean
  have h2 := log_five_lt_log_nine
  have h3 : 0 < p * (Real.log 9 - Real.log 5) := mul_pos hp (by linarith)
  nlinarith

/-- The three-mean support is more efficient than the nested support (same order, `10p+59`
traces) for every positive degree. -/
theorem effIndex_mean_gt_nest {p : ℝ} (hp : 0 < p) :
    effIndex 9 (10 * p + 59) < effIndex 9 (10 * p + 11) := by
  unfold effIndex
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  have h9 : 0 < Real.log 9 := Real.log_pos (by norm_num)
  nlinarith

/-- With an integer degree the residual of the three-mean step uses an integer power only. -/
theorem step_natCast (μ : ℕ) (Y u : ℝ) :
    step (μ : ℝ) Y u = u * correction (μ : ℝ) (Y / u ^ μ) := by
  unfold step
  rw [Real.rpow_natCast]

/-- Proposition 4.5 (i) for the three-mean support. For a rational degree `p = μ / ν` with
`μ ≥ 3`, the three-mean iteration of integer degree `μ`, run on the input `X ^ ν`, converges to
`X ^ (1 / p)` from every positive start. -/
theorem rational_degree_three_mean {X u : ℝ} (hX : 0 < X) (hu : 0 < u) {μ : ℕ} (hμ : 3 ≤ μ)
    (ν : ℕ) :
    Tendsto (fun n : ℕ => (step (μ : ℝ) (X ^ ν))^[n] u) atTop
      (𝓝 (X ^ ((1 : ℝ) / ((μ : ℝ) / ν)))) :=
  rational_degree_convergence step
    (fun p X u hp hX hu => global_convergence p X u hp hX hu) hX hu hμ ν

/-- The same statement with the iteration written with integer powers. -/
theorem rational_degree_three_mean_integer_powers {X u : ℝ} (hX : 0 < X) (hu : 0 < u) {μ : ℕ}
    (hμ : 3 ≤ μ) (ν : ℕ) :
    Tendsto (fun n : ℕ => (fun v : ℝ => v * correction (μ : ℝ) (X ^ ν / v ^ μ))^[n] u) atTop
      (𝓝 (X ^ ((1 : ℝ) / ((μ : ℝ) / ν)))) := by
  have h := rational_degree_three_mean hX hu hμ ν
  have e : step (μ : ℝ) (X ^ ν) = fun v : ℝ => v * correction (μ : ℝ) (X ^ ν / v ^ μ) := by
    funext v
    exact step_natCast μ (X ^ ν) v
  rwa [e] at h

end LeanMath.Papers.ThreeMeanWork
