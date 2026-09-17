import LeanMath.Papers.ExponentialFamily
import Mathlib.Analysis.Convex.Slope

noncomputable section
namespace LeanMath.Papers.ExponentialFamily
open Real Set MeasureTheory ProbabilityTheory Filter
open scoped Topology

/-- The equation has at most two solutions for a nondegenerate exponent law. -/
theorem no_three_roots (ν : Measure ℝ) [IsFiniteMeasure ν] [NeZero ν] (m n c x y z : ℝ)
    (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n)
    (hnd : ¬ ∃ a : ℝ, ∀ᵐ k ∂ν, k=a) (hxy : x < y) (hyz : y < z)
    (hx : g ν x=c) (hy : g ν y=c) (hz : g ν z=c) : False := by
  have hc := strictly_convex ν m n hs hnd
  have hh := hc.slope_strict_mono_adjacent (mem_univ x) (mem_univ z) hxy hyz
  simpa [slope_def_field,hx,hy,hz] using hh

/-- Positive supports give strict monotonicity, including a one-point law. -/
theorem positive_support_monotone (ν : Measure ℝ) [IsFiniteMeasure ν] [NeZero ν] (m n : ℝ)
    (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n) (hm : 0 < m) : StrictMono (g ν) := by
  apply strictMonoOn_univ.mp
  apply strictMonoOn_of_deriv_pos convex_univ
  · exact fun x _ => (analytic ν m n hs x).continuousAt.continuousWithinAt
  · intro x hx
    exact hm.trans_le (mean_in_support ν m n x hs).1

theorem negative_support_antitone (ν : Measure ℝ) [IsFiniteMeasure ν] [NeZero ν] (m n : ℝ)
    (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n) (hn : n < 0) : StrictAnti (g ν) := by
  apply strictAntiOn_univ.mp
  apply strictAntiOn_of_deriv_neg convex_univ
  · exact fun x _ => (analytic ν m n hs x).continuousAt.continuousWithinAt
  · intro x hx
    exact (mean_in_support ν m n x hs).2.trans_lt hn

/-- The right branch is strictly increasing once its mean exponent is positive. -/
theorem right_branch_monotone (ν : Measure ℝ) [IsFiniteMeasure ν] [NeZero ν] (m n x₀ : ℝ)
    (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n)
    (hnd : ¬ ∃ a : ℝ, ∀ᵐ k ∂ν, k=a) (h₀ : 0 ≤ deriv (g ν) x₀) :
    StrictMonoOn (g ν) (Ici x₀) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici x₀)
  · exact fun x _ => (analytic ν m n hs x).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    exact h₀.trans_lt (mean_strictly_increasing ν m n hs hnd hx)

theorem left_branch_antitone (ν : Measure ℝ) [IsFiniteMeasure ν] [NeZero ν] (m n x₀ : ℝ)
    (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n)
    (hnd : ¬ ∃ a : ℝ, ∀ᵐ k ∂ν, k=a) (h₀ : deriv (g ν) x₀ ≤ 0) :
    StrictAntiOn (g ν) (Iic x₀) := by
  apply strictAntiOn_of_deriv_neg (convex_Iic x₀)
  · exact fun x _ => (analytic ν m n hs x).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Iic] at hx
    exact (mean_strictly_increasing ν m n hs hnd hx).trans_le h₀

/-- The sign of the residual identifies the side once the right branch is selected. -/
theorem right_branch_side_test (ν : Measure ℝ) [IsFiniteMeasure ν] [NeZero ν] (m n x₀ x r : ℝ)
    (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n)
    (hnd : ¬ ∃ a : ℝ, ∀ᵐ k ∂ν, k=a) (h₀ : 0 ≤ deriv (g ν) x₀)
    (hx : x₀ ≤ x) (hr : x₀ ≤ r) :
    (0 < g ν r-g ν x ↔ x < r) := by
  rw [sub_pos]
  exact (right_branch_monotone ν m n x₀ hs hnd h₀).lt_iff_lt hx hr

/-- A uniformly positive derivative yields an explicit finite bracket for every target. -/
theorem positive_support_unique_root (ν : Measure ℝ) [IsFiniteMeasure ν] [NeZero ν]
    (m n c : ℝ) (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n) (hm : 0 < m) :
    ∃! x : ℝ, g ν x=c := by
  let B := (|c-g ν 0|+1)/m
  have hB : 0 < B := div_pos (by positivity) hm
  have he : m*B=|c-g ν 0|+1 := by dsimp [B]; field_simp
  have hd : Differentiable ℝ (g ν) := fun x => (analytic ν m n hs x).differentiableAt
  have hlo := mul_sub_le_image_sub_of_le_deriv hd
    (fun x => (mean_in_support ν m n x hs).1) (show -B ≤ 0 by linarith)
  have hhi := mul_sub_le_image_sub_of_le_deriv hd
    (fun x => (mean_in_support ν m n x hs).1) hB.le
  have hleft : g ν (-B) ≤ c := by nlinarith [neg_abs_le (c-g ν 0)]
  have hright : c ≤ g ν B := by nlinarith [le_abs_self (c-g ν 0)]
  obtain ⟨x,hx,hxc⟩ := intermediate_value_Icc (show -B ≤ B by linarith)
    hd.continuous.continuousOn ⟨hleft,hright⟩
  refine ⟨x,hxc,fun y hy => ?_⟩
  exact (positive_support_monotone ν m n hs hm).injective (hy.trans hxc.symm)

end LeanMath.Papers.ExponentialFamily
