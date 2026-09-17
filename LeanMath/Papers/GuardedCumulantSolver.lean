import LeanMath.Papers.GuardedBracket
import LeanMath.Papers.CumulantCoefficient

noncomputable section
namespace LeanMath.Papers.GuardedCumulantSolver
open Real Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
open ExponentialFamily AnalyticReversion

/-- Explicit finite initial interval for a uniformly positive support. -/
def radius (ν : Measure ℝ) (m c : ℝ) := (|c-g ν 0|+1)/m

theorem positive_initial_bracket (ν : Measure ℝ) [IsFiniteMeasure ν] [NeZero ν]
    (m n c : ℝ) (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n) (hm : 0 < m) :
    0 < radius ν m c ∧ g ν (-radius ν m c) ≤ c ∧ c ≤ g ν (radius ν m c) := by
  have hB : 0 < radius ν m c := div_pos (by positivity) hm
  have he : m*radius ν m c=|c-g ν 0|+1 := by unfold radius; field_simp
  have hd : Differentiable ℝ (g ν) := fun x => (analytic ν m n hs x).differentiableAt
  have hlo := mul_sub_le_image_sub_of_le_deriv hd
    (fun x => (mean_in_support ν m n x hs).1) (show -radius ν m c ≤ 0 by linarith)
  have hhi := mul_sub_le_image_sub_of_le_deriv hd
    (fun x => (mean_in_support ν m n x hs).1) hB.le
  refine ⟨hB,?_,?_⟩
  · nlinarith [neg_abs_le (c-g ν 0)]
  · nlinarith [le_abs_self (c-g ν 0)]

def solvePositive (ν : Measure ℝ) (m c ε : ℝ) :=
  GuardedBracket.solve (g ν) c (cumulantStep ν c) (-radius ν m c) (radius ν m c) ε

/-- A complete exact-real solve from the target and positive support bounds, without a supplied root. -/
theorem positive_solve_certificate (ν : Measure ℝ) [IsFiniteMeasure ν] [NeZero ν]
    (m n c ε : ℝ) (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n) (hm : 0 < m) (hε : 0 < ε) :
    ∃ r : ℝ, g ν r=c ∧ r ∈ Icc (solvePositive ν m c ε).1 (solvePositive ν m c ε).2 ∧
      (solvePositive ν m c ε).2-(solvePositive ν m c ε).1 < 2*ε ∧
      |GuardedBracket.middle (solvePositive ν m c ε)-r| < ε := by
  obtain ⟨hB,ha,hb⟩ := positive_initial_bracket ν m n c hs hm
  have hab : -radius ν m c ≤ radius ν m c := by linarith
  have hc : ContinuousOn (g ν) (Icc (-radius ν m c) (radius ν m c)) :=
    fun x _ => (analytic ν m n hs x).continuousAt.continuousWithinAt
  obtain ⟨r,hr,hval⟩ := intermediate_value_Icc hab hc ⟨ha,hb⟩
  have h := GuardedBracket.solve_certificate (g ν) c r (-radius ν m c) (radius ν m c) ε
    (cumulantStep ν c) ((positive_support_monotone ν m n hs hm).strictMonoOn _) hval hr hε
  exact ⟨r,hval,⟨h.2.1,h.2.2.1⟩,h.2.2.2.2.1,h.2.2.2.2.2⟩

/-- Tangent-based upper endpoint on an increasing convex branch. -/
def upper (ν : Measure ℝ) (c a : ℝ) := a+(c-g ν a)/deriv (g ν) a

theorem right_initial_bracket (ν : Measure ℝ) [IsFiniteMeasure ν]
    (m n c a : ℝ) (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n)
    (ha : 0 < deriv (g ν) a) (hc : g ν a ≤ c) :
    a ≤ upper ν c a ∧ c ≤ g ν (upper ν c a) := by
  have hab : a ≤ upper ν c a := by
    unfold upper
    exact le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr hc) ha.le)
  refine ⟨hab,?_⟩
  rcases eq_or_lt_of_le hab with heq | hlt
  · have he : c=g ν a := by
      unfold upper at heq
      have hz : (c-g ν a)/deriv (g ν) a=0 := by linarith
      exact sub_eq_zero.mp ((div_eq_zero_iff).mp hz |>.resolve_right ha.ne')
    rw [←heq,he]
  · have ht := (convex ν m n hs).deriv_le_slope (mem_univ a) (mem_univ (upper ν c a)) hlt
      (analytic ν m n hs a).differentiableAt
    rw [slope_def_field] at ht
    have hh := (le_div_iff₀ (sub_pos.mpr hlt)).mp ht
    have he : deriv (g ν) a*(upper ν c a-a)=c-g ν a := by unfold upper; field_simp; ring
    linarith

def solveRight (ν : Measure ℝ) (c a ε : ℝ) :=
  GuardedBracket.solve (g ν) c (cumulantStep ν c) a (upper ν c a) ε

/-- Signed supports are permitted when a point below the target selects the increasing branch. -/
theorem right_solve_certificate (ν : Measure ℝ) [IsFiniteMeasure ν] [NeZero ν]
    (m n c a ε : ℝ) (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n)
    (hnd : ¬ ∃ b : ℝ, ∀ᵐ k ∂ν, k=b) (ha : 0 < deriv (g ν) a)
    (hc : g ν a ≤ c) (hε : 0 < ε) :
    ∃ r : ℝ, g ν r=c ∧ r ∈ Icc (solveRight ν c a ε).1 (solveRight ν c a ε).2 ∧
      (solveRight ν c a ε).2-(solveRight ν c a ε).1 < 2*ε ∧
      |GuardedBracket.middle (solveRight ν c a ε)-r| < ε := by
  obtain ⟨hab,hb⟩ := right_initial_bracket ν m n c a hs ha hc
  have hcont : ContinuousOn (g ν) (Icc a (upper ν c a)) :=
    fun x _ => (analytic ν m n hs x).continuousAt.continuousWithinAt
  obtain ⟨r,hr,hval⟩ := intermediate_value_Icc hab hcont ⟨hc,hb⟩
  have hm : StrictMonoOn (g ν) (Icc a (upper ν c a)) :=
    (right_branch_monotone ν m n a hs hnd ha.le).mono (fun _ ht => ht.1)
  have h := GuardedBracket.solve_certificate (g ν) c r a (upper ν c a) ε (cumulantStep ν c) hm hval hr hε
  exact ⟨r,hval,⟨h.2.1,h.2.2.1⟩,h.2.2.2.2.1,h.2.2.2.2.2⟩

end LeanMath.Papers.GuardedCumulantSolver
