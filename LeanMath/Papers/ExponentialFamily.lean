import LeanMath.Papers.ExtremalBracket
import Mathlib.Probability.Moments.Tilted
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

noncomputable section
namespace LeanMath.Papers.ExponentialFamily
open Real Set MeasureTheory ProbabilityTheory Filter
open scoped Topology ProbabilityTheory

def g (ν : Measure ℝ) : ℝ → ℝ := cgf id ν
def law (ν : Measure ℝ) (x : ℝ) := ν.tilted (fun k => x*k)
def cumulant (ν : Measure ℝ) (x : ℝ) (n : ℕ) := iteratedDeriv n (cgf id (law ν x)) 0

theorem exponential_integrable (ν : Measure ℝ) [IsFiniteMeasure ν] (m n x : ℝ)
    (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n) : Integrable (fun k => exp (x*k)) ν := by
  simpa only [mul_comm] using (Extremal.support_integrable ν m n x hs).2

theorem interior_all (ν : Measure ℝ) [IsFiniteMeasure ν] (m n : ℝ)
    (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n) (x : ℝ) :
    x ∈ interior (integrableExpSet id ν) := by
  have he : integrableExpSet id ν=univ := by
    ext t
    simp only [mem_univ,iff_true]
    exact exponential_integrable ν m n t hs
  rw [he,interior_univ]
  trivial

theorem analytic (ν : Measure ℝ) [IsFiniteMeasure ν] (m n : ℝ)
    (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n) (x : ℝ) : AnalyticAt ℝ (g ν) x :=
  analyticAt_cgf (interior_all ν m n hs x)

theorem tilted_probability (ν : Measure ℝ) [IsFiniteMeasure ν] [NeZero ν] (m n x : ℝ)
    (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n) : IsProbabilityMeasure (law ν x) :=
  isProbabilityMeasure_tilted (exponential_integrable ν m n x hs)

theorem tilted_support (ν : Measure ℝ) (m n x : ℝ)
    (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n) : ∀ᵐ k ∂(law ν x), m ≤ k ∧ k ≤ n :=
  (Measure.ae_le_iff_absolutelyContinuous.mpr (tilted_absolutelyContinuous ν (fun k => x*k))) hs

/-- Lemma 2.1: first derivative is the mean of the tilted exponent law. -/
theorem derivative_mean (ν : Measure ℝ) [IsFiniteMeasure ν] (m n x : ℝ)
    (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n) : deriv (g ν) x=∫ k, k ∂(law ν x) :=
  (integral_tilted_mul_self (interior_all ν m n hs x)).symm

/-- Lemma 2.1: second derivative is its variance. -/
theorem second_derivative_variance (ν : Measure ℝ) [IsFiniteMeasure ν] (m n x : ℝ)
    (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n) :
    iteratedDeriv 2 (g ν) x=Var[id; law ν x] :=
  (variance_tilted_mul (interior_all ν m n hs x)).symm

/-- Theorem 3.1: the complete residual identity, for continuous as well as atomic measures. -/
theorem residual_identity (ν : Measure ℝ) (x z : ℝ) :
    (∫ k, exp (z*k) ∂(law ν x)) = mgf id ν (x+z)/mgf id ν x := by
  rw [law,integral_exp_tilted]
  congr 1
  unfold mgf
  congr 1
  funext k
  simp only [Pi.add_apply,id_eq]
  congr 1
  ring

theorem cgf_shift (ν : Measure ℝ) [IsFiniteMeasure ν] [NeZero ν] (m n x z : ℝ)
    (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n) :
    cgf id (law ν x) z=g ν (x+z)-g ν x := by
  change log (∫ k, exp (z*k) ∂(law ν x))= _
  rw [residual_identity,log_div
    (mgf_pos' (X := id) (NeZero.ne ν) (exponential_integrable ν m n (x+z) hs)).ne'
    (mgf_pos' (X := id) (NeZero.ne ν) (exponential_integrable ν m n x hs)).ne']
  rfl

/-- The full cumulant hierarchy: every positive derivative order, not a finite list. -/
theorem cumulant_hierarchy (ν : Measure ℝ) [IsFiniteMeasure ν] [NeZero ν] (m n x : ℝ)
    (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n) (j : ℕ) (hj : 0 < j) :
    cumulant ν x j=iteratedDeriv j (g ν) x := by
  have he : cgf id (law ν x)=(fun z => -g ν x+g ν (x+z)) := by
    funext z
    rw [cgf_shift ν m n x z hs]
    ring
  unfold cumulant
  rw [he,iteratedDeriv_const_add hj,iteratedDeriv_comp_const_add]
  simp

theorem mean_in_support (ν : Measure ℝ) [IsFiniteMeasure ν] [NeZero ν] (m n x : ℝ)
    (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n) : m ≤ deriv (g ν) x ∧ deriv (g ν) x ≤ n := by
  letI := tilted_probability ν m n x hs
  rw [derivative_mean ν m n x hs]
  have ht := tilted_support ν m n x hs
  have hi := (Extremal.support_integrable (law ν x) m n 0 ht).1
  constructor
  · have h := integral_mono_ae (integrable_const m) hi (ht.mono fun k hk => hk.1)
    simpa using h
  · have h := integral_mono_ae hi (integrable_const n) (ht.mono fun k hk => hk.2)
    simpa using h

theorem convex (ν : Measure ℝ) [IsFiniteMeasure ν] (m n : ℝ)
    (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n) : ConvexOn ℝ univ (g ν) := by
  have ha : AnalyticOnNhd ℝ (g ν) univ := fun x _ => analytic ν m n hs x
  apply convexOn_of_deriv2_nonneg' convex_univ
  · exact fun x _ => (analytic ν m n hs x).differentiableAt.differentiableWithinAt
  · exact fun x _ => (ha.deriv x (mem_univ x)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [←iteratedDeriv_eq_iterate]
    rw [second_derivative_variance ν m n x hs]
    exact variance_nonneg _ _

/-- Tilting cannot remove nondegeneracy; hence the variance is strictly positive. -/
theorem variance_positive (ν : Measure ℝ) [IsFiniteMeasure ν] [NeZero ν] (m n x : ℝ)
    (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n)
    (hnd : ¬ ∃ c : ℝ, ∀ᵐ k ∂ν, k=c) : 0 < Var[id; law ν x] := by
  letI := tilted_probability ν m n x hs
  have hv := variance_nonneg id (law ν x)
  apply lt_of_le_of_ne hv
  intro he
  have hz : Var[id; law ν x]=0 := he.symm
  have hc := ae_eq_integral_of_variance_eq_zero
    (memLp_tilted_mul (interior_all ν m n hs x) 2) hz
  apply hnd
  refine ⟨∫ k, k ∂(law ν x),?_⟩
  exact (Measure.ae_le_iff_absolutelyContinuous.mpr
    (absolutelyContinuous_tilted (exponential_integrable ν m n x hs))) hc

theorem strictly_convex (ν : Measure ℝ) [IsFiniteMeasure ν] [NeZero ν] (m n : ℝ)
    (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n)
    (hnd : ¬ ∃ c : ℝ, ∀ᵐ k ∂ν, k=c) : StrictConvexOn ℝ univ (g ν) := by
  apply strictConvexOn_of_deriv2_pos' convex_univ
  · exact fun x _ => (analytic ν m n hs x).continuousAt.continuousWithinAt
  · intro x hx
    rw [←iteratedDeriv_eq_iterate,second_derivative_variance ν m n x hs]
    exact variance_positive ν m n x hs hnd

/-- The mean exponent is strictly increasing for every nondegenerate bounded law. -/
theorem mean_strictly_increasing (ν : Measure ℝ) [IsFiniteMeasure ν] [NeZero ν] (m n : ℝ)
    (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n)
    (hnd : ¬ ∃ c : ℝ, ∀ᵐ k ∂ν, k=c) : StrictMono (deriv (g ν)) := by
  have ha : AnalyticOnNhd ℝ (g ν) univ := fun x _ => analytic ν m n hs x
  apply strictMonoOn_univ.mp
  apply strictMonoOn_of_deriv_pos convex_univ
  · exact fun x _ => (ha.deriv x (mem_univ x)).continuousAt.continuousWithinAt
  · intro x hx
    have hv := variance_positive ν m n x hs hnd
    rw [←second_derivative_variance ν m n x hs] at hv
    simpa only [iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using hv

end LeanMath.Papers.ExponentialFamily
