import LeanMath.Papers.SeriesReversion
import LeanMath.Papers.BranchTaylor
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Analysis.Analytic.Polynomial

noncomputable section
namespace LeanMath.Papers.AnalyticReversion
open Real Polynomial Filter Set
open scoped Topology
open SeriesReversion

def inverseJet (a b c d e f : ℝ) :=
  jet (c1 a) (c2 a b) (c3 a b c) (c4 a b c d) (c5 a b c d e) (c6 a b c d e f)

/-- Reversion also cancels in the composition order used by the update. -/
theorem reverse_jet_six (a b c d e f : ℝ) (ha : a ≠ 0) (j : Fin 7) :
    ((inverseJet a b c d e f).comp (jet a b c d e f)).coeff j = (X : Polynomial ℝ).coeff j := by
  unfold inverseJet
  rw [composition_coefficients]
  fin_cases j <;> norm_num [c1,c2,c3,c4,c5,c6,Polynomial.coeff_X] <;> field_simp [ha] <;> ring

/-- The polynomial composition error has an exact seventh-power factor. -/
theorem reverse_jet_factor (a b c d e f : ℝ) (ha : a ≠ 0) :
    ∃ V : Polynomial ℝ, (inverseJet a b c d e f).comp (jet a b c d e f)-X=X^7*V := by
  apply X_pow_dvd_iff.mpr
  intro j hj
  rw [Polynomial.coeff_sub,reverse_jet_six a b c d e f ha ⟨j,hj⟩,sub_self]

/-- Polynomial divided difference, with no division at coincident arguments. -/
def dd (a b c d e f u v : ℝ) := a+b*(u+v)+c*(u^2+u*v+v^2)+
  d*(u^3+u^2*v+u*v^2+v^3)+e*(u^4+u^3*v+u^2*v^2+u*v^3+v^4)+
  f*(u^5+u^4*v+u^3*v^2+u^2*v^3+u*v^4+v^5)

theorem jet_difference (a b c d e f u v : ℝ) :
    (jet a b c d e f).eval u-(jet a b c d e f).eval v=(u-v)*dd a b c d e f u v := by
  simp only [jet,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C]
  unfold dd
  ring

/-- A genuine analytic input with the prescribed six-jet has an analytic
seventh-order reversion error. This is a fixed-base local statement. -/
theorem analytic_error_factor (h : ℝ → ℝ) (a b c d e f : ℝ) (ha : a ≠ 0)
    (hh : AnalyticAt ℝ h 0)
    (hjet : ∃ A : ℝ → ℝ, AnalyticAt ℝ A 0 ∧ ∀ᶠ t in 𝓝 0,
      h t=(jet a b c d e f).eval t+t^7*A t) :
    ∃ B : ℝ → ℝ, AnalyticAt ℝ B 0 ∧ ∀ᶠ t in 𝓝 0,
      (inverseJet a b c d e f).eval (h t)-t=t^7*B t := by
  obtain ⟨A,hA,hEq⟩ := hjet
  obtain ⟨V,hV⟩ := reverse_jet_factor a b c d e f ha
  let D := fun t : ℝ => dd (c1 a) (c2 a b) (c3 a b c) (c4 a b c d)
    (c5 a b c d e) (c6 a b c d e f) (h t) ((jet a b c d e f).eval t)
  refine ⟨fun t => A t*D t+V.eval t,?_,?_⟩
  · have hP : AnalyticAt ℝ (fun t => (jet a b c d e f).eval t) 0 :=
      AnalyticOnNhd.eval_polynomial _ 0 (mem_univ 0)
    have hD : AnalyticAt ℝ D 0 := by unfold D dd; fun_prop
    exact (hA.mul hD).add (AnalyticOnNhd.eval_polynomial V 0 (mem_univ 0))
  · filter_upwards [hEq] with t ht
    have hv := congrArg (fun P : Polynomial ℝ => P.eval t) hV
    simp only [Polynomial.eval_sub,Polynomial.eval_comp,Polynomial.eval_mul,
      Polynomial.eval_pow,Polynomial.eval_X] at hv
    have hd := jet_difference (c1 a) (c2 a b) (c3 a b c) (c4 a b c d)
      (c5 a b c d e) (c6 a b c d e f) (h t) ((jet a b c d e f).eval t)
    change (inverseJet a b c d e f).eval (h t)-
      (inverseJet a b c d e f).eval ((jet a b c d e f).eval t)=
      (h t-(jet a b c d e f).eval t)*D t at hd
    have he : h t-(jet a b c d e f).eval t=t^7*A t := by linarith
    rw [he] at hd
    linear_combination hd+hv

def taylorCoeff (h : ℝ → ℝ) (j : ℕ) := iteratedDeriv j h 0/(j.factorial : ℝ)
def reversion (h : ℝ → ℝ) := inverseJet (taylorCoeff h 1) (taylorCoeff h 2)
  (taylorCoeff h 3) (taylorCoeff h 4) (taylorCoeff h 5) (taylorCoeff h 6)

/-- Analyticity supplies the six-jet remainder required by the algebraic certificate. -/
theorem six_jet_remainder (h : ℝ → ℝ) (hh : AnalyticAt ℝ h 0) (h0 : h 0=0) :
    ∃ A : ℝ → ℝ, AnalyticAt ℝ A 0 ∧ ∀ᶠ t in 𝓝 0,
      h t=(jet (taylorCoeff h 1) (taylorCoeff h 2) (taylorCoeff h 3)
        (taylorCoeff h 4) (taylorCoeff h 5) (taylorCoeff h 6)).eval t+t^7*A t := by
  obtain ⟨A,hA,hEq⟩ := hh.exists_eventuallyEq_sum_add_pow_mul 7
  refine ⟨A,hA,?_⟩
  filter_upwards [hEq] with t ht
  rw [ht]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,
    iteratedDeriv_zero,h0,smul_eq_mul]
  simp only [jet,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C,taylorCoeff]
  norm_num
  <;> ring

theorem analytic_reversion_factor (h : ℝ → ℝ) (hh : AnalyticAt ℝ h 0)
    (h0 : h 0=0) (h1 : deriv h 0 ≠ 0) :
    ∃ B : ℝ → ℝ, AnalyticAt ℝ B 0 ∧ ∀ᶠ t in 𝓝 0,
      (reversion h).eval (h t)-t=t^7*B t := by
  apply analytic_error_factor h _ _ _ _ _ _ _ hh (six_jet_remainder h hh h0)
  simpa [taylorCoeff,iteratedDeriv_succ,iteratedDeriv_zero] using h1

/-- Fixed-base analytic reversion has an actual O(t^7) remainder. -/
theorem analytic_reversion_bigO (h : ℝ → ℝ) (hh : AnalyticAt ℝ h 0)
    (h0 : h 0=0) (h1 : deriv h 0 ≠ 0) :
    (fun t : ℝ => (reversion h).eval (h t)-t) =O[𝓝 0] (fun t : ℝ => t^7) := by
  obtain ⟨B,hB,hEq⟩ := analytic_reversion_factor h hh h0 h1
  apply (BranchTaylor.analytic_remainder_bigO B 7 hB).congr' _ Filter.EventuallyEq.rfl
  filter_upwards [hEq] with t ht
  exact ht.symm

/-- The seventh-order normalized error has a finite limit, supplied by the analytic factor. -/
theorem analytic_reversion_limit (h : ℝ → ℝ) (hh : AnalyticAt ℝ h 0)
    (h0 : h 0=0) (h1 : deriv h 0 ≠ 0) :
    ∃ L : ℝ, Tendsto (fun t : ℝ => ((reversion h).eval (h t)-t)/t^7) (𝓝[≠] 0) (𝓝 L) := by
  obtain ⟨B,hB,hEq⟩ := analytic_reversion_factor h hh h0 h1
  refine ⟨B 0,?_⟩
  apply (hB.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [mem_nhdsWithin_of_mem_nhds hEq,self_mem_nhdsWithin] with t ht ht0
  rw [ht]
  field_simp [show t ≠ 0 from ht0]

open MeasureTheory ProbabilityTheory ExponentialFamily

/-- The degree-six correction built from the tilted cumulants at the chosen base. -/
def cumulantJet (ν : Measure ℝ) (x : ℝ) := inverseJet
  (cumulant ν x 1) (cumulant ν x 2/2) (cumulant ν x 3/6)
  (cumulant ν x 4/24) (cumulant ν x 5/120) (cumulant ν x 6/720)

theorem cumulantJet_eq_reversion (ν : Measure ℝ) (x : ℝ) :
    cumulantJet ν x=reversion (g (law ν x)) := by
  norm_num [cumulantJet,reversion,taylorCoeff,cumulant,g]

/-- For every fixed tilted law, the printed cumulant polynomial inverts its
logarithmic residual through order six, with a certified analytic remainder. -/
theorem cumulant_reversion_factor (ν : Measure ℝ) [IsFiniteMeasure ν] [NeZero ν]
    (m n x : ℝ) (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n) (hx : cumulant ν x 1 ≠ 0) :
    ∃ B : ℝ → ℝ, AnalyticAt ℝ B 0 ∧ ∀ᶠ z in 𝓝 0,
      (cumulantJet ν x).eval (g (law ν x) z)-z=z^7*B z := by
  letI := tilted_probability ν m n x hs
  have hsup := tilted_support ν m n x hs
  rw [cumulantJet_eq_reversion]
  apply analytic_reversion_factor _ (analytic (law ν x) m n hsup 0)
  · exact cgf_zero
  · simpa only [cumulant,g,iteratedDeriv_succ,iteratedDeriv_zero] using hx

theorem cumulant_reversion_bigO (ν : Measure ℝ) [IsFiniteMeasure ν] [NeZero ν]
    (m n x : ℝ) (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n) (hx : cumulant ν x 1 ≠ 0) :
    (fun z : ℝ => (cumulantJet ν x).eval (g (law ν x) z)-z)
      =O[𝓝 0] (fun z : ℝ => z^7) := by
  obtain ⟨B,hB,hEq⟩ := cumulant_reversion_factor ν m n x hs hx
  apply (BranchTaylor.analytic_remainder_bigO B 7 hB).congr' _ Filter.EventuallyEq.rfl
  filter_upwards [hEq] with z hz
  exact hz.symm

/-- Log-coordinate implementation of the printed degree-six cumulant update. -/
def cumulantStep (ν : Measure ℝ) (target x : ℝ) :=
  x+(cumulantJet ν x).eval (target-g ν x)

theorem reversion_linear (p : ℝ) : reversion (fun t : ℝ => t*p)=C (1/p)*X := by
  norm_num [reversion,taylorCoeff,iteratedDeriv_succ,iteratedDeriv_zero,
    inverseJet,c1,c2,c3,c4,c5,c6,jet]
  <;> ring

/-- The actual cumulant update is exact in one step on the monomial stratum. -/
theorem monomial_cumulant_exact (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (p r x : ℝ) (hp : ∀ᵐ k ∂ν, k=p) (hp0 : p ≠ 0) :
    cumulantStep ν (g ν r) x=r := by
  have hs : ∀ᵐ k ∂ν, p ≤ k ∧ k ≤ p := by
    filter_upwards [hp] with k hk
    simp [hk]
  letI := tilted_probability ν p p x hs
  have htilt : ∀ᵐ k ∂law ν x, k=p := by
    filter_upwards [tilted_support ν p p x hs] with k hk
    exact le_antisymm hk.2 hk.1
  have he : g (law ν x)=(fun t : ℝ => t*p) :=
    funext (fun t => monomial_log_partition (law ν x) p t htilt)
  unfold cumulantStep
  rw [cumulantJet_eq_reversion,he,reversion_linear,
    monomial_log_partition ν p r hp,monomial_log_partition ν p x hp]
  simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
  field_simp
  <;> ring

end LeanMath.Papers.AnalyticReversion
