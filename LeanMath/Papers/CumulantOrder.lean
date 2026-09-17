import LeanMath.Papers.PolynomialPaths

noncomputable section
namespace LeanMath.Papers.CumulantOrder
open Real Polynomial Filter Set MeasureTheory ProbabilityTheory
open scoped Topology
open ExponentialFamily AnalyticReversion MovingTaylor CumulantPropagation PolynomialPaths

def composition (ν : Measure ℝ) (x : ℝ) := (cumulantJet ν x).comp (forwardJet ν x)
def tailValue (ν : Measure ℝ) (r e : ℝ) :=
  ∑ j ∈ Finset.range 30, (composition ν (r+e)).coeff (j+7)*(-e)^j
/-- Exact coefficient, currently expressed using a finite polynomial composition. -/
def errorCoefficient (ν : Measure ℝ) (r : ℝ) :=
  -(composition ν r).coeff 7-cumulant ν r 7/(5040*cumulant ν r 1)

theorem composition_coeff_analytic (ν : Measure ℝ) [IsFiniteMeasure ν] [NeZero ν]
    (m n r : ℝ) (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n) (hr : cumulant ν r 1 ≠ 0) :
    CoeffAnalytic (composition ν) r := by
  have h1 := cumulant_analytic ν m n r hs 1 (by norm_num)
  have h2 := (cumulant_analytic ν m n r hs 2 (by norm_num)).div_const (c := (2:ℝ))
  have h3 := (cumulant_analytic ν m n r hs 3 (by norm_num)).div_const (c := (6:ℝ))
  have h4 := (cumulant_analytic ν m n r hs 4 (by norm_num)).div_const (c := (24:ℝ))
  have h5 := (cumulant_analytic ν m n r hs 5 (by norm_num)).div_const (c := (120:ℝ))
  have h6 := (cumulant_analytic ν m n r hs 6 (by norm_num)).div_const (c := (720:ℝ))
  exact path_inverse_composition _ _ _ _ _ _ r h1 h2 h3 h4 h5 h6 hr

theorem tail_continuous (ν : Measure ℝ) [IsFiniteMeasure ν] [NeZero ν]
    (m n r : ℝ) (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n) (hr : cumulant ν r 1 ≠ 0) :
    ContinuousAt (tailValue ν r) 0 := by
  unfold tailValue
  apply AnalyticAt.continuousAt (𝕜 := ℝ)
  apply Finset.analyticAt_fun_sum
  intro j hj
  have hc := composition_coeff_analytic ν m n r hs hr (j+7)
  have hc' : AnalyticAt ℝ (fun x => (composition ν x).coeff (j+7)) (r+0) := by simpa using hc
  exact (hc'.comp (show AnalyticAt ℝ (fun e : ℝ => r+e) 0 by fun_prop)).fun_mul (by fun_prop)

theorem tail_zero (ν : Measure ℝ) (r : ℝ) : tailValue ν r 0=(composition ν r).coeff 7 := by
  unfold tailValue
  simp only [add_zero,neg_zero]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j hj hj0
    simp [zero_pow hj0]
  · simp

/-- All lower-degree model errors cancel even when the coefficients move. -/
theorem model_error_factor (ν : Measure ℝ) (r e : ℝ) (he : cumulant ν (r+e) 1 ≠ 0) :
    modelStep ν r (r+e)-r= -e^7*tailValue ν r e := by
  have hd : (composition ν (r+e)).natDegree < 37 := composition_degree _ _ _ _ _ _
  have hl : ∀ j < 7, (composition ν (r+e)).coeff j=(X : Polynomial ℝ).coeff j :=
    fun j hj => reverse_jet_six _ _ _ _ _ _ he ⟨j,hj⟩
  have h := eval_tail (composition ν (r+e)) hd hl (-e)
  simp only [composition,Polynomial.eval_comp] at h
  unfold modelStep tailValue
  rw [show r-(r+e)= -e by ring]
  change r+e+(cumulantJet ν (r+e)).eval ((forwardJet ν (r+e)).eval (-e))-r= _
  rw [neg_pow] at h
  norm_num at h
  unfold composition
  linear_combination h

theorem model_error_limit (ν : Measure ℝ) [IsFiniteMeasure ν] [NeZero ν]
    (m n r : ℝ) (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n) (hr : cumulant ν r 1 ≠ 0) :
    Tendsto (fun e : ℝ => (modelStep ν r (r+e)-r)/e^7) (𝓝[≠] 0)
      (𝓝 (-(composition ν r).coeff 7)) := by
  have ht : Tendsto (fun e : ℝ => -tailValue ν r e) (𝓝[≠] 0) (𝓝 (-tailValue ν r 0)) :=
    (tail_continuous ν m n r hs hr).tendsto.neg.mono_left nhdsWithin_le_nhds
  rw [tail_zero] at ht
  have hc : ContinuousAt (fun e : ℝ => cumulant ν (r+e) 1) 0 := by
    have h : ContinuousAt (fun x => cumulant ν x 1) (r+0) := by
      simpa using (cumulant_analytic ν m n r hs 1 (by norm_num)).continuousAt
    exact h.comp (by fun_prop)
  have hn : ∀ᶠ e in 𝓝 0, cumulant ν (r+e) 1 ≠ 0 := hc.eventually_ne (by simpa using hr)
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds hn] with e he he1
  rw [model_error_factor ν r e he1]
  field_simp [show e ≠ 0 from he]

/-- The actual moving-cumulant iteration has a seventh-order normalized error limit. -/
theorem full_error_limit (ν : Measure ℝ) [IsFiniteMeasure ν] [NeZero ν]
    (m n r : ℝ) (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n) (hr : cumulant ν r 1 ≠ 0) :
    Tendsto (fun e : ℝ => (cumulantStep ν (g ν r) (r+e)-r)/e^7) (𝓝[≠] 0)
      (𝓝 (errorCoefficient ν r)) := by
  have h := (model_error_limit ν m n r hs hr).add (propagated_remainder_limit ν m n r hs hr)
  have he : -(composition ν r).coeff 7 + -cumulant ν r 7/(5040*cumulant ν r 1)=errorCoefficient ν r := by unfold errorCoefficient; ring
  rw [he] at h
  apply h.congr'
  apply Eventually.of_forall
  intro e
  dsimp only
  ring

theorem full_error_bigO (ν : Measure ℝ) [IsFiniteMeasure ν] [NeZero ν]
    (m n r : ℝ) (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n) (hr : cumulant ν r 1 ≠ 0) :
    (fun e : ℝ => cumulantStep ν (g ν r) (r+e)-r) =O[𝓝[≠] 0] (fun e : ℝ => e^7) := by
  apply Asymptotics.isBigO_of_div_tendsto_nhds _ _ (full_error_limit ν m n r hs hr)
  filter_upwards [self_mem_nhdsWithin] with e he hzero
  exact False.elim ((pow_ne_zero 7 he) hzero)

/-- The order is exactly seven whenever the certified leading coefficient is nonzero. -/
theorem full_error_exact_order (ν : Measure ℝ) [IsFiniteMeasure ν] [NeZero ν]
    (m n r : ℝ) (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n) (hr : cumulant ν r 1 ≠ 0)
    (hK : errorCoefficient ν r ≠ 0) :
    (fun e : ℝ => cumulantStep ν (g ν r) (r+e)-r) =Θ[𝓝[≠] 0] (fun e : ℝ => e^7) := by
  exact (Asymptotics.isTheta_of_div_tendsto_nhds_ne_zero (full_error_limit ν m n r hs hr) hK).symm

end LeanMath.Papers.CumulantOrder
