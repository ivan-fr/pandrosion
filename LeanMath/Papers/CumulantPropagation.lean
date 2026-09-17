import LeanMath.Papers.MovingTaylor

noncomputable section
namespace LeanMath.Papers.CumulantPropagation
open Real Filter Set MeasureTheory ProbabilityTheory
open scoped Topology
open ExponentialFamily AnalyticReversion MovingTaylor SeriesReversion

/-- Evaluate the inverse polynomial at the degree-six moving Taylor model. -/
def modelStep (ν : Measure ℝ) (r x : ℝ) :=
  x+(cumulantJet ν x).eval ((forwardJet ν x).eval (r-x))

/-- Divided difference of the inverse polynomial at the true and model residuals. -/
def propagationFactor (ν : Measure ℝ) (r x : ℝ) :=
  dd (c1 (cumulant ν x 1))
    (c2 (cumulant ν x 1) (cumulant ν x 2/2))
    (c3 (cumulant ν x 1) (cumulant ν x 2/2) (cumulant ν x 3/6))
    (c4 (cumulant ν x 1) (cumulant ν x 2/2) (cumulant ν x 3/6) (cumulant ν x 4/24))
    (c5 (cumulant ν x 1) (cumulant ν x 2/2) (cumulant ν x 3/6) (cumulant ν x 4/24) (cumulant ν x 5/120))
    (c6 (cumulant ν x 1) (cumulant ν x 2/2) (cumulant ν x 3/6) (cumulant ν x 4/24) (cumulant ν x 5/120) (cumulant ν x 6/720))
    (g ν r-g ν x) ((forwardJet ν x).eval (r-x))

/-- Exact identity, including when the true and polynomial residuals coincide. -/
theorem step_difference (ν : Measure ℝ) (r x : ℝ) :
    cumulantStep ν (g ν r) x-modelStep ν r x=
      (g ν r-g ν x-(forwardJet ν x).eval (r-x))*propagationFactor ν r x := by
  have h := jet_difference (c1 (cumulant ν x 1))
    (c2 (cumulant ν x 1) (cumulant ν x 2/2))
    (c3 (cumulant ν x 1) (cumulant ν x 2/2) (cumulant ν x 3/6))
    (c4 (cumulant ν x 1) (cumulant ν x 2/2) (cumulant ν x 3/6) (cumulant ν x 4/24))
    (c5 (cumulant ν x 1) (cumulant ν x 2/2) (cumulant ν x 3/6) (cumulant ν x 4/24) (cumulant ν x 5/120))
    (c6 (cumulant ν x 1) (cumulant ν x 2/2) (cumulant ν x 3/6) (cumulant ν x 4/24) (cumulant ν x 5/120) (cumulant ν x 6/720))
    (g ν r-g ν x) ((forwardJet ν x).eval (r-x))
  simpa only [cumulantStep,modelStep,cumulantJet,inverseJet,propagationFactor,add_sub_add_left_eq_sub] using h

theorem propagation_at_root (ν : Measure ℝ) (r : ℝ) :
    propagationFactor ν r r=1/cumulant ν r 1 := by
  simp [propagationFactor,forwardJet,jet,dd,c1]

/-- The divided difference stays analytic as the base and both residuals move. -/
theorem propagation_analytic (ν : Measure ℝ) [IsFiniteMeasure ν] [NeZero ν]
    (m n r x : ℝ) (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n) (hx : cumulant ν x 1 ≠ 0) :
    AnalyticAt ℝ (propagationFactor ν r) x := by
  have h1 := cumulant_analytic ν m n x hs 1 (by norm_num)
  have h2 := cumulant_analytic ν m n x hs 2 (by norm_num)
  have h3 := cumulant_analytic ν m n x hs 3 (by norm_num)
  have h4 := cumulant_analytic ν m n x hs 4 (by norm_num)
  have h5 := cumulant_analytic ν m n x hs 5 (by norm_num)
  have h6 := cumulant_analytic ν m n x hs 6 (by norm_num)
  have hg := analytic ν m n hs x
  unfold propagationFactor forwardJet jet
  simp only [Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C]
  unfold dd c1 c2 c3 c4 c5 c6
  fun_prop (disch := positivity)

/-- Exact seventh-order contribution of the Taylor remainder after the full inverse polynomial. -/
theorem propagated_remainder_limit (ν : Measure ℝ) [IsFiniteMeasure ν] [NeZero ν]
    (m n r : ℝ) (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n) (hr : cumulant ν r 1 ≠ 0) :
    Tendsto (fun e : ℝ =>
      (cumulantStep ν (g ν r) (r+e)-modelStep ν r (r+e))/e^7) (𝓝[≠] 0)
      (𝓝 (-cumulant ν r 7/(5040*cumulant ν r 1))) := by
  have hc : ContinuousAt (fun e : ℝ => propagationFactor ν r (r+e)) 0 := by
    have h := (propagation_analytic ν m n r r hs hr).continuousAt
    have h' : ContinuousAt (propagationFactor ν r) (r+0) := by simpa using h
    exact h'.comp (show ContinuousAt (fun e : ℝ => r+e) 0 by fun_prop)
  have hp : Tendsto (fun e : ℝ => propagationFactor ν r (r+e)) (𝓝[≠] 0)
      (𝓝 (1/cumulant ν r 1)) := by
    simpa only [add_zero,propagation_at_root] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have h := (moving_cumulant_jet_limit ν m n r hs).mul hp
  have he : (-cumulant ν r 7/5040)*(1/cumulant ν r 1)= -cumulant ν r 7/(5040*cumulant ν r 1) := by ring
  rw [he] at h
  apply h.congr'
  apply Eventually.of_forall
  intro e
  dsimp only
  rw [step_difference,show r-(r+e)= -e by ring]
  ring

/-- Propagation preserves the order-seven bound along the actual moving-base path. -/
theorem propagated_remainder_bigO (ν : Measure ℝ) [IsFiniteMeasure ν] [NeZero ν]
    (m n r : ℝ) (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n) (hr : cumulant ν r 1 ≠ 0) :
    (fun e : ℝ => cumulantStep ν (g ν r) (r+e)-modelStep ν r (r+e))
      =O[𝓝[≠] 0] (fun e : ℝ => e^7) := by
  apply Asymptotics.isBigO_of_div_tendsto_nhds _ _ (propagated_remainder_limit ν m n r hs hr)
  filter_upwards [self_mem_nhdsWithin] with e he hzero
  exact False.elim ((pow_ne_zero 7 he) hzero)

end LeanMath.Papers.CumulantPropagation
