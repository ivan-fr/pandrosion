import LeanMath.Papers.AnalyticReversion

noncomputable section
namespace LeanMath.Papers.MovingTaylor
open Real Filter Set
open scoped Topology

/-- Taylor polynomial based at x, evaluated at a fixed target r. -/
def backward (f : ℝ → ℝ) (r : ℝ) (n : ℕ) (x : ℝ) :=
  ∑ j ∈ Finset.range (n+1), iteratedDeriv j f x*(r-x)^j/(j.factorial : ℝ)

theorem analytic_iterated (f : ℝ → ℝ) (hf : ∀ x, AnalyticAt ℝ f x) (n : ℕ) (x : ℝ) :
    AnalyticAt ℝ (iteratedDeriv n f) x := by
  induction n with
  | zero => simpa using hf x
  | succ n ih => simpa only [iteratedDeriv_succ] using ih.deriv

theorem iterated_hasDeriv (f : ℝ → ℝ) (hf : ∀ x, AnalyticAt ℝ f x) (n : ℕ) (x : ℝ) :
    HasDerivAt (iteratedDeriv n f) (iteratedDeriv (n+1) f x) x := by
  simpa only [iteratedDeriv_succ] using (analytic_iterated f hf n x).differentiableAt.hasDerivAt

/-- Every lower-order term cancels upon differentiating the moving-base Taylor polynomial. -/
theorem backward_derivative (f : ℝ → ℝ) (hf : ∀ x, AnalyticAt ℝ f x)
    (r x : ℝ) (n : ℕ) :
    HasDerivAt (backward f r n)
      (iteratedDeriv (n+1) f x*(r-x)^n/(n.factorial : ℝ)) x := by
  induction n with
  | zero =>
    have he : backward f r 0=f := by funext t; simp [backward]
    rw [he]
    simpa only [Nat.zero_add,pow_zero,Nat.factorial_zero,Nat.cast_one,mul_one,div_one,iteratedDeriv_zero] using iterated_hasDeriv f hf 0 x
  | succ n ih =>
    have he : backward f r (n+1)=(fun t => backward f r n t+
        iteratedDeriv (n+1) f t*(r-t)^(n+1)/((n+1).factorial : ℝ)) := by
      funext t
      simp only [backward,Finset.sum_range_succ]
    rw [he]
    have hd := (((iterated_hasDeriv f hf (n+1) x).mul
      (((hasDerivAt_id x).const_sub r).pow (n+1))).div_const ((n+1).factorial : ℝ))
    convert! ih.add hd using 1
    simp only [Pi.pow_apply,id_eq,Nat.add_sub_cancel]
    simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    have hn : (n:ℝ)+1 ≠ 0 := by positivity
    have hfac : (n.factorial:ℝ) ≠ 0 := by positivity
    field_simp
    <;> ring

def residual (f : ℝ → ℝ) (r : ℝ) (n : ℕ) (e : ℝ) := f r-backward f r n (r+e)

theorem residual_zero (f : ℝ → ℝ) (r : ℝ) (n : ℕ) : residual f r n 0=0 := by
  unfold residual backward
  simp only [add_zero,sub_self]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j hj hj0
    simp [zero_pow hj0]
  · simp

theorem residual_derivative (f : ℝ → ℝ) (hf : ∀ x, AnalyticAt ℝ f x)
    (r e : ℝ) (n : ℕ) :
    HasDerivAt (residual f r n)
      (e^n*((-1:ℝ)^(n+1)*iteratedDeriv (n+1) f (r+e)/(n.factorial : ℝ))) e := by
  have h := ((backward_derivative f hf r (r+e) n).comp e ((hasDerivAt_id e).const_add r)).const_sub (f r)
  convert! h using 1
  rw [show r-(r+e)= -e by ring,neg_pow,pow_succ]
  ring

/-- Exact leading remainder, allowing the Taylor base to vary with e. -/
theorem residual_limit (f : ℝ → ℝ) (hf : ∀ x, AnalyticAt ℝ f x) (r : ℝ) (n : ℕ) :
    Tendsto (fun e : ℝ => residual f r n e/e^(n+1)) (𝓝[≠] 0)
      (𝓝 (((-1:ℝ)^(n+1)*iteratedDeriv (n+1) f r)/((n+1).factorial : ℝ))) := by
  have hc : ContinuousAt (fun e : ℝ => (-1:ℝ)^(n+1)*iteratedDeriv (n+1) f (r+e)/(n.factorial : ℝ)) 0 := by
    have h : Continuous (iteratedDeriv (n+1) f) := continuous_iff_continuousAt.mpr (fun x => (analytic_iterated f hf (n+1) x).continuousAt)
    fun_prop
  have h := LocalOrder.from_derivative n (residual f r n)
    (fun e : ℝ => (-1:ℝ)^(n+1)*iteratedDeriv (n+1) f (r+e)/(n.factorial : ℝ))
    (residual_zero f r n) (residual_derivative f hf r 0 n).continuousAt hc
    (Eventually.of_forall (fun e => residual_derivative f hf r e n))
  convert h using 1
  congr 1
  simp only [add_zero,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

open MeasureTheory ProbabilityTheory ExponentialFamily AnalyticReversion

/-- Every cumulant is analytic as a function of the moving base point. -/
theorem cumulant_analytic (ν : Measure ℝ) [IsFiniteMeasure ν] [NeZero ν]
    (m n x : ℝ) (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n) (j : ℕ) (hj : 0 < j) :
    AnalyticAt ℝ (fun t => cumulant ν t j) x := by
  have he : (fun t => cumulant ν t j)=iteratedDeriv j (g ν) :=
    funext (fun t => cumulant_hierarchy ν m n t hs j hj)
  rw [he]
  exact analytic_iterated (g ν) (analytic ν m n hs) j x

/-- The actual cumulant update, including its varying coefficients, is analytic near a simple root. -/
theorem cumulantStep_analytic (ν : Measure ℝ) [IsFiniteMeasure ν] [NeZero ν]
    (m n target x : ℝ) (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n) (hx : cumulant ν x 1 ≠ 0) :
    AnalyticAt ℝ (cumulantStep ν target) x := by
  have h1 := cumulant_analytic ν m n x hs 1 (by norm_num)
  have h2 := cumulant_analytic ν m n x hs 2 (by norm_num)
  have h3 := cumulant_analytic ν m n x hs 3 (by norm_num)
  have h4 := cumulant_analytic ν m n x hs 4 (by norm_num)
  have h5 := cumulant_analytic ν m n x hs 5 (by norm_num)
  have h6 := cumulant_analytic ν m n x hs 6 (by norm_num)
  have hg := analytic ν m n hs x
  unfold cumulantStep cumulantJet inverseJet SeriesReversion.jet
  simp only [Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C]
  unfold SeriesReversion.c1 SeriesReversion.c2 SeriesReversion.c3 SeriesReversion.c4 SeriesReversion.c5 SeriesReversion.c6
  fun_prop (disch := positivity)

/-- At the root the full cumulant step fixes that root. -/
theorem cumulantStep_fixed (ν : Measure ℝ) (r : ℝ) : cumulantStep ν (g ν r) r=r := by
  simp [cumulantStep,cumulantJet,inverseJet,SeriesReversion.jet]

/-- The Taylor remainder has the correct seventh-order limit even though its base is moving. -/
theorem cumulant_residual_limit (ν : Measure ℝ) [IsFiniteMeasure ν] [NeZero ν]
    (m n r : ℝ) (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n) :
    Tendsto (fun e : ℝ => residual (g ν) r 6 e/e^7) (𝓝[≠] 0)
      (𝓝 (-cumulant ν r 7/5040)) := by
  have h := residual_limit (g ν) (analytic ν m n hs) r 6
  rw [cumulant_hierarchy ν m n r hs 7 (by norm_num)]
  convert h using 1 <;> norm_num

def forwardJet (ν : Measure ℝ) (x : ℝ) := SeriesReversion.jet
  (cumulant ν x 1) (cumulant ν x 2/2) (cumulant ν x 3/6)
  (cumulant ν x 4/24) (cumulant ν x 5/120) (cumulant ν x 6/720)

/-- The polynomial used by the algebraic inverse is exactly the moving Taylor jet. -/
theorem backward_eq_cumulantJet (ν : Measure ℝ) [IsFiniteMeasure ν] [NeZero ν]
    (m n r x : ℝ) (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n) :
    backward (g ν) r 6 x=g ν x+(forwardJet ν x).eval (r-x) := by
  unfold forwardJet
  rw [cumulant_hierarchy ν m n x hs 1 (by norm_num),
    cumulant_hierarchy ν m n x hs 2 (by norm_num),
    cumulant_hierarchy ν m n x hs 3 (by norm_num),
    cumulant_hierarchy ν m n x hs 4 (by norm_num),
    cumulant_hierarchy ν m n x hs 5 (by norm_num),
    cumulant_hierarchy ν m n x hs 6 (by norm_num)]
  norm_num [backward,Finset.sum_range_succ,SeriesReversion.jet,Polynomial.eval_mul,
    Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C,iteratedDeriv_zero]
  <;> ring

/-- Residual of the actual moving cumulant jet, in the variables of the iteration. -/
theorem moving_cumulant_jet_limit (ν : Measure ℝ) [IsFiniteMeasure ν] [NeZero ν]
    (m n r : ℝ) (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n) :
    Tendsto (fun e : ℝ =>
      (g ν r-g ν (r+e)-(forwardJet ν (r+e)).eval (-e))/e^7) (𝓝[≠] 0)
      (𝓝 (-cumulant ν r 7/5040)) := by
  apply (cumulant_residual_limit ν m n r hs).congr'
  apply Eventually.of_forall
  intro e
  dsimp only
  unfold residual
  rw [backward_eq_cumulantJet ν m n r (r+e) hs,show r-(r+e)= -e by ring]
  ring

/-- Uniform local O(e^7) control along the moving-base path. -/
theorem moving_cumulant_jet_bigO (ν : Measure ℝ) [IsFiniteMeasure ν] [NeZero ν]
    (m n r : ℝ) (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n) :
    (fun e : ℝ => g ν r-g ν (r+e)-(forwardJet ν (r+e)).eval (-e))
      =O[𝓝[≠] 0] (fun e : ℝ => e^7) := by
  apply Asymptotics.isBigO_of_div_tendsto_nhds _ _ (moving_cumulant_jet_limit ν m n r hs)
  filter_upwards [self_mem_nhdsWithin] with e he hzero
  exact False.elim ((pow_ne_zero 7 he) hzero)

end LeanMath.Papers.MovingTaylor
