import LeanMath.Papers.BranchStructure
import LeanMath.Papers.IntervalIteration

noncomputable section
namespace LeanMath.Papers.ExponentialFamily
open Real Set MeasureTheory ProbabilityTheory Filter Function
open scoped Topology

def envelopeStep (ν : Measure ℝ) (n c x : ℝ) := x+(c-g ν x)/n
def meanStep (ν : Measure ℝ) (c x : ℝ) := x+(c-g ν x)/deriv (g ν) x

theorem envelope_convergence (ν : Measure ℝ) [IsFiniteMeasure ν] [NeZero ν]
    (m n a r u : ℝ) (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n)
    (hnd : ¬ ∃ c : ℝ, ∀ᵐ k ∂ν, k=c) (ha : 0 < deriv (g ν) a)
    (hr : a ≤ r) (hu : a ≤ u) :
    Tendsto (fun j : ℕ => (envelopeStep ν n (g ν r))^[j] u) atTop (𝓝 r) := by
  have hn : 0 < n := ha.trans_le (mean_in_support ν m n a hs).2
  have hd : Differentiable ℝ (g ν) := fun x => (analytic ν m n hs x).differentiableAt
  have hm := right_branch_monotone ν m n a hs hnd ha.le
  have hbound := image_sub_le_mul_sub_of_deriv_le hd (fun x => (mean_in_support ν m n x hs).2)
  apply IntervalIteration.converge _ a (max r u) r u ⟨hr,le_max_left _ _⟩ ⟨hu,le_max_right _ _⟩
  · intro t ht
    exact continuousAt_id.add ((continuousAt_const.sub (hd t).continuousAt).div_const n)
  · simp [envelopeStep]
  · intro t ht htr
    have hg := hm ht.1 hr htr
    have hb := hbound htr.le
    constructor
    · change t < t+(g ν r-g ν t)/n
      exact lt_add_of_pos_right _ (div_pos (sub_pos.mpr hg) hn)
    · change t+(g ν r-g ν t)/n ≤ r
      have hh : (g ν r-g ν t)/n ≤ r-t := (div_le_iff₀ hn).mpr (by nlinarith)
      linarith
  · intro t ht hrt
    have hg := hm hr ht.1 hrt
    have hb := hbound hrt.le
    constructor
    · change r ≤ t+(g ν r-g ν t)/n
      have hh : (g ν t-g ν r)/n ≤ t-r := (div_le_iff₀ hn).mpr (by nlinarith)
      have he : (g ν r-g ν t)/n= -((g ν t-g ν r)/n) := by ring
      rw [he]
      linarith
    · change t+(g ν r-g ν t)/n < t
      exact add_lt_of_neg_right _ (div_neg_of_neg_of_pos (sub_neg.mpr hg) hn)

/-- Convexity puts every Newton/mean-exponent update on or above the selected root. -/
theorem mean_step_above_root (ν : Measure ℝ) [IsFiniteMeasure ν] (m n r t : ℝ)
    (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n) (ht : 0 < deriv (g ν) t) :
    r ≤ meanStep ν (g ν r) t := by
  have hc := convex ν m n hs
  have hd := (analytic ν m n hs t).differentiableAt
  have hbound : deriv (g ν) t*(r-t) ≤ g ν r-g ν t := by
    rcases lt_trichotomy t r with h | h | h
    · have hh := hc.deriv_le_slope (mem_univ t) (mem_univ r) h hd
      rw [slope_def_field] at hh
      exact (le_div_iff₀ (sub_pos.mpr h)).mp hh
    · subst t
      simp
    · have hh := hc.slope_le_deriv (mem_univ r) (mem_univ t) h hd
      rw [slope_def_field] at hh
      have hh' := (div_le_iff₀ (sub_pos.mpr h)).mp hh
      nlinarith
  unfold meanStep
  have hh : r-t ≤ (g ν r-g ν t)/deriv (g ν) t :=
    (le_div_iff₀ ht).mpr (by nlinarith)
  linarith

theorem mean_convergence_from_above (ν : Measure ℝ) [IsFiniteMeasure ν] [NeZero ν]
    (m n a r u : ℝ) (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n)
    (hnd : ¬ ∃ c : ℝ, ∀ᵐ k ∂ν, k=c) (ha : 0 < deriv (g ν) a)
    (hr : a ≤ r) (hu : r ≤ u) :
    Tendsto (fun j : ℕ => (meanStep ν (g ν r))^[j] u) atTop (𝓝 r) := by
  have hmono := mean_strictly_increasing ν m n hs hnd
  have hpos : ∀ t, a ≤ t → 0 < deriv (g ν) t := fun t ht => ha.trans_le (hmono.monotone ht)
  have hg := right_branch_monotone ν m n a hs hnd ha.le
  have hd : AnalyticOnNhd ℝ (g ν) univ := fun x _ => analytic ν m n hs x
  apply IntervalIteration.converge _ r u r u ⟨le_rfl,hu⟩ ⟨hu,le_rfl⟩
  · intro t ht
    exact continuousAt_id.add ((continuousAt_const.sub (analytic ν m n hs t).continuousAt).div
      (hd.deriv t (mem_univ t)).continuousAt (hpos t (hr.trans ht.1)).ne')
  · simp [meanStep]
  · intro t ht htr
    linarith [ht.1]
  · intro t ht hrt
    have htpos := hpos t (hr.trans ht.1)
    refine ⟨mean_step_above_root ν m n r t hs htpos,?_⟩
    have hh := hg hr (hr.trans ht.1) hrt
    exact add_lt_of_neg_right _ (div_neg_of_neg_of_pos (sub_neg.mpr hh) htpos)

/-- From below the first step may overshoot; every subsequent step converges monotonically. -/
theorem mean_convergence (ν : Measure ℝ) [IsFiniteMeasure ν] [NeZero ν]
    (m n a r u : ℝ) (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n)
    (hnd : ¬ ∃ c : ℝ, ∀ᵐ k ∂ν, k=c) (ha : 0 < deriv (g ν) a)
    (hr : a ≤ r) (hu : a ≤ u) :
    Tendsto (fun j : ℕ => (meanStep ν (g ν r))^[j] u) atTop (𝓝 r) := by
  have hpos : 0 < deriv (g ν) u :=
    ha.trans_le ((mean_strictly_increasing ν m n hs hnd).monotone hu)
  have hfirst := mean_step_above_root ν m n r u hs hpos
  have ht := mean_convergence_from_above ν m n a r (meanStep ν (g ν r) u) hs hnd ha hr hfirst
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa only [iterate_succ_apply] using ht

end LeanMath.Papers.ExponentialFamily
