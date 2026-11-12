import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

noncomputable section
namespace LeanMath.Papers.LocalOrder
open Filter
open scoped Topology

/-- An exact factored derivative determines the leading local error term.
This is a limit theorem, not a numerical slope estimate. -/
theorem from_derivative (m : ℕ) (f g : ℝ → ℝ) (hf0 : f 0 = 0)
    (hf : ContinuousAt f 0) (hg : ContinuousAt g 0)
    (hd : ∀ᶠ y in 𝓝[≠] (0:ℝ), HasDerivAt f (y^m*g y) y) :
    Tendsto (fun y : ℝ => f y/y^(m+1)) (𝓝[≠] 0) (𝓝 (g 0/(m+1))) := by
  have hn : (m:ℝ)+1 ≠ 0 := by positivity
  have hy : ∀ᶠ y : ℝ in 𝓝[≠] 0, y ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with y h
    exact h
  apply HasDerivAt.lhopital_zero_nhdsNE hd
    (g' := fun y : ℝ => ((m:ℝ)+1)*y^m)
  · apply Eventually.of_forall
    intro y
    convert! (hasDerivAt_id y).pow (m+1) using 1 <;> simp
  · filter_upwards [hy] with y hy
    exact mul_ne_zero hn (pow_ne_zero m hy)
  · simpa only [hf0] using hf.tendsto.mono_left nhdsWithin_le_nhds
  · have hc : ContinuousAt (fun y : ℝ => y^(m+1)) 0 := by fun_prop
    simpa using hc.tendsto.mono_left (show 𝓝[≠] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  · have h := (hg.tendsto.div_const ((m:ℝ)+1)).mono_left
      (show 𝓝[≠] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    apply h.congr'
    filter_upwards [hy] with y hy
    try dsimp
    field_simp

end LeanMath.Papers.LocalOrder
