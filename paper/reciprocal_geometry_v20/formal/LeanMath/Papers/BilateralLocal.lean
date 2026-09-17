import LeanMath.Papers.Bilateral
import LeanMath.Papers.LocalOrder

noncomputable section
namespace LeanMath.Papers.RealBracket.Local
open Real Filter Set
open scoped Topology

def shiftedGap (p d : ℝ) := gap p (1+d)
def factor (p d : ℝ) := -(p-1)^2*(p-2)/(2*p*(1+d)*((p-1)*(1+d)+1)*(1+d+p-1))
def coordinate (p e : ℝ) := exp (-p*e)-1
def error (p e : ℝ) := e+log (center p (exp (-p*e)))
def coefficient (p : ℝ) := (p-1)^2*(p-2)/6

theorem shiftedGap_zero (p : ℝ) : shiftedGap p 0=0 := by simp [shiftedGap,gap_one]

theorem derivative (p d : ℝ) (hp : 1 < p) (hd : -1 < d) :
    HasDerivAt (shiftedGap p) (d^2*factor p d) d := by
  convert! (hasDerivAt_gap p (1+d) hp (by linarith)).comp d
    ((hasDerivAt_id d).const_add 1) using 1
  simp only [mul_one]
  unfold factor
  ring

theorem factor_continuous (p : ℝ) (hp : 1 < p) : ContinuousAt (factor p) 0 := by
  unfold factor
  apply ContinuousAt.div
  · fun_prop
  · fun_prop
  · simp only [add_zero,mul_one,sub_add_cancel]
    have hp0 : 0 < p := by linarith
    have : 0 < p-1+1 := by linarith
    have : 0 < 1+p-1 := by linarith
    positivity

theorem gap_order (p : ℝ) (hp : 1 < p) :
    Tendsto (fun d : ℝ => shiftedGap p d/d^3) (𝓝[≠] 0)
      (𝓝 (-(p-1)^2*(p-2)/(6*p^3))) := by
  have hd : ∀ᶠ d in 𝓝[≠] (0:ℝ), HasDerivAt (shiftedGap p) (d^2*factor p d) d := by
    have hm : Ioi (-1:ℝ) ∈ 𝓝 (0:ℝ) := Ioi_mem_nhds (by norm_num)
    filter_upwards [mem_nhdsWithin_of_mem_nhds hm] with d hd
    exact derivative p d hp hd
  have h := LocalOrder.from_derivative 2 (shiftedGap p) (factor p) (shiftedGap_zero p)
    (derivative p 0 hp (by norm_num)).continuousAt (factor_continuous p hp) hd
  have he : factor p 0 / ((2:ℝ)+1)= -(p-1)^2*(p-2)/(6*p^3) := by
    unfold factor
    ring
  simpa only [Nat.cast_ofNat,Nat.reduceAdd,he] using h

theorem coordinate_zero (p : ℝ) : coordinate p 0=0 := by simp [coordinate]

theorem coordinate_derivative (p : ℝ) : HasDerivAt (coordinate p) (-p) 0 := by
  convert! (((hasDerivAt_id (0:ℝ)).const_mul (-p)).exp).sub_const 1 using 1 <;> simp

theorem coordinate_ne_zero (p e : ℝ) (hp : p ≠ 0) (he : e ≠ 0) : coordinate p e ≠ 0 := by
  simp only [coordinate,ne_eq,sub_eq_zero,exp_eq_one_iff,mul_eq_zero,neg_eq_zero]
  exact not_or_intro hp he

theorem error_eq_gap (p e : ℝ) (hp : 1 < p) : error p e=shiftedGap p (coordinate p e) := by
  have hp0 : p ≠ 0 := by linarith
  unfold error shiftedGap coordinate gap
  rw [show 1+(exp (-p*e)-1)=exp (-p*e) by ring]
  rw [log_center p _ hp (exp_pos _), log_exp]
  field_simp
  <;> ring

theorem exact_cubic_limit (p : ℝ) (hp : 1 < p) :
    Tendsto (fun e : ℝ => error p e/e^3) (𝓝[≠] 0) (𝓝 (coefficient p)) := by
  have hp0 : p ≠ 0 := by linarith
  have hne : ∀ᶠ e : ℝ in 𝓝[≠] 0, e ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with e he
    exact he
  have hc : Tendsto (coordinate p) (𝓝[≠] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [coordinate_zero] using
        (coordinate_derivative p).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [hne] with e he
      exact coordinate_ne_zero p e hp0 he
  have hs : Tendsto (fun e : ℝ => coordinate p e/e) (𝓝[≠] 0) (𝓝 (-p)) := by
    have he : slope (coordinate p) 0=(fun e : ℝ => coordinate p e/e) := by
      funext e
      simp [slope_def_field,coordinate_zero]
    simpa only [he] using (coordinate_derivative p).tendsto_slope
  have h := ((gap_order p hp).comp hc).mul (hs.pow 3)
  have he : (-(p-1)^2*(p-2)/(6*p^3))*(-p)^3=coefficient p := by
    unfold coefficient
    field_simp
    <;> ring
  rw [he] at h
  apply h.congr'
  filter_upwards [hne] with e he
  have hy := coordinate_ne_zero p e hp0 he
  rw [error_eq_gap p e hp]
  simp only [Function.comp_def]
  field_simp

theorem coefficient_pos (p : ℝ) (hp : 2 < p) : 0 < coefficient p := by
  have h1 : 0 < p-1 := by linarith
  have h2 : 0 < p-2 := by linarith
  unfold coefficient
  positivity

theorem coefficient_neg (p : ℝ) (hp : 1 < p) (hp2 : p < 2) : coefficient p < 0 := by
  have h1 : 0 < (p-1)^2 := sq_pos_of_pos (by linarith)
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg h1 (by linarith)) (by norm_num)

end LeanMath.Papers.RealBracket.Local
