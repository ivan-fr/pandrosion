import LeanMath.Papers.V14Cell
import Mathlib.Analysis.Analytic.Binomial

/-! The finite-binomial replacement used in §10, in exact arithmetic. -/
noncomputable section
namespace LeanMath.Papers.V14Truncation
open Real Filter Asymptotics Set
open LeanMath.Papers.Cayley LeanMath.Papers.V14Local
open scoped Topology

def truncation (h : ℝ) (n : ℕ) (x : ℝ) :=
  ∑ k ∈ Finset.range (n+1), Ring.choose h k*x^k

/-- The stated O(x^13) remainder is an analytic theorem, not a numerical fit. -/
theorem binomial_remainder (h : ℝ) (n : ℕ) :
    (fun x : ℝ => (1+x)^h-truncation h n x) =O[𝓝 0] (fun x => x^(n+1)) := by
  have hh := (one_add_rpow_hasFPowerSeriesAt_zero (a:=h)).isBigO_sub_partialSum_pow (n+1)
  simpa [truncation,FormalMultilinearSeries.partialSum,binomialSeries,
    FormalMultilinearSeries.ofScalars_apply_eq,Real.norm_eq_abs,← abs_pow,mul_comm] using hh

/-- An analytic increment vanishing at zero transports the truncation order. -/
theorem composed_remainder (h : ℝ) (n : ℕ) (x : ℝ → ℝ)
    (hx : DifferentiableAt ℝ x 0) (hx0 : x 0=0) :
    (fun y : ℝ => (1+x y)^h-truncation h n (x y)) =O[𝓝 0] (fun y => y^(n+1)) := by
  have ht : Tendsto x (𝓝 0) (𝓝 0) := by simpa only [hx0] using hx.continuousAt.tendsto
  have hb : x =O[𝓝 0] (fun y : ℝ => y) := by
    simpa only [hx0,sub_zero] using hx.hasDerivAt.isBigO_sub
  exact ((binomial_remainder h n).comp_tendsto ht).trans (hb.pow (n+1))

def increment (p y : ℝ) := (-4*y/p)/((1-LeanMath.Papers.V14Defect.a p*y)*(1+y))

theorem increment_zero (p : ℝ) : increment p 0=0 := by simp [increment]

theorem increment_differentiable (p : ℝ) : DifferentiableAt ℝ (increment p) 0 := by
  unfold increment
  fun_prop (disch := norm_num)

theorem implemented_base_remainder (p : ℝ) :
    (fun y : ℝ => (1+increment p y)^((p-1)/2)-truncation ((p-1)/2) 12 (increment p y))
      =O[𝓝 0] (fun y => y^13) :=
  composed_remainder _ 12 _ (increment_differentiable p) (increment_zero p)

theorem base_perturbation_below_order_eleven (p : ℝ) :
    (fun y : ℝ => (1+increment p y)^((p-1)/2)-truncation ((p-1)/2) 12 (increment p y))
      =o[𝓝 0] (fun y => y^11) :=
  (implemented_base_remainder p).trans_isLittleO (isLittleO_pow_pow (by decide : 11 < 13))

theorem increment_identity (p y : ℝ) (hp : 2 < p) (hy : y ∈ Ioo (-1) 1) :
    1+increment p y = unchi (LeanMath.Papers.V14Defect.a p*y)/unchi y := by
  have hm := LeanMath.Papers.V14Defect.scaled_mem p y hp hy
  have hp0 : p ≠ 0 := by linarith
  have h1 : 1-LeanMath.Papers.V14Defect.a p*y ≠ 0 := by linarith [hm.2]
  have h2 : 1+y ≠ 0 := by linarith [hy.1]
  have h3 : 1-y ≠ 0 := by linarith [hy.2]
  have he : -4*y/p = 2*(LeanMath.Papers.V14Defect.a p-1)*y := by
    unfold LeanMath.Papers.V14Defect.a
    field_simp
    <;> ring
  unfold increment
  rw [he]
  unfold unchi
  field_simp [h1,h2,h3]
  <;> ring

/-- Equation 10.1 for the exact geometric center. -/
theorem stable_center (p y : ℝ) (hp : 2 < p) (hy : y ∈ Ioo (-1) 1) :
    LeanMath.Papers.RealBracket.center p (unchi y) = unchi y*(1+increment p y)^((p-1)/2) := by
  have hR := unchi_pos y hy
  have hm := LeanMath.Papers.V14Defect.scaled_mem p y hp hy
  have hb : 0 < 1+increment p y := by
    rw [increment_identity p y hp hy]; exact div_pos (unchi_pos _ hm) hR
  apply log_injOn_pos (LeanMath.Papers.RealBracket.center_pos p _ (by linarith) hR)
    (mul_pos hR (rpow_pos_of_pos hb _))
  rw [LeanMath.Papers.V14Defect.log_center_coordinate p y hp hy,
    log_mul hR.ne' (rpow_pos_of_pos hb _).ne',log_rpow hb,
    increment_identity p y hp hy,log_div (unchi_pos _ hm).ne' hR.ne',
    LeanMath.Papers.V14Defect.log_unchi y hy,LeanMath.Papers.V14Defect.log_unchi _ hm]
  ring

theorem truncation_zero (h : ℝ) (n : ℕ) : truncation h n 0=1 := by
  unfold truncation
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k hk hk0; simp [zero_pow hk0]
  · simp

theorem truncation_continuous (h : ℝ) (n : ℕ) : Continuous (truncation h n) := by
  unfold truncation
  fun_prop

/-- Taking logarithms preserves the thirteenth-order remainder near the unit base. -/
theorem logarithmic_remainder (p : ℝ) :
    (fun y : ℝ => log (truncation ((p-1)/2) 12 (increment p y))-
      log ((1+increment p y)^((p-1)/2))) =O[𝓝 0] (fun y => y^13) := by
  have hx : Tendsto (increment p) (𝓝 0) (𝓝 0) := by
    simpa only [increment_zero] using (increment_differentiable p).continuousAt.tendsto
  have ht : Tendsto (fun y => truncation ((p-1)/2) 12 (increment p y)) (𝓝 0) (𝓝 1) := by
    simpa only [truncation_zero,Function.comp_def] using
      (truncation_continuous ((p-1)/2) 12).continuousAt.tendsto.comp hx
  have hb : Tendsto (fun y => (1+increment p y)^((p-1)/2)) (𝓝 0) (𝓝 1) := by
    have h := (continuousAt_rpow_const 1 ((p-1)/2) (Or.inl one_ne_zero)).tendsto.comp (show Tendsto (fun y => 1+increment p y) (𝓝 0) (𝓝 1) by simpa using hx.const_add 1)
    simpa only [add_zero,one_rpow,Function.comp_def] using h
  have hl := (hasStrictDerivAt_log (by norm_num : (1:ℝ) ≠ 0)).hasStrictFDerivAt.isBigO_sub
  have hc := hl.comp_tendsto (ht.prodMk_nhds hb)
  have hd := (implemented_base_remainder p).neg_left
  have hd' : (fun y : ℝ => truncation ((p-1)/2) 12 (increment p y)-
      (1+increment p y)^((p-1)/2)) =O[𝓝 0] (fun y => y^13) := by
    simpa only [neg_sub] using hd
  exact hc.trans hd'

/-- Log error of the binomial implementation, expressed as the exact error plus
its replacement of the center's power factor. -/
def implementedError (p e : ℝ) := rootLogError .eleven p e +
  log (truncation ((p-1)/2) 12 (increment p (errorCoordinate p e)))-
  log ((1+increment p (errorCoordinate p e))^((p-1)/2))

theorem implemented_local_order (p : ℝ) (hp : 2 < p) :
    Tendsto (fun e : ℝ => implementedError p e/e^11) (𝓝[≠] 0)
      (𝓝 (LeanMath.Papers.V14Coefficients.q11 (LeanMath.Papers.V14Defect.a p)*p^11/2^10)) := by
  have hx := hasDerivAt_errorCoordinate p
  have ht : Tendsto (errorCoordinate p) (𝓝 0) (𝓝 0) := by
    simpa only [errorCoordinate_zero] using hx.continuousAt.tendsto
  have hO : errorCoordinate p =O[𝓝 0] (fun e : ℝ => e) := by
    simpa only [errorCoordinate_zero,sub_zero] using hx.isBigO_sub
  have hd := ((logarithmic_remainder p).comp_tendsto ht).trans (hO.pow 13)
  have hl := hd.trans_isLittleO (isLittleO_pow_pow (by decide : 11 < 13))
  have hz := hl.tendsto_div_nhds_zero.mono_left (show 𝓝[≠] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hf := exact_local_order .eleven p hp
  have hsum := hf.add hz
  simp only [order,coefficient,add_zero] at hsum
  convert! hsum using 1
  funext e
  unfold implementedError
  simp only [Function.comp_apply]
  ring

def implementedCorrection (p R : ℝ) := R*
  truncation ((p-1)/2) 12 (increment p (chi R))*
  unchi (Q .eleven (LeanMath.Papers.V14Defect.a p) (chi R))

/-- The error used above is exactly that of the finite-binomial multiplicative update. -/
theorem implemented_error_eq (p e : ℝ) (hp : 3 ≤ p)
    (he : |e| ≤ LeanMath.Papers.RealBracket.Local.radius p)
    (hT : 0 < truncation ((p-1)/2) 12 (increment p (errorCoordinate p e))) :
    implementedError p e = e+log (implementedCorrection p (exp (-p*e))) := by
  have hR := exp_pos (-p*e)
  have hy := chi_mem (exp (-p*e)) hR
  have hm := LeanMath.Papers.V14Defect.scaled_mem p _ (by linarith) hy
  have ha := LeanMath.Papers.V14Defect.a_mem p (by linarith)
  have hq := unchi_pos _ (LeanMath.Papers.V14Cell.Q_mem .eleven _ _ ha.1 ha.2
    (LeanMath.Papers.V14Cell.coordinate_small p e hp he))
  have hb : 0 < 1+increment p (errorCoordinate p e) := by
    unfold errorCoordinate
    rw [increment_identity p _ (by linarith) hy]
    exact div_pos (unchi_pos _ hm) (unchi_pos _ hy)
  have hc := stable_center p _ (by linarith) hy
  rw [unchi_chi _ hR] at hc
  unfold implementedError rootLogError correction implementedCorrection
  simp only [errorCoordinate] at hT hb hq ⊢
  rw [hc,log_mul (mul_pos hR (rpow_pos_of_pos hb _)).ne' hq.ne',
    log_mul hR.ne' (rpow_pos_of_pos hb _).ne',
    log_mul (mul_pos hR hT).ne' hq.ne',log_mul hR.ne' hT.ne']
  ring

/-- Section 10: the actual finite-binomial update retains the exact eleventh-order constant. -/
theorem finite_binomial_order_eleven (p : ℝ) (hp : 3 ≤ p) :
    Tendsto (fun e : ℝ => (e+log (implementedCorrection p (exp (-p*e))))/e^11)
      (𝓝[≠] 0) (𝓝 (LeanMath.Papers.V14Coefficients.q11 (LeanMath.Papers.V14Defect.a p)*p^11/2^10)) := by
  have hx : Tendsto (fun e => increment p (errorCoordinate p e)) (𝓝 0) (𝓝 0) := by
    have h1 : Tendsto (increment p) (𝓝 0) (𝓝 0) := by
      simpa only [increment_zero] using (increment_differentiable p).continuousAt.tendsto
    have h2 : Tendsto (errorCoordinate p) (𝓝 0) (𝓝 0) := by
      simpa only [errorCoordinate_zero] using (hasDerivAt_errorCoordinate p).continuousAt.tendsto
    exact h1.comp h2
  have ht : Tendsto (fun e => truncation ((p-1)/2) 12 (increment p (errorCoordinate p e)))
      (𝓝 0) (𝓝 1) := by
    simpa only [truncation_zero,Function.comp_def] using
      (truncation_continuous ((p-1)/2) 12).continuousAt.tendsto.comp hx
  have hT : ∀ᶠ e : ℝ in 𝓝 0, 0 < truncation ((p-1)/2) 12 (increment p (errorCoordinate p e)) :=
    (tendsto_order.mp ht).1 0 (by norm_num)
  have he : ∀ᶠ e : ℝ in 𝓝 0, |e| ≤ LeanMath.Papers.RealBracket.Local.radius p := by
    have hr := LeanMath.Papers.RealBracket.Local.radius_pos p (by linarith)
    filter_upwards [Ioo_mem_nhds (show -LeanMath.Papers.RealBracket.Local.radius p < 0 by linarith) hr] with e he
    exact (abs_lt.mpr he).le
  apply (implemented_local_order p (by linarith)).congr'
  filter_upwards [hT.filter_mono nhdsWithin_le_nhds,he.filter_mono nhdsWithin_le_nhds] with e hT he
  rw [implemented_error_eq p e hp he hT]

end LeanMath.Papers.V14Truncation
