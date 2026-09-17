import LeanMath.Papers.Family
import LeanMath.Papers.CayleyLocal

noncomputable section
namespace LeanMath.Papers.Cayley.Cubic
open Real Filter Set
open scoped Topology

def gap (p y : ℝ) := logCoord (P₁ p y)-logCoord y/p
def factor (p y : ℝ) := 2*(1-p^2)/(p^3*((1-(P₁ p y)^2)*(1-y^2)))
def error (p e : ℝ) := e+log (C₃ p (exp (-p*e)))
def coefficient (p : ℝ) := (p^2-1)/12

theorem polynomial_mem (p y : ℝ) (hp : 1 < p) (hy : y ∈ Ioo (-1) 1) :
    P₁ p y ∈ Ioo (-1) 1 := by
  simpa [truncation] using truncation_mem 0 p y hp hy

theorem polynomial_derivative (p y : ℝ) : HasDerivAt (P₁ p) (a₁ p) y := by
  convert! (hasDerivAt_id y).const_mul (a₁ p) using 1 <;> simp [id_eq]

theorem hasDerivAt_gap (p y : ℝ) (hp : 1 < p) (hy : y ∈ Ioo (-1) 1) :
    HasDerivAt (gap p) (y^2*factor p y) y := by
  have hb := polynomial_mem p y hp hy
  have hd1 : 1-(P₁ p y)^2 ≠ 0 := by nlinarith [hb.1,hb.2]
  have hd2 : 1-y^2 ≠ 0 := by nlinarith [hy.1,hy.2]
  have hp0 : p ≠ 0 := by linarith
  have hd := ((hasDerivAt_logCoord (P₁ p y) hb).comp y
    (polynomial_derivative p y)).sub ((hasDerivAt_logCoord y hy).div_const p)
  convert! hd using 1
  unfold factor
  field_simp [hd1,hd2,hp0]
  simp only [P₁,a₁,a₃]
  field_simp
  <;> ring

theorem factor_continuous (p : ℝ) (hp : 1 < p) : ContinuousAt (factor p) 0 := by
  have hp0 : 0 < p := by linarith
  unfold factor
  apply ContinuousAt.div
  · fun_prop
  · unfold P₁
    fun_prop
  · simp only [P₁,zero_pow (by decide : 3 ≠ 0),zero_pow (by decide : 2 ≠ 0),
      mul_zero,add_zero,sub_zero,mul_one]
    positivity

theorem gap_order (p : ℝ) (hp : 1 < p) :
    Tendsto (fun y : ℝ => gap p y/y^3) (𝓝[≠] 0) (𝓝 (-2*(p^2-1)/(3*p^3))) := by
  have hzero : gap p 0=0 := by simp [gap,logCoord,P₁]
  have hc := (hasDerivAt_gap p 0 hp (by norm_num)).continuousAt
  have hd : ∀ᶠ y in 𝓝[≠] (0:ℝ), HasDerivAt (gap p) (y^2*factor p y) y := by
    have hmem : Ioo (-1:ℝ) 1 ∈ 𝓝 (0:ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
    filter_upwards [mem_nhdsWithin_of_mem_nhds hmem] with y hy
    exact hasDerivAt_gap p y hp hy
  have h := LocalOrder.from_derivative 2 (gap p) (factor p) hzero hc (factor_continuous p hp) hd
  have hp0 : p ≠ 0 := by linarith
  have he : factor p 0 / ((2:ℝ)+1) = -2*(p^2-1)/(3*p^3) := by
    simp only [factor,P₁,a₁,a₃]
    simp only [zero_pow (by decide : 2 ≠ 0),zero_pow (by decide : 3 ≠ 0),
      mul_zero,add_zero,sub_zero,mul_one]
    field_simp
    <;> ring
  simpa only [Nat.cast_ofNat,Nat.reduceAdd,he] using h

theorem error_eq_gap (p e : ℝ) (hp : 1 < p) : error p e=gap p (errorCoordinate p e) := by
  have hR := exp_pos (-p*e)
  have hy := chi_mem (exp (-p*e)) hR
  have hP := polynomial_mem p _ hp hy
  have hp0 : p ≠ 0 := by linarith
  unfold error gap errorCoordinate
  rw [logCoord_eq _ hP,logCoord_eq _ hy,unchi_chi _ hR,log_exp]
  unfold C₃
  field_simp
  <;> ring

theorem coefficient_pos (p : ℝ) (hp : 1 < p) : 0 < coefficient p := by
  have hsq : 0 < p^2-1 := by nlinarith
  have hsq2 : 0 < 3*p^2-2 := by nlinarith
  unfold coefficient
  positivity

/-- Exact order 3, in the root-log error, for every real p>1. -/
theorem exact_order (p : ℝ) (hp : 1 < p) :
    Tendsto (fun e : ℝ => error p e/e^3) (𝓝[≠] 0) (𝓝 (coefficient p)) := by
  have hp0 : p ≠ 0 := by linarith
  have hne : ∀ᶠ e : ℝ in 𝓝[≠] 0, e ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with e he
    exact he
  have hcoord : Tendsto (errorCoordinate p) (𝓝[≠] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [errorCoordinate_zero] using
        (hasDerivAt_errorCoordinate p).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [hne] with e he
      exact errorCoordinate_ne_zero p e hp0 he
  have hslope : Tendsto (fun e : ℝ => errorCoordinate p e/e) (𝓝[≠] 0) (𝓝 (-p/2)) := by
    have he : slope (errorCoordinate p) 0=(fun e : ℝ => errorCoordinate p e/e) := by
      funext e
      simp [slope_def_field,errorCoordinate_zero]
    simpa only [he] using (hasDerivAt_errorCoordinate p).tendsto_slope
  have hprod := ((gap_order p hp).comp hcoord).mul (hslope.pow 3)
  have hconst : (-2*(p^2-1)/(3*p^3))*(-p/2)^3=coefficient p := by
    unfold coefficient
    field_simp
    <;> ring
  rw [hconst] at hprod
  apply hprod.congr'
  filter_upwards [hne] with e he
  have hy := errorCoordinate_ne_zero p e hp0 he
  rw [error_eq_gap p e hp]
  simp only [Function.comp_def]
  field_simp

end LeanMath.Papers.Cayley.Cubic
