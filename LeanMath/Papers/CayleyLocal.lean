import LeanMath.Papers.Comparison
import LeanMath.Papers.LocalOrder
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope

noncomputable section
namespace LeanMath.Papers.Cayley
open Real Filter Set
open scoped Topology

def gapFactor (p y : ℝ) :=
  2*(p^2-1)*B p (y^2)/(225*p^11*((1-(P₅ p y)^2)*(1-y^2)))

theorem hasDerivAt_logGap_factor (p y : ℝ) (hp : 1 < p) (hy : y ∈ Ioo (-1) 1) :
    HasDerivAt (logGap p) (y^6*gapFactor p y) y := by
  have hb := P₅_mem p y hp hy
  have hd1 : 1-(P₅ p y)^2 ≠ 0 := by nlinarith [hb.1,hb.2]
  have hd2 : 1-y^2 ≠ 0 := by nlinarith [hy.1,hy.2]
  have hp0 : p ≠ 0 := by linarith
  convert hasDerivAt_logGap_all p y hp hy using 1
  have he :
      2/(1-(P₅ p y)^2)*(a₁ p+3*a₃ p*y^2+5*a₅ p*y^4) - (2/(1-y^2))/p =
      2*((1-y^2)*(a₁ p+3*a₃ p*y^2+5*a₅ p*y^4)-(1/p)*(1-(P₅ p y)^2)) /
        ((1-(P₅ p y)^2)*(1-y^2)) := by field_simp
  rw [he,residual_identity p y hp0]
  unfold gapFactor
  field_simp
  <;> ring

theorem continuousAt_gapFactor (p : ℝ) (hp : 1 < p) : ContinuousAt (gapFactor p) 0 := by
  have hp0 : 0 < p := by linarith
  unfold gapFactor
  apply ContinuousAt.div
  · unfold B
    fun_prop
  · unfold P₅
    fun_prop
  · simp only [P₅,zero_pow (by decide : 3 ≠ 0),zero_pow (by decide : 5 ≠ 0),
      mul_zero,add_zero,zero_pow (by decide : 2 ≠ 0),sub_zero,mul_one]
    positivity

/-- Leading error coefficient in the Cayley coordinate. -/
theorem gap_order_seven (p : ℝ) (hp : 1 < p) :
    Tendsto (fun y : ℝ => logGap p y/y^7) (𝓝[≠] 0)
      (𝓝 (-2*(p^2-1)*(45*p^4-53*p^2+17)/(315*p^7))) := by
  have hzero : logGap p 0=0 := by simp [logGap,logCoord,P₅]
  have hc := (hasDerivAt_logGap_factor p 0 hp (by norm_num)).continuousAt
  have hd : ∀ᶠ y in 𝓝[≠] (0:ℝ), HasDerivAt (logGap p) (y^6*gapFactor p y) y := by
    have hmem : Ioo (-1:ℝ) 1 ∈ 𝓝 (0:ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
    filter_upwards [mem_nhdsWithin_of_mem_nhds hmem] with y hy
    exact hasDerivAt_logGap_factor p y hp hy
  have h := LocalOrder.from_derivative 6 (logGap p) (gapFactor p) hzero hc
    (continuousAt_gapFactor p hp) hd
  have hp0 : p ≠ 0 := by linarith
  have he : gapFactor p 0 / ((6:ℝ)+1) =
      -2*(p^2-1)*(45*p^4-53*p^2+17)/(315*p^7) := by
    unfold gapFactor B P₅
    simp only [zero_pow (by decide : 2 ≠ 0),zero_pow (by decide : 3 ≠ 0),
      zero_pow (by decide : 5 ≠ 0),mul_zero,add_zero,sub_zero,mul_one]
    field_simp
    <;> ring
  simpa only [Nat.cast_ofNat, Nat.reduceAdd, he] using h

def errorCoordinate (p e : ℝ) := chi (exp (-p*e))
def logError (p e : ℝ) := e + log (C₇ p (exp (-p*e)))

theorem errorCoordinate_zero (p : ℝ) : errorCoordinate p 0 = 0 := by simp [errorCoordinate,chi]

theorem hasDerivAt_errorCoordinate (p : ℝ) : HasDerivAt (errorCoordinate p) (-p/2) 0 := by
  have hd := ((hasDerivAt_id (0:ℝ)).const_mul (-p)).exp
  convert! (hd.sub_const 1).div (hd.add_const 1) (by norm_num) using 1
  norm_num
  ring

theorem errorCoordinate_ne_zero (p e : ℝ) (hp : p ≠ 0) (he : e ≠ 0) :
    errorCoordinate p e ≠ 0 := by
  unfold errorCoordinate chi
  apply div_ne_zero
  · intro h
    have hh : exp (-p*e)=1 := sub_eq_zero.mp h
    rw [exp_eq_one_iff] at hh
    exact (mul_ne_zero (neg_ne_zero.mpr hp) he) hh
  · linarith [exp_pos (-p*e)]

theorem logError_eq_gap (p e : ℝ) (hp : 1 < p) :
    logError p e = logGap p (errorCoordinate p e) := by
  have hR : 0 < exp (-p*e) := exp_pos _
  have hy := chi_mem (exp (-p*e)) hR
  have hP := P₅_mem p _ hp hy
  have hp0 : p ≠ 0 := by linarith
  unfold logError logGap errorCoordinate
  rw [logCoord_eq _ hP, logCoord_eq _ hy, unchi_chi _ hR,log_exp]
  unfold C₇
  field_simp
  <;> ring

def kappa₇ (p : ℝ) := (p^2-1)*(45*p^4-53*p^2+17)/20160

theorem kappa₇_pos (p : ℝ) (hp : 1 < p) : 0 < kappa₇ p := by
  have hs : 0 < p^2-1 := by nlinarith
  have he : 45*p^4-53*p^2+17 = 45*(p^2-1)^2+37*(p^2-1)+9 := by ring
  unfold kappa₇
  rw [he]
  positivity

/-- Exact seventh local order in the root-log error, with the printed nonzero
coefficient, for every real degree p>1. -/
theorem exact_order_seven (p : ℝ) (hp : 1 < p) :
    Tendsto (fun e : ℝ => logError p e/e^7) (𝓝[≠] 0) (𝓝 (kappa₇ p)) := by
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
    have he : slope (errorCoordinate p) 0 = (fun e : ℝ => errorCoordinate p e/e) := by
      funext e
      simp [slope_def_field,errorCoordinate_zero]
    simpa only [he] using (hasDerivAt_errorCoordinate p).tendsto_slope
  have hprod := ((gap_order_seven p hp).comp hcoord).mul (hslope.pow 7)
  have hconst : (-2*(p^2-1)*(45*p^4-53*p^2+17)/(315*p^7)) * (-p/2)^7 = kappa₇ p := by
    unfold kappa₇
    field_simp
    <;> ring
  rw [hconst] at hprod
  apply hprod.congr'
  filter_upwards [hne] with e he
  have hy := errorCoordinate_ne_zero p e hp0 he
  rw [logError_eq_gap p e hp]
  simp only [Function.comp_def]
  field_simp

end LeanMath.Papers.Cayley
