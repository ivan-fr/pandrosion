import LeanMath.Papers.V14Comparison
import LeanMath.Papers.CayleyLocal

/-! Exact local orders 5,7,9,11, obtained from factored derivatives. -/
noncomputable section
namespace LeanMath.Papers.V14Local
open Real Filter Set
open scoped Topology
open LeanMath.Papers.V14Coefficients LeanMath.Papers.V14Comparison LeanMath.Papers.Cayley

inductive Index | five | seven | nine | eleven deriving DecidableEq

def order : Index → ℕ | .five => 5 | .seven => 7 | .nine => 9 | .eleven => 11

def coefficient (i : Index) (a : ℝ) := match i with
  | .five => q5 a | .seven => q7 a | .nine => q9 a | .eleven => q11 a

def Q (i : Index) (a y : ℝ) := match i with
  | .five => Q3 a y | .seven => Q5 a y | .nine => Q7 a y | .eleven => Q9 a y

def Qprime (i : Index) (a y : ℝ) := match i with
  | .five => 3*q3 a*y^2
  | .seven => 3*q3 a*y^2+5*q5 a*y^4
  | .nine => 3*q3 a*y^2+5*q5 a*y^4+7*q7 a*y^6
  | .eleven => Q9prime a y

def tailFactor (i : Index) (a y : ℝ) := match i with
  | .five => -5*q5 a+3*a^2*q3 a*y^2+c a*(q3 a)^2*y^4
  | .seven => -7*q7 a+(5*a^2*q5 a+c a*(q3 a)^2)*y^2+
      2*c a*q3 a*q5 a*y^4+c a*(q5 a)^2*y^6
  | .nine => -9*q9 a+(7*a^2*q7 a+2*c a*q3 a*q5 a)*y^2+
      c a*(2*q3 a*q7 a+(q5 a)^2)*y^4+2*c a*q5 a*q7 a*y^6+c a*(q7 a)^2*y^8
  | .eleven => -11*q11 a+(9*a^2*q9 a+c a*(2*q3 a*q7 a+(q5 a)^2))*y^2+
      c a*(2*q3 a*q9 a+2*q5 a*q7 a)*y^4+
      c a*(2*q5 a*q9 a+(q7 a)^2)*y^6+2*c a*q7 a*q9 a*y^8+c a*(q9 a)^2*y^10

def errorGap (i : Index) (a y : ℝ) := logCoord (Q i a y)-delta a y

def factor (i : Index) (a y : ℝ) :=
  2*tailFactor i a y/((1-(Q i a y)^2)*(1-y^2)*(1-a^2*y^2))

theorem Q_zero (i : Index) (a : ℝ) : Q i a 0 = 0 := by
  cases i <;> simp [Q,Q3,Q5,Q7,Q9]

theorem Q_odd (i : Index) (a y : ℝ) : Q i a (-y) = -Q i a y := by
  cases i <;> simp only [Q,Q3,Q5,Q7,Q9] <;> ring

theorem Q_continuous (i : Index) (a : ℝ) : Continuous (Q i a) := by
  cases i <;> unfold Q Q9 Q7 Q5 Q3 <;> fun_prop

theorem coefficient_pos (i : Index) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    0 < coefficient i a := by
  obtain ⟨_,h5,h7,h9,h11⟩ := coefficients_positive a ha0 ha1
  cases i <;> assumption

theorem hasDerivAt_Q (i : Index) (a y : ℝ) : HasDerivAt (Q i a) (Qprime i a y) y := by
  cases i with
  | five =>
    convert! ((hasDerivAt_id y).pow 3).const_mul (q3 a) using 1
    simp [Qprime]; ring
  | seven =>
    convert! (((hasDerivAt_id y).pow 3).const_mul (q3 a)).add
      (((hasDerivAt_id y).pow 5).const_mul (q5 a)) using 1
    simp [Qprime]; ring
  | nine =>
    convert! ((((hasDerivAt_id y).pow 3).const_mul (q3 a)).add
      (((hasDerivAt_id y).pow 5).const_mul (q5 a))).add
      (((hasDerivAt_id y).pow 7).const_mul (q7 a)) using 1
    simp [Qprime]; ring
  | eleven => exact hasDerivAt_Q9 a y

/-- All four exact differential residual factorizations. -/
theorem residual_factorization (i : Index) (a y : ℝ) :
    (1-y^2)*(1-a^2*y^2)*Qprime i a y-c a*y^2*(1-(Q i a y)^2) =
      y^(order i-1)*tailFactor i a y := by
  cases i <;> simp only [Q, Qprime, tailFactor, order, Q9, Q7, Q5, Q3, Q9prime,
    q3, q5, q7, q9, q11, d3, d5, d7, d9, d11, c] <;> norm_num <;> ring

theorem gap_derivative (i : Index) (a y : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (hy : y ∈ Ioo (-1) 1) (hQ : Q i a y ∈ Ioo (-1) 1) :
    HasDerivAt (errorGap i a) (y^(order i-1)*factor i a y) y := by
  have hay := scaled_mem a y ha0 ha1 hy
  have hd : 1-y^2 ≠ 0 := by nlinarith [hy.1,hy.2]
  have hd' : 1-a^2*y^2 ≠ 0 := by nlinarith [hay.1,hay.2]
  have hd'' : 1-y^2*a^2 ≠ 0 := by nlinarith [hay.1,hay.2]
  have hqd : 1-(Q i a y)^2 ≠ 0 := by nlinarith [hQ.1,hQ.2]
  convert! ((hasDerivAt_logCoord _ hQ).comp y (hasDerivAt_Q i a y)).sub
    (hasDerivAt_delta a y ha0 ha1 hy) using 1
  have he : 2/(1-(Q i a y)^2)*Qprime i a y-2*c a*y^2/((1-y^2)*(1-a^2*y^2)) =
      2*((1-y^2)*(1-a^2*y^2)*Qprime i a y-c a*y^2*(1-(Q i a y)^2))/
        ((1-(Q i a y)^2)*(1-y^2)*(1-a^2*y^2)) := by
    field_simp [hd,hd',hd'',hqd]
    <;> ring
  rw [he,residual_factorization]
  unfold factor
  ring

theorem factor_continuous (i : Index) (a : ℝ) : ContinuousAt (factor i a) 0 := by
  unfold factor
  apply ContinuousAt.div
  · cases i <;> unfold tailFactor <;> fun_prop
  · exact (((continuous_const.sub ((Q_continuous i a).pow 2)).mul
      (continuous_const.sub (continuous_id.pow 2))).mul
      (continuous_const.sub (continuous_const.mul (continuous_id.pow 2)))).continuousAt
  · simp [Q_zero]

/-- The local coefficient in y; no Taylor remainder is assumed. -/
theorem coordinate_order (i : Index) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    Tendsto (fun y : ℝ => errorGap i a y/y^(order i)) (𝓝[≠] 0)
      (𝓝 (-2*coefficient i a)) := by
  have hy : ∀ᶠ y : ℝ in 𝓝 (0:ℝ), y ∈ Ioo (-1) 1 := Ioo_mem_nhds (by norm_num) (by norm_num)
  have hQ : ∀ᶠ y : ℝ in 𝓝 (0:ℝ), Q i a y ∈ Ioo (-1) 1 :=
    (Q_continuous i a).continuousAt (by simpa [Q_zero] using (Ioo_mem_nhds (by norm_num : (-1:ℝ)<0) (by norm_num : (0:ℝ)<1)))
  have hzero : errorGap i a 0 = 0 := by simp [errorGap,Q_zero,delta,logCoord]
  have hc := (gap_derivative i a 0 ha0 ha1 (by norm_num) (by simp [Q_zero])).continuousAt
  have hd : ∀ᶠ y in 𝓝[≠] (0:ℝ), HasDerivAt (errorGap i a) (y^(order i-1)*factor i a y) y := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds hy,mem_nhdsWithin_of_mem_nhds hQ] with y hy hQ
    exact gap_derivative i a y ha0 ha1 hy hQ
  have h := LeanMath.Papers.LocalOrder.from_derivative (order i-1)
    (errorGap i a) (factor i a) hzero hc (factor_continuous i a) hd
  have hn : order i-1+1=order i := by cases i <;> rfl
  have hv : factor i a 0/((order i-1:ℕ)+1:ℝ) = -2*coefficient i a := by
    cases i <;> simp [factor,tailFactor,Q_zero,order,coefficient] <;> ring
  simpa only [hn,hv] using h


/-- The actual center-based correction from Equation 9.10. -/
def correction (i : Index) (p R : ℝ) :=
  LeanMath.Papers.RealBracket.center p R * unchi (Q i (V14Defect.a p) (chi R))

def rootLogError (i : Index) (p e : ℝ) := e+log (correction i p (exp (-p*e)))

theorem correction_reciprocal (i : Index) (p R : ℝ) (hp : 2 < p) (hR : 0 < R) :
    correction i p R⁻¹ = (correction i p R)⁻¹ := by
  unfold correction
  rw [LeanMath.Papers.RealBracket.center_reciprocal p R (by linarith) hR,
    chi_inv R hR,Q_odd,unchi_neg,mul_inv_rev]
  ring

theorem error_eq_gap (i : Index) (p e : ℝ) (hp : 2 < p)
    (hQ : Q i (V14Defect.a p) (errorCoordinate p e) ∈ Ioo (-1) 1) :
    rootLogError i p e = errorGap i (V14Defect.a p) (errorCoordinate p e) := by
  have hR := exp_pos (-p*e)
  have hy := chi_mem _ hR
  have hg := LeanMath.Papers.RealBracket.center_pos p _ (by linarith) hR
  have hdelta := delta_eq_defect p (errorCoordinate p e) hp hy
  unfold V14Defect.defect errorCoordinate at hdelta
  rw [unchi_chi _ hR,log_div (rpow_pos_of_pos hR _).ne' hg.ne',
    log_rpow hR,log_exp] at hdelta
  have hp0 : p ≠ 0 := by linarith
  have he : 1/p*(-p*e) = -e := by field_simp
  rw [he] at hdelta
  unfold rootLogError correction errorGap errorCoordinate at *
  rw [log_mul hg.ne' (unchi_pos _ hQ).ne',← logCoord_eq _ hQ, hdelta]
  ring

/-- Theorem 9.3: the exact local orders in the original logarithmic root error. -/
theorem exact_local_order (i : Index) (p : ℝ) (hp : 2 < p) :
    Tendsto (fun e : ℝ => rootLogError i p e/e^(order i)) (𝓝[≠] 0)
      (𝓝 (coefficient i (V14Defect.a p)*p^(order i)/2^(order i-1))) := by
  have hp0 : p ≠ 0 := by linarith
  have ha := V14Defect.a_mem p hp
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
  have hprod := ((coordinate_order i _ ha.1 ha.2).comp hcoord).mul (hslope.pow (order i))
  have hconst : (-2*coefficient i (V14Defect.a p))*(-p/2)^(order i) =
      coefficient i (V14Defect.a p)*p^(order i)/2^(order i-1) := by
    cases i <;> norm_num [order] <;> ring
  rw [hconst] at hprod
  have hc := (Q_continuous i (V14Defect.a p)).continuousAt.comp
    (hasDerivAt_errorCoordinate p).continuousAt
  have hQ : ∀ᶠ e : ℝ in 𝓝 (0:ℝ),
      Q i (V14Defect.a p) (errorCoordinate p e) ∈ Ioo (-1) 1 := by
    apply hc
    change Ioo (-1) 1 ∈ 𝓝 (Q i (V14Defect.a p) (errorCoordinate p 0))
    rw [errorCoordinate_zero,Q_zero]
    exact Ioo_mem_nhds (by norm_num) (by norm_num)
  apply hprod.congr'
  filter_upwards [hne,mem_nhdsWithin_of_mem_nhds hQ] with e he hQ
  have hy := errorCoordinate_ne_zero p e hp0 he
  rw [error_eq_gap i p e hp hQ]
  simp only [Function.comp_def]
  rw [div_pow]
  field_simp

/-- The limit in Theorem 9.3 is nonzero for all four methods and every p>2. -/
theorem local_constant_positive (i : Index) (p : ℝ) (hp : 2 < p) :
    0 < coefficient i (V14Defect.a p)*p^(order i)/2^(order i-1) := by
  have ha := V14Defect.a_mem p hp
  have hq := coefficient_pos i _ ha.1 ha.2
  have hp0 : 0 < p := by linarith
  positivity

end LeanMath.Papers.V14Local
