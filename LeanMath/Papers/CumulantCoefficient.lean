import LeanMath.Papers.CumulantOrder
import LeanMath.Papers.AnalyticLimitFactor

noncomputable section
namespace LeanMath.Papers.CumulantCoefficient
open Polynomial Real
open SeriesReversion AnalyticReversion

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem product_coefficient_seven (P Q : Polynomial ℝ) :
    (P*Q).coeff 7=P.coeff 0*Q.coeff 7+P.coeff 1*Q.coeff 6+P.coeff 2*Q.coeff 5+
      P.coeff 3*Q.coeff 4+P.coeff 4*Q.coeff 3+P.coeff 5*Q.coeff 2+P.coeff 6*Q.coeff 1+P.coeff 7*Q.coeff 0 := by
  rw [Polynomial.coeff_mul]
  norm_num [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,Finset.sum_range_succ]
  <;> ring

theorem composition_seventh (u v w x y z a b c d e f : ℝ) :
    ((jet u v w x y z).comp (jet a b c d e f)).coeff 7=
      v*(2*a*f+2*b*e+2*c*d)+w*(3*a^2*e+6*a*b*d+3*a*c^2+3*b^2*c)+
      x*(4*a^3*d+12*a^2*b*c+4*a*b^3)+y*(5*a^4*c+10*a^3*b^2)+z*(6*a^5*b) := by
  change ((X*(C u+X*(C v+X*(C w+X*(C x+X*(C y+X*C z)))))).comp
    (jet a b c d e f)).coeff 7 = _
  simp only [Polynomial.mul_comp,Polynomial.add_comp,Polynomial.X_comp,Polynomial.C_comp]
  norm_num [product_coefficient_0,product_coefficient_1,product_coefficient_2,
    product_coefficient_3,product_coefficient_4,product_coefficient_5,product_coefficient_6,
    product_coefficient_seven,jet_coefficient,Polynomial.coeff_C]
  <;> ring

/-- Universal numerator derived from the explicitly defined cumulant update. -/
def N7 (a b c d e f g : ℝ) :=
  a^5*g-28*a^4*b*f-56*a^4*c*e-35*a^4*d^2+
  378*a^3*b^2*e+1260*a^3*b*c*d+280*a^3*c^3-
  3150*a^2*b^3*d-6300*a^2*b^2*c^2+17325*a*b^4*c-10395*b^6

theorem coefficient_formula (a b c d e f g : ℝ) (ha : a ≠ 0) :
    -((inverseJet a (b/2) (c/6) (d/24) (e/120) (f/720)).comp
      (jet a (b/2) (c/6) (d/24) (e/120) (f/720))).coeff 7-g/(5040*a)=
      -N7 a b c d e f g/(5040*a^6) := by
  unfold inverseJet
  rw [composition_seventh]
  unfold c2 c3 c4 c5 c6 N7
  field_simp
  <;> ring

open ExponentialFamily MovingTaylor CumulantOrder MeasureTheory Filter
open scoped Topology

theorem errorCoefficient_formula (ν : Measure ℝ) (r : ℝ) (hr : cumulant ν r 1 ≠ 0) :
    errorCoefficient ν r= -N7 (cumulant ν r 1) (cumulant ν r 2) (cumulant ν r 3)
      (cumulant ν r 4) (cumulant ν r 5) (cumulant ν r 6) (cumulant ν r 7)/
      (5040*(cumulant ν r 1)^6) :=
  coefficient_formula _ _ _ _ _ _ _ hr

/-- Explicit seventh-order leading coefficient for the actual moving-cumulant iteration. -/
theorem full_error_limit_explicit (ν : Measure ℝ) [IsFiniteMeasure ν] [NeZero ν]
    (m n r : ℝ) (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n) (hr : cumulant ν r 1 ≠ 0) :
    Tendsto (fun e : ℝ => (cumulantStep ν (g ν r) (r+e)-r)/e^7) (𝓝[≠] 0)
      (𝓝 (-N7 (cumulant ν r 1) (cumulant ν r 2) (cumulant ν r 3)
        (cumulant ν r 4) (cumulant ν r 5) (cumulant ν r 6) (cumulant ν r 7)/
        (5040*(cumulant ν r 1)^6))) := by
  rw [←errorCoefficient_formula ν r hr]
  exact full_error_limit ν m n r hs hr

/-- The printed seventh-order expansion, with the universal polynomial written explicitly. -/
theorem full_remainder_explicit (ν : Measure ℝ) [IsFiniteMeasure ν] [NeZero ν]
    (m n r : ℝ) (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n) (hr : cumulant ν r 1 ≠ 0) :
    (fun e : ℝ => cumulantStep ν (g ν r) (r+e)-r-
      (-N7 (cumulant ν r 1) (cumulant ν r 2) (cumulant ν r 3)
        (cumulant ν r 4) (cumulant ν r 5) (cumulant ν r 6) (cumulant ν r 7)/
        (5040*(cumulant ν r 1)^6))*e^7) =O[𝓝 0] (fun e : ℝ => e^8) := by
  rw [←errorCoefficient_formula ν r hr]
  exact AnalyticLimitFactor.full_remainder_bigO ν m n r hs hr

/-- Nonvanishing of the explicit numerator certifies exact order seven. -/
theorem exact_order_seven (ν : Measure ℝ) [IsFiniteMeasure ν] [NeZero ν]
    (m n r : ℝ) (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n) (hr : cumulant ν r 1 ≠ 0)
    (hN : N7 (cumulant ν r 1) (cumulant ν r 2) (cumulant ν r 3)
      (cumulant ν r 4) (cumulant ν r 5) (cumulant ν r 6) (cumulant ν r 7) ≠ 0) :
    (fun e : ℝ => cumulantStep ν (g ν r) (r+e)-r) =Θ[𝓝[≠] 0] (fun e : ℝ => e^7) := by
  apply full_error_exact_order ν m n r hs hr
  rw [errorCoefficient_formula ν r hr]
  exact div_ne_zero (neg_ne_zero.mpr hN) (mul_ne_zero (by norm_num) (pow_ne_zero 6 hr))

end LeanMath.Papers.CumulantCoefficient
