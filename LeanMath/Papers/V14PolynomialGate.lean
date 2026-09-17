import LeanMath.Papers.V14RationalCertificate

/-! A rational coefficient certificate for positivity on a symmetric gate. -/
noncomputable section
namespace LeanMath.Papers.V14PolynomialGate
open Polynomial

def ofCoeffs : List ℚ → ℝ[X]
  | [] => 0
  | a::cs => C (a:ℝ)+X*ofCoeffs cs

/-- Exact rational absolute-coefficient majorant, evaluated by Horner's rule. -/
def mass : List ℚ → ℚ → ℚ
  | [], _ => 0
  | a::cs, r => |a|+r*mass cs r

theorem mass_nonneg (cs : List ℚ) (r : ℚ) (hr : 0≤r) : 0≤mass cs r := by
  induction cs with
  | nil => simp [mass]
  | cons a cs ih => exact add_nonneg (abs_nonneg a) (mul_nonneg hr ih)

theorem eval_abs_bound (cs : List ℚ) (r : ℚ) (hr : 0≤r) (y : ℝ) (hy : |y|≤(r:ℝ)) :
    |(ofCoeffs cs).eval y| ≤ (mass cs r:ℝ) := by
  induction cs with
  | nil => simp [ofCoeffs,mass]
  | cons a cs ih =>
    simp only [ofCoeffs,eval_add,eval_C,eval_mul,eval_X,mass,Rat.cast_add,Rat.cast_mul,Rat.cast_abs]
    calc
      |(a:ℝ)+y*(ofCoeffs cs).eval y| ≤ |(a:ℝ)|+|y*(ofCoeffs cs).eval y| := abs_add_le _ _
      _ ≤ |(a:ℝ)|+(r:ℝ)*(mass cs r:ℝ) := by
        rw [abs_mul]
        exact add_le_add le_rfl (mul_le_mul hy ih (abs_nonneg _) (by exact_mod_cast hr))

theorem positive_on_gate (cs : List ℚ) (r : ℚ) (hr : 0≤r) (hcert : r*mass cs r<1)
    (y : ℝ) (hy : |y|≤(r:ℝ)) : 0<(ofCoeffs (1::cs)).eval y := by
  have hb := eval_abs_bound cs r hr y hy
  have hmass : (0:ℝ) ≤ mass cs r := by exact_mod_cast mass_nonneg cs r hr
  have hprod : |y*(ofCoeffs cs).eval y| ≤ (r:ℝ)*(mass cs r:ℝ) := by
    rw [abs_mul]
    exact mul_le_mul hy hb (abs_nonneg _) (by exact_mod_cast hr)
  have hc : (r:ℝ)*(mass cs r:ℝ)<1 := by exact_mod_cast hcert
  simp only [ofCoeffs,eval_add,eval_C,eval_mul,eval_X,Rat.cast_one]
  linarith [(abs_le.mp hprod).1]

end LeanMath.Papers.V14PolynomialGate
