import LeanMath.Papers.V14Defect
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Degree.Defs

/-! Reciprocal fusion and its error-budget bridge, §§11.1–11.4. -/
noncomputable section
namespace LeanMath.Papers.V14Fused
open Real Polynomial
open LeanMath.Papers.Cayley

def centerCoordinate (Pg Qg : ℝ[X]) (y : ℝ) := y*Pg.eval (y^2)/Qg.eval (y^2)
def defectCoordinate (Ph Qh : ℝ[X]) (y : ℝ) := y^3*Ph.eval (y^2)/Qh.eval (y^2)

def numerator (Pg Qg Ph Qh : ℝ[X]) : ℝ[X] :=
  (Qg.comp (X^2)+X*Pg.comp (X^2))*(Qh.comp (X^2)+X^3*Ph.comp (X^2))

def fused (Pg Qg Ph Qh : ℝ[X]) (y : ℝ) :=
  (numerator Pg Qg Ph Qh).eval y / (numerator Pg Qg Ph Qh).eval (-y)

theorem fused_reciprocal (Pg Qg Ph Qh : ℝ[X]) (y : ℝ) :
    fused Pg Qg Ph Qh (-y) = (fused Pg Qg Ph Qh y)⁻¹ := by
  simp [fused, inv_div]

theorem numerator_formula (Pg Qg Ph Qh : ℝ[X]) (y : ℝ) :
    (numerator Pg Qg Ph Qh).eval y =
      (Qg.eval (y^2)+y*Pg.eval (y^2))*(Qh.eval (y^2)+y^3*Ph.eval (y^2)) := by
  simp [numerator]

theorem fused_eq_product (Pg Qg Ph Qh : ℝ[X]) (y : ℝ)
    (hg : Qg.eval (y^2) ≠ 0) (hh : Qh.eval (y^2) ≠ 0) :
    fused Pg Qg Ph Qh y =
      unchi (centerCoordinate Pg Qg y)*unchi (defectCoordinate Ph Qh y) := by
  unfold fused
  rw [numerator_formula, numerator_formula]
  simp only [even_two, Even.neg_pow, neg_pow, neg_mul, Odd.neg_pow (by decide : Odd 3)]
  unfold unchi centerCoordinate defectCoordinate
  field_simp
  <;> ring

/-- The positivity/pole-freedom part of Proposition 11.1. -/
theorem fused_positive (Pg Qg Ph Qh : ℝ[X]) (y : ℝ)
    (hg : Qg.eval (y^2) ≠ 0) (hh : Qh.eval (y^2) ≠ 0)
    (hj : |centerCoordinate Pg Qg y| < 1)
    (hd : |defectCoordinate Ph Qh y| < 1) :
    0 < fused Pg Qg Ph Qh y := by
  rw [fused_eq_product Pg Qg Ph Qh y hg hh]
  exact mul_pos (unchi_pos _ (abs_lt.mp hj)) (unchi_pos _ (abs_lt.mp hd))

/-- Reciprocity in the original residual coordinate. -/
theorem residual_reciprocal (Pg Qg Ph Qh : ℝ[X]) (R : ℝ) (hR : 0 < R) :
    fused Pg Qg Ph Qh (chi R⁻¹) = (fused Pg Qg Ph Qh (chi R))⁻¹ := by
  rw [chi_inv R hR, fused_reciprocal]

/-- Polynomial degree before the linear-fractional substitution; no cancellation is assumed. -/
theorem numerator_degree (Pg Qg Ph Qh : ℝ[X]) (dg dh : ℕ)
    (hpg : Pg.natDegree ≤ dg) (hqg : Qg.natDegree ≤ dg)
    (hph : Ph.natDegree ≤ dh) (hqh : Qh.natDegree ≤ dh) :
    (numerator Pg Qg Ph Qh).natDegree ≤ 2*dg+2*dh+4 := by
  have hx2 : ((X:ℝ[X])^2).natDegree = 2 := by simp
  have hx3 : ((X:ℝ[X])^3).natDegree = 3 := by simp
  have hPg := natDegree_comp_le (p:=Pg) (q:=(X:ℝ[X])^2)
  have hQg := natDegree_comp_le (p:=Qg) (q:=(X:ℝ[X])^2)
  have hPh := natDegree_comp_le (p:=Ph) (q:=(X:ℝ[X])^2)
  have hQh := natDegree_comp_le (p:=Qh) (q:=(X:ℝ[X])^2)
  rw [hx2] at hPg hQg hPh hQh
  have hG : (Qg.comp (X^2)+X*Pg.comp (X^2)).natDegree ≤ 2*dg+1 := by
    apply (natDegree_add_le _ _).trans
    apply max_le
    · omega
    · have h := natDegree_mul_le (p:=(X:ℝ[X])) (q:=Pg.comp (X^2))
      simp only [natDegree_X] at h
      omega
  have hH : (Qh.comp (X^2)+X^3*Ph.comp (X^2)).natDegree ≤ 2*dh+3 := by
    apply (natDegree_add_le _ _).trans
    apply max_le
    · omega
    · have h := natDegree_mul_le (p:=((X:ℝ[X])^3)) (q:=Ph.comp (X^2))
      rw [hx3] at h
      omega
  unfold numerator
  have h := natDegree_mul_le (p:=Qg.comp (X^2)+X*Pg.comp (X^2))
    (q:=Qh.comp (X^2)+X^3*Ph.comp (X^2))
  omega

/-- Equation 11.9: exact-function error plus residual coherence error. -/
theorem coherence_error_identity (p X u R F : ℝ)
    (hp : p ≠ 0) (hX : 0 < X) (hu : 0 < u) (hR : 0 < R) (hF : 0 < F) :
    log (u*F/X^(1/p)) = log (F/R^(1/p))+log (R*u^p/X)/p := by
  rw [log_div (mul_pos hu hF).ne' (rpow_pos_of_pos hX _).ne',
    log_mul hu.ne' hF.ne',log_rpow hX,
    log_div hF.ne' (rpow_pos_of_pos hR _).ne',log_rpow hR,
    log_div (mul_pos hR (rpow_pos_of_pos hu p)).ne' hX.ne',
    log_mul hR.ne' (rpow_pos_of_pos hu p).ne',log_rpow hu]
  field_simp
  <;> ring

/-- The resulting error budget, with an explicit evaluation perturbation. -/
theorem total_error_budget (p E beta zeta eta b z : ℝ) (hp : 0 < p)
    (hE : |E| ≤ eta) (hb : |beta| ≤ b) (hz : |zeta| ≤ z) :
    |E+beta/p+zeta| ≤ eta+b/p+z := by
  calc
    |E+beta/p+zeta| ≤ |E+beta/p|+|zeta| := abs_add_le _ _
    _ ≤ (|E|+|beta/p|)+|zeta| := by linarith [abs_add_le E (beta/p)]
    _ = (|E|+|beta|/p)+|zeta| := by rw [abs_div,abs_of_pos hp]
    _ ≤ eta+b/p+z := add_le_add (add_le_add hE (div_le_div_of_nonneg_right hb hp.le)) hz

end LeanMath.Papers.V14Fused
