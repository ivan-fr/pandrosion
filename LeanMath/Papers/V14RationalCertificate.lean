import LeanMath.Papers.V14Uniform
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! The polynomial derivative certificate applies to the actual rational function. -/
noncomputable section
namespace LeanMath.Papers.V14RationalCertificate
open Real Set Polynomial
open LeanMath.Papers.Cayley

/-- Logarithmic error, in an algebraically convenient form. -/
def error (A Z : ℝ[X]) (p y : ℝ) := log (A.eval y)-log (Z.eval y)-logCoord y/p

def numerator (A Z : ℝ[X]) (p : ℝ) :=
  C p*(1-X^2)*(A.derivative*Z-A*Z.derivative)-C 2*A*Z

def denominator (A Z : ℝ[X]) (p : ℝ) := C p*(1-X^2)*A*Z

theorem denominator_pos (A Z : ℝ[X]) (p y : ℝ) (hp : 0 < p)
    (hy : y ∈ Ioo (-1) 1) (hA : 0 < A.eval y) (hZ : 0 < Z.eval y) :
    0 < (denominator A Z p).eval y := by
  have hy2 : y^2 < 1 := (sq_lt_one_iff_abs_lt_one y).mpr (abs_lt.mpr hy)
  simp only [denominator,eval_mul,eval_C,eval_sub,eval_one,eval_pow,eval_X]
  positivity

/-- Equation 11.6, including the exact cancellation polynomial. -/
theorem hasDerivAt_error (A Z : ℝ[X]) (p y : ℝ) (hp : p ≠ 0)
    (hy : y ∈ Ioo (-1) 1) (hA : A.eval y ≠ 0) (hZ : Z.eval y ≠ 0) :
    HasDerivAt (error A Z p) ((numerator A Z p).eval y/(denominator A Z p).eval y) y := by
  have hh := (((A.hasDerivAt y).log hA).sub ((Z.hasDerivAt y).log hZ)).sub
    ((hasDerivAt_logCoord y hy).div_const p)
  convert! hh using 1
  simp only [numerator,denominator,eval_sub,eval_mul,eval_C,eval_one,eval_pow,eval_X]
  have hy2 : 1-y^2 ≠ 0 := by nlinarith [(sq_lt_one_iff_abs_lt_one y).mpr (abs_lt.mpr hy)]
  field_simp
  <;> ring

/-- Equality to the relative-error logarithm for the positive root target. -/
theorem error_eq_log_ratio (A Z : ℝ[X]) (p y : ℝ) (hy : y ∈ Ioo (-1) 1)
    (hA : 0 < A.eval y) (hZ : 0 < Z.eval y) :
    error A Z p y = log ((A.eval y/Z.eval y)/(unchi y)^(1/p)) := by
  rw [log_div (div_pos hA hZ).ne' (rpow_pos_of_pos (unchi_pos y hy) _).ne',
    log_div hA.ne' hZ.ne',log_rpow (unchi_pos y hy)]
  unfold error logCoord unchi
  rw [log_div (by linarith [hy.1] : 1+y ≠ 0) (by linarith [hy.2] : 1-y ≠ 0)]
  ring

theorem error_zero (A : ℝ[X]) (p : ℝ) : error A (A.comp (-X)) p 0 = 0 := by
  simp [error,logCoord,unchi]

theorem error_odd (A : ℝ[X]) (p y : ℝ) (hy : y ∈ Ioo (-1) 1) :
    error A (A.comp (-X)) p (-y) = -error A (A.comp (-X)) p y := by
  simp only [error,eval_comp,eval_neg,eval_X,neg_neg]
  rw [LeanMath.Papers.V14Halley.logCoord_odd y]
  ring

/-- The complete mathematical implication of Proposition 11.2 for A(y)/A(-y).
The finite derivative inequalities remain explicit certificate obligations. -/
theorem uniform_relative_error (A : ℝ[X]) (p rho eta : ℝ) (t lo hi : ℕ → ℝ) (n : ℕ)
    (hp : 0 < p) (hrho : rho < 1) (heta0 : 0 ≤ eta) (heta1 : eta < 1)
    (hn : 0 < n) (ht0 : t 0=0) (htn : t n=rho)
    (ht : ∀ i < n, t i ≤ t (i+1))
    (hnodes : ∀ i ≤ n, t i ∈ Icc 0 rho)
    (hpos : ∀ y, |y| ≤ rho → 0 < A.eval y)
    (hb : ∀ i < n, ∀ y ∈ Ioo (t i) (t (i+1)),
      lo i ≤ (numerator A (A.comp (-X)) p).eval y/(denominator A (A.comp (-X)) p).eval y ∧
      (numerator A (A.comp (-X)) p).eval y/(denominator A (A.comp (-X)) p).eval y ≤ hi i)
    (hcert : ∀ i < n,
      |LeanMath.Papers.V14Uniform.lowerSum t lo i+min 0 (lo i)*(t (i+1)-t i)| ≤ eta ∧
      |LeanMath.Papers.V14Uniform.upperSum t hi i+max 0 (hi i)*(t (i+1)-t i)| ≤ eta)
    (y : ℝ) (hy : |y| ≤ rho) :
    |(A.eval y/A.eval (-y))/(unchi y)^(1/p)-1| ≤ eta/(1-eta) := by
  let Z := A.comp (-X)
  have hgate : ∀ x, |x| ≤ rho → x ∈ Ioo (-1) 1 := by
    intro x hx
    exact abs_lt.mp (hx.trans_lt hrho)
  have hZ : ∀ x, |x| ≤ rho → 0 < Z.eval x := by
    intro x hx
    simpa [Z] using hpos (-x) (by simpa using hx)
  have hd : ∀ x, |x| ≤ rho → HasDerivAt (error A Z p)
      ((numerator A Z p).eval x/(denominator A Z p).eval x) x := by
    intro x hx
    exact hasDerivAt_error A Z p x hp.ne' (hgate x hx) (hpos x hx).ne' (hZ x hx).ne'
  have hinterval : ∀ i < n, ∀ x ∈ Icc (t i) (t (i+1)), |x| ≤ rho := by
    intro i hi' x hx
    have hl := (hnodes i (by omega)).1
    have hh := (hnodes (i+1) (by omega)).2
    rw [abs_of_nonneg (by linarith [hx.1])]
    linarith [hx.2]
  have hhalf : ∀ x ∈ Icc 0 rho, |error A Z p x| ≤ eta := by
    intro x hx
    apply LeanMath.Papers.V14Uniform.positive_uniform_bound (error A Z p) t lo hi n eta x hn
    · rw [ht0]; exact error_zero A p
    · simpa only [ht0,htn] using hx
    · exact ht
    · intro i hi' z hz
      exact (hd z (hinterval i hi' z hz)).continuousAt.continuousWithinAt
    · intro i hi' z hz
      exact (hd z (hinterval i hi' z ⟨hz.1.le,hz.2.le⟩)).differentiableAt.differentiableWithinAt
    · intro i hi' z hz
      rw [(hd z (hinterval i hi' z ⟨hz.1.le,hz.2.le⟩)).deriv]
      exact hb i hi' z hz
    · exact hcert
  have herr : |error A Z p y| ≤ eta := by
    by_cases hy0 : 0 ≤ y
    · exact hhalf y ⟨hy0,by simpa [abs_of_nonneg hy0] using hy⟩
    · have h := hhalf (-y) ⟨by linarith,by simpa [abs_of_neg (lt_of_not_ge hy0)] using hy⟩
      rw [error_odd A p y (hgate y hy),abs_neg] at h
      exact h
  have hv := div_pos (div_pos (hpos y hy) (hZ y hy)) (rpow_pos_of_pos (unchi_pos y (hgate y hy)) (1/p))
  rw [error_eq_log_ratio A Z p y (hgate y hy) (hpos y hy) (hZ y hy)] at herr
  simpa [Z] using LeanMath.Papers.V14Uniform.certified_relative_error _ eta hv heta0 heta1 herr

end LeanMath.Papers.V14RationalCertificate
