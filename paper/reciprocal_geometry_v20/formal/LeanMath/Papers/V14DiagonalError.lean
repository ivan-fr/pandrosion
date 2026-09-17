import LeanMath.Papers.V14DiagonalWronskian
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! The normalized diagonal candidate and its exact logarithmic error. -/
noncomputable section
namespace LeanMath.Papers.V14DiagonalError
open Real Polynomial Filter Set Asymptotics
open scoped Topology
open LeanMath.Papers.V14DiagonalPolynomials LeanMath.Papers.V14DiagonalWronskian

def correction (a : ℝ) (d : ℕ) (R : ℝ) : ℝ :=
  (poly a d).eval R*(poly (-a) d).eval 1/((poly (-a) d).eval R*(poly a d).eval 1)

def logError (a : ℝ) (d : ℕ) (R : ℝ) : ℝ :=
  a*log R-log ((poly a d).eval R)+log ((poly (-a) d).eval R)+
    log ((poly a d).eval 1)-log ((poly (-a) d).eval 1)

theorem correction_pos (a : ℝ) (ha : -1<a ∧ a<1) (d : ℕ) (R : ℝ) (hR : 0<R) :
    0<correction a d R := by
  have ha' : -1 < -a ∧ -a<1 := by constructor <;> linarith [ha.1,ha.2]
  exact div_pos (mul_pos (poly_pos a ha d R hR.le) (poly_pos (-a) ha' d 1 (by norm_num)))
    (mul_pos (poly_pos (-a) ha' d R hR.le) (poly_pos a ha d 1 (by norm_num)))

theorem correction_one (a : ℝ) (ha : -1<a ∧ a<1) (d : ℕ) : correction a d 1=1 := by
  have h := correction_pos a ha d 1 (by norm_num)
  unfold correction at h ⊢
  rw [mul_comm ((poly a d).eval 1)] at h ⊢
  exact div_self (by contrapose! h; rw [h]; simp)

theorem logError_one (a : ℝ) (d : ℕ) : logError a d 1=0 := by simp [logError]

theorem logError_eq (a : ℝ) (ha : -1<a ∧ a<1) (d : ℕ) (R : ℝ) (hR : 0<R) :
    logError a d R=a*log R-log (correction a d R) := by
  have ha' : -1 < -a ∧ -a<1 := by constructor <;> linarith [ha.1,ha.2]
  have hA := (poly_pos a ha d R hR.le).ne'
  have hB := (poly_pos (-a) ha' d R hR.le).ne'
  have hA1 := (poly_pos a ha d 1 (by norm_num)).ne'
  have hB1 := (poly_pos (-a) ha' d 1 (by norm_num)).ne'
  simp only [logError,correction,log_div (mul_ne_zero hA hB1) (mul_ne_zero hB hA1),
    log_mul hA hB1,log_mul hB hA1]
  ring

theorem hasDerivAt_logError (a : ℝ) (ha : -1<a ∧ a<1) (d : ℕ) (R : ℝ) (hR : 0<R) :
    HasDerivAt (logError a d) (a*(R-1)^(2*d)/(R*(poly a d).eval R*(poly (-a) d).eval R)) R := by
  have ha' : -1 < -a ∧ -a<1 := by constructor <;> linarith [ha.1,ha.2]
  have hA := (poly_pos a ha d R hR.le).ne'
  have hB := (poly_pos (-a) ha' d R hR.le).ne'
  have hh := (((((hasDerivAt_log hR.ne').const_mul a).sub
    (((poly a d).hasDerivAt R).log hA)).add
    (((poly (-a) d).hasDerivAt R).log hB)).add_const
    (log ((poly a d).eval 1))).sub_const (log ((poly (-a) d).eval 1))
  have he := congrArg (Polynomial.eval R) (error_identity a ha d)
  simp only [errorPolynomial,eval_sub,eval_mul,eval_C,eval_X,eval_pow,eval_one] at he
  convert! hh using 1
  field_simp
  nlinarith [he]

theorem analytic_logError (a : ℝ) (ha : -1<a ∧ a<1) (d : ℕ) (R : ℝ) (hR : 0<R) :
    AnalyticAt ℝ (logError a d) R := by
  have ha' : -1 < -a ∧ -a<1 := by constructor <;> linarith [ha.1,ha.2]
  have hA := (poly_pos a ha d R hR.le).ne'
  have hB := (poly_pos (-a) ha' d R hR.le).ne'
  have hAp := poly_pos a ha d R hR.le
  have hBp := poly_pos (-a) ha' d R hR.le
  have hPA : AnalyticAt ℝ (fun x => (poly a d).eval x) R :=
    AnalyticOnNhd.eval_polynomial (poly a d) R (by trivial)
  have hPB : AnalyticAt ℝ (fun x => (poly (-a) d).eval x) R :=
    AnalyticOnNhd.eval_polynomial (poly (-a) d) R (by trivial)
  exact ((((analyticAt_const.mul (analyticAt_log hR)).sub (hPA.log hAp)).add
    (hPB.log hBp)).add analyticAt_const).sub analyticAt_const

end LeanMath.Papers.V14DiagonalError
