import LeanMath.Papers.V14DiagonalError

/-! The positive-coefficient construction satisfies the classical diagonal Padé contact. -/
noncomputable section
namespace LeanMath.Papers.V14DiagonalContact
open Real Polynomial Filter Asymptotics Set
open scoped Topology
open LeanMath.Papers.V14DiagonalPolynomials LeanMath.Papers.V14DiagonalError

theorem error_contact (a : ℝ) (ha : -1<a ∧ a<1) (d : ℕ) :
    logError a d =O[𝓝 1] (fun R : ℝ => (R-1)^(2*d+1)) := by
  have hA := analytic_logError a ha d 1 (by norm_num)
  have ha' : -1 < -a ∧ -a<1 := by constructor <;> linarith [ha.1,ha.2]
  let g := fun R : ℝ => a/(R*(poly a d).eval R*(poly (-a) d).eval R)
  have hg : AnalyticAt ℝ g 1 := by
    have hPA : AnalyticAt ℝ (fun R => (poly a d).eval R) 1 :=
      AnalyticOnNhd.eval_polynomial (poly a d) 1 (by trivial)
    have hPB : AnalyticAt ℝ (fun R => (poly (-a) d).eval R) 1 :=
      AnalyticOnNhd.eval_polynomial (poly (-a) d) 1 (by trivial)
    exact analyticAt_const.div ((analyticAt_id.mul hPA).mul hPB)
      (by have h1 := poly_pos a ha d 1 (by norm_num)
          have h2 := poly_pos (-a) ha' d 1 (by norm_num)
          positivity)
  have ho : (2*d:ℕ) ≤ analyticOrderAt (deriv (logError a d)) 1 := by
    apply (natCast_le_analyticOrderAt hA.deriv).mpr
    refine ⟨g,hg,?_⟩
    filter_upwards [Ioi_mem_nhds (by norm_num : (0:ℝ)<1)] with R hR
    rw [(hasDerivAt_logError a ha d R hR).deriv]
    dsimp [g]; ring
  have ho' : (2*d+1:ℕ) ≤ analyticOrderAt (logError a d) 1 :=
    (analyticOrderAt_deriv_ge_iff hA (logError_one a d)).mp ho
  obtain ⟨q,hq,he⟩ := (natCast_le_analyticOrderAt hA).mp ho'
  have hh := (isBigO_refl (fun R : ℝ => (R-1)^(2*d+1)) (𝓝 1)).mul
    (hq.continuousAt.tendsto.isBigO_one ℝ)
  apply hh.congr'
  · filter_upwards [he] with R hR
    simpa only [smul_eq_mul] using hR.symm
  · filter_upwards [] with R; simp

theorem correction_contact (a : ℝ) (ha : -1<a ∧ a<1) (d : ℕ) :
    (fun R : ℝ => correction a d R-R^a) =O[𝓝 1] (fun R => (R-1)^(2*d+1)) := by
  have hA := analytic_logError a ha d 1 (by norm_num)
  have ht : Tendsto (fun R => -logError a d R) (𝓝 1) (𝓝 0) := by
    simpa [logError_one] using hA.continuousAt.tendsto.neg
  have he := (hasDerivAt_exp (0:ℝ)).differentiableAt.isBigO_sub.comp_tendsto ht
  simp only [exp_zero,sub_zero] at he
  have hh := he.trans (error_contact a ha d).neg_left
  have hp : ContinuousAt (fun R : ℝ => R^a) 1 := continuousAt_id.rpow_const (Or.inl (by norm_num))
  have hb := hp.tendsto.isBigO_one ℝ
  have hprod := hb.mul hh
  apply hprod.congr'
  · filter_upwards [Ioi_mem_nhds (by norm_num : (0:ℝ)<1)] with R hR
    have hc := correction_pos a ha d R hR
    simp only [Function.comp_def]
    rw [logError_eq a ha d R hR]
    have heq : exp (-(a*log R-log (correction a d R)))=correction a d R/R^a := by
      rw [neg_sub,exp_sub,exp_log hc,Real.rpow_def_of_pos hR]
      rw [mul_comm a (log R)]
    rw [heq]
    have hr := (rpow_pos_of_pos hR a).ne'
    field_simp
  · filter_upwards [] with R
    simp

/-- Explicit normalized polynomial pair for the diagonal root function. -/
def numerator (a : ℝ) (d : ℕ) : ℝ[X] := C ((poly (-a) d).eval 1)*poly a d

def denominator (a : ℝ) (d : ℕ) : ℝ[X] := C ((poly a d).eval 1)*poly (-a) d

theorem isDiagonal (a : ℝ) (ha : -1<a ∧ a<1) (d : ℕ) :
    LeanMath.Papers.V14PadeTheorem.IsDiagonal a d (numerator a d) (denominator a d) := by
  have ha' : -1 < -a ∧ -a<1 := by constructor <;> linarith [ha.1,ha.2]
  refine ⟨(natDegree_C_mul_le _ _).trans (degree_le a d),
    (natDegree_C_mul_le _ _).trans (degree_le (-a) d),?_,?_⟩
  · dsimp [denominator]
    rw [eval_mul,eval_C]
    exact mul_ne_zero (poly_pos a ha d 1 (by norm_num)).ne' (poly_pos (-a) ha' d 1 (by norm_num)).ne'
  · have ht : Tendsto (fun h : ℝ => 1+h) (𝓝 0) (𝓝 1) := by
      simpa using tendsto_const_nhds.add ((tendsto_id : Tendsto (fun h : ℝ => h) (𝓝 0) (𝓝 0)))
    have hh := (correction_contact a ha d).comp_tendsto ht
    simpa [Function.comp_def,numerator,denominator,correction,mul_comm] using hh

end LeanMath.Papers.V14DiagonalContact
