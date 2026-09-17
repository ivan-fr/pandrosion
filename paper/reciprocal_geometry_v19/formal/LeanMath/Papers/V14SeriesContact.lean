import LeanMath.Papers.V14ScalarSeries
import LeanMath.Papers.V14AnalyticUniqueness

/-! Equivalence bridge from analytic matching to formal coefficient matching. -/
noncomputable section
namespace LeanMath.Papers.V14SeriesContact
open PowerSeries Filter Asymptotics
open scoped Topology
open LeanMath.Papers.V14ScalarSeries

theorem polynomial_represents (P : Polynomial ℝ) : Represents (P:PowerSeries ℝ) (fun y => P.eval y) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simpa only [Polynomial.coe_add,Polynomial.eval_add] using V14ScalarSeries.add _ _ _ _ hP hQ
  | monomial k c =>
    rw [represents_iff]
    filter_upwards [] with y
    convert! hasSum_single k (fun j hj =>
      show coeff j ((Polynomial.monomial k c : Polynomial ℝ) : PowerSeries ℝ)*y^j=0 by
        simp [Polynomial.coeff_coe,Polynomial.coeff_monomial,PowerSeries.coeff_monomial,hj,Ne.symm hj]) using 1
    simp

theorem truncation_remainder (F : PowerSeries ℝ) (f : ℝ → ℝ) (hf : Represents F f) (n : ℕ) :
    (fun y : ℝ => f y-(trunc n F).eval y) =O[𝓝 0] (fun y => y^n) := by
  have hh := hf.isBigO_sub_partialSum_pow n
  have he : ∀ y : ℝ, (trunc n F).eval y = ∑ k ∈ Finset.range n, coeff k F*y^k := by
    intro y
    exact eval₂_trunc_eq_sum_range y (RingHom.id ℝ) n F
  simpa [he,FormalMultilinearSeries.partialSum,FormalMultilinearSeries.ofScalars_apply_eq,
    Real.norm_eq_abs,←abs_pow,mul_comm] using hh

/-- Analytic vanishing forces all lower formal coefficients to vanish. -/
theorem analytic_vanishing (F : PowerSeries ℝ) (f : ℝ → ℝ) (hf : Represents F f)
    (n : ℕ) (hO : f =O[𝓝 0] (fun y : ℝ => y^n)) : X^n ∣ F := by
  cases n with
  | zero => simp
  | succ n =>
    have hh := hO.sub (truncation_remainder F f hf (n+1))
    have hT : (fun y : ℝ => (trunc (n+1) F).eval y) =O[𝓝 0] (fun y => y^(n+1)) := by
      convert! hh using 1
      funext y; ring
    have hz := V14AnalyticUniqueness.polynomial_contact_zero _ _ (natDegree_trunc_lt F n) hT
    apply X_pow_dvd_iff.mpr
    intro k hk
    have hc := congrArg (fun T : Polynomial ℝ => T.coeff k) hz
    simpa [coeff_trunc,hk] using hc

/-- The paper's analytic Padé matching condition implies formal matching. -/
theorem analytic_matching (F : PowerSeries ℝ) (f : ℝ → ℝ) (hf : Represents F f)
    (P Q : Polynomial ℝ) (n : ℕ) (hQ0 : Q.eval 0 ≠ 0)
    (hm : (fun y : ℝ => f y-P.eval y/Q.eval y) =O[𝓝 0] (fun y => y^n)) :
    V14Pade.Matches F P Q n := by
  have hb := (Q.continuous.tendsto 0).isBigO_one ℝ
  have hh := hb.mul hm
  simp only [one_mul] at hh
  have hr : (fun y : ℝ => Q.eval y*f y-P.eval y) =O[𝓝 0] (fun y => y^n) := by
    apply hh.congr' _ Filter.EventuallyEq.rfl
    have hne := (Q.continuous.tendsto 0).eventually (eventually_ne_nhds hQ0)
    filter_upwards [hne] with y hy
    field_simp
    <;> ring
  exact analytic_vanishing _ _
    (V14ScalarSeries.sub _ _ _ _ (V14ScalarSeries.mul _ _ _ _ (polynomial_represents Q) hf)
      (polynomial_represents P)) n hr

end LeanMath.Papers.V14SeriesContact
