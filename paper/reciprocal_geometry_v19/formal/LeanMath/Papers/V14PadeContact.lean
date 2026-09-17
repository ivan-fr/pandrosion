import LeanMath.Papers.V14Contact
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Algebra.Polynomial.Div

/-! Formal Padé matching gives actual analytic error bounds. -/
noncomputable section
namespace LeanMath.Papers.V14PadeContact
open Real Filter Asymptotics
open scoped Topology
open LeanMath.Papers.Cayley LeanMath.Papers.V14RootSeries

theorem root_truncation_remainder (a : ℝ) (n : ℕ) :
    (fun y : ℝ => (unchi y)^a-(PowerSeries.trunc n (rootSeries a)).eval y)
      =O[𝓝 0] (fun y => y^n) := by
  have hh := (V14RootAnalytic.root_hasFPowerSeries a).isBigO_sub_partialSum_pow n
  have he : ∀ y : ℝ, (PowerSeries.trunc n (rootSeries a)).eval y =
      ∑ k ∈ Finset.range n, PowerSeries.coeff k (rootSeries a)*y^k := by
    intro y
    exact PowerSeries.eval₂_trunc_eq_sum_range y (RingHom.id ℝ) n (rootSeries a)
  simpa [he,FormalMultilinearSeries.partialSum,FormalMultilinearSeries.ofScalars_apply_eq,
    Real.norm_eq_abs,←abs_pow,mul_comm] using hh

theorem truncation_divisible (F : PowerSeries ℝ) (n : ℕ) :
    PowerSeries.X^n ∣ F-(PowerSeries.trunc n F : PowerSeries ℝ) := by
  apply PowerSeries.X_pow_dvd_iff.mpr
  intro k hk
  simp [PowerSeries.coeff_trunc,hk]

theorem matched_polynomial_divisible (F : PowerSeries ℝ) (P Q : Polynomial ℝ) (n : ℕ)
    (hm : V14Pade.Matches F P Q n) :
    Polynomial.X^n ∣ Q*PowerSeries.trunc n F-P := by
  have hd := dvd_sub hm (dvd_mul_of_dvd_right (truncation_divisible F n) (Q:PowerSeries ℝ))
  have hd' : PowerSeries.X^n ∣ ((Q*PowerSeries.trunc n F-P : Polynomial ℝ) : PowerSeries ℝ) := by
    convert! hd using 1 <;> simp only [Polynomial.coe_sub,Polynomial.coe_mul] <;> ring
  apply Polynomial.X_pow_dvd_iff.mpr
  intro k hk
  exact_mod_cast PowerSeries.X_pow_dvd_iff.mp hd' k hk

/-- The formal contact assumption certifies a real numerator residual. -/
theorem matching_residual_bound (a : ℝ) (P Q : Polynomial ℝ) (n : ℕ)
    (hm : V14Pade.Matches (rootSeries a) P Q n) :
    (fun y : ℝ => Q.eval y*(unchi y)^a-P.eval y) =O[𝓝 0] (fun y => y^n) := by
  obtain ⟨W,hW⟩ := matched_polynomial_divisible (rootSeries a) P Q n hm
  have hq := (Q.continuous.tendsto 0).isBigO_one ℝ
  have hw := (W.continuous.tendsto 0).isBigO_one ℝ
  have hfirst := hq.mul (root_truncation_remainder a n)
  have hsecond := (isBigO_refl (fun y : ℝ => y^n) (𝓝 0)).mul hw
  simp only [one_mul,mul_one] at hfirst hsecond
  have hh := hfirst.add hsecond
  convert! hh using 1
  funext y
  have he := congrArg (Polynomial.eval y) hW
  simp only [Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X] at he
  linear_combination he

/-- Normalized formal Padé contact is actual rational approximation contact. -/
theorem matching_quotient_bound (a : ℝ) (P Q : Polynomial ℝ) (n : ℕ)
    (hQ0 : Q.eval 0 ≠ 0) (hm : V14Pade.Matches (rootSeries a) P Q n) :
    (fun y : ℝ => P.eval y/Q.eval y-(unchi y)^a) =O[𝓝 0] (fun y => y^n) := by
  have hi := ((Q.continuousAt (a:=0)).inv₀ hQ0).tendsto.isBigO_one ℝ
  have hh := ((matching_residual_bound a P Q n hm).neg_left).mul hi
  simp only [mul_one] at hh
  apply hh.congr' _ Filter.EventuallyEq.rfl
  have hn : ∀ᶠ y : ℝ in 𝓝 0, Q.eval y ≠ 0 :=
    (Q.continuous.tendsto 0).eventually (eventually_ne_nhds hQ0)
  filter_upwards [hn] with y hy
  simp only [Pi.inv_apply]
  field_simp
  <;> ring

/-- The root-specific reciprocal lift has its full contact order at R=1. -/
theorem lifted_residual_contact (a : ℝ) (P Q : Polynomial ℝ) (m n : ℕ)
    (hP : P.natDegree ≤ m) (hQ : Q.natDegree ≤ n) (hbal : n=m ∨ n=m+1)
    (hQ0 : Q.eval 0 ≠ 0)
    (hm : V14Pade.Matches (compressed a) P Q (m+n+1)) :
    (fun h : ℝ => (V14PadeNormalization.residualNumerator P Q (m+n+1)).eval (1+h) /
      (V14PadeNormalization.residualDenominator P Q (m+n+1)).eval (1+h)-(1+h)^a)
      =O[𝓝 0] (fun h => h^(2*(m+n+1)+1)) := by
  obtain ⟨hn,hd⟩ := V14Pade.lifted_degrees P Q m n hP hQ hbal
  have hd0 : (V14Pade.denominator P Q).eval 0 ≠ 0 := by simpa [V14Pade.denominator] using hQ0
  exact V14Contact.cleared_contact _ _ _ _ a hn hd
    (matching_quotient_bound a _ _ _ hd0 (root_lift_contact a P Q _ hm))

end LeanMath.Papers.V14PadeContact
