import LeanMath.Papers.ProportionalReadouts
import LeanMath.Papers.CrossBracket

/-! Cubic nested and intersected certificates in the real-degree notation of v14. -/
noncomputable section
namespace LeanMath.Papers.V14CubicEnclosure
open Real
open LeanMath.Papers.ProportionalReadouts LeanMath.Papers.RealBracket LeanMath.Papers.Cayley

theorem lower_three (R : ℝ) : lower 3 R=Bracket.lower 3 R := by
  norm_num [lower,Bracket.lower,rpow_two]

theorem upper_three (R : ℝ) : upper 3 R=Bracket.upper 3 R := by
  simp only [upper,Bracket.upper,lower_three]

theorem mean_bounds (R : ℝ) (hR : 0<R) :
    harmonic R≤R^(1/(3:ℝ)) ∧ R^(1/(3:ℝ))≤arithmetic R := by
  have hr := rpow_pos_of_pos hR (1/(3:ℝ))
  have he : (R^(1/(3:ℝ)))^3=R := by
    rw [←rpow_natCast,←rpow_mul hR.le]
    norm_num
  simpa only [he] using And.intro (harmonic_le_root _ hr) (root_le_arithmetic _ hr)

theorem nested_enclosure (R : ℝ) (hR : 0<R) :
    lower 3 R≤harmonic R ∧ harmonic R≤R^(1/(3:ℝ)) ∧
    R^(1/(3:ℝ))≤arithmetic R ∧ arithmetic R≤upper 3 R := by
  have hn := nested_bounds R hR
  rw [←lower_three,←upper_three] at hn
  exact ⟨hn.1,(mean_bounds R hR).1,(mean_bounds R hR).2,hn.2⟩

theorem exact_half_width (R : ℝ) (hR : 0<R) :
    log (arithmetic R/harmonic R)=log (upper 3 R/lower 3 R)/2 := by
  simpa only [lower_three,upper_three] using logarithmic_width_half R hR

/-- The intersection above residual one improves both original certificates. -/
theorem intersection_above (R : ℝ) (hR : 1<R) :
    lower 3 R<C₇ 3 R ∧ harmonic R<C₇ 3 R ∧ C₇ 3 R<R^(1/(3:ℝ)) ∧
    R^(1/(3:ℝ))≤arithmetic R ∧ arithmetic R≤upper 3 R := by
  have hR0 : 0<R := by linarith
  have hc := C₇_above_one_below_root 3 R (by norm_num) hR
  have hH : harmonic R<C₃ 3 R := by
    rw [halley_formula 3 R (by norm_num) hR0]
    unfold harmonic
    have h1 : 0<2*R+1 := by positivity
    have h2 : 0<(3-1)*R+(3+1) := by linarith
    apply (div_lt_div_iff₀ h1 h2).mpr
    nlinarith [sq_pos_of_pos (show 0<R-1 by linarith)]
  have h37 := RealCorrections.C₃_lt_C₇ 3 R (by norm_num) hR
  have hn := nested_enclosure R hR0
  exact ⟨hn.1.trans_lt (hH.trans h37),hH.trans h37,hc.2,hn.2.2.1,hn.2.2.2⟩

/-- The intersection below residual one uses the harmonic lower endpoint. -/
theorem intersection_below (R : ℝ) (hR : 0<R) (hR1 : R<1) :
    lower 3 R≤harmonic R ∧ harmonic R≤R^(1/(3:ℝ)) ∧
    R^(1/(3:ℝ))<C₇ 3 R ∧ C₇ 3 R<arithmetic R ∧ C₇ 3 R<upper 3 R := by
  have hc := C₇_below_one_above_root 3 R (by norm_num) hR hR1
  have hi := intersection_above R⁻¹ ((one_lt_inv₀ hR).mpr hR1)
  have hH : harmonic R⁻¹=(arithmetic R)⁻¹ := by
    unfold harmonic arithmetic
    field_simp
    <;> ring
  rw [hH,C₇_reciprocal 3 R hR] at hi
  have hA : 0<arithmetic R := by unfold arithmetic; positivity
  have hca : C₇ 3 R<arithmetic R := (inv_lt_inv₀ hA (C₇_pos 3 R (by norm_num) hR)).mp hi.2.1
  have hn := nested_enclosure R hR
  exact ⟨hn.1,hn.2.1,hc.1,hca,hca.trans_le hn.2.2.2⟩

end LeanMath.Papers.V14CubicEnclosure
