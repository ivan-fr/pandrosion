import LeanMath.Papers.Bilateral

noncomputable section
namespace LeanMath.Papers.PandrosionMinimal
open Real Filter Set
open scoped Topology

/-- Cubic specialization of the width-corrected Pandrosion center. -/
def numerator (R : ℝ) := 40*R^6+252*R^5+1254*R^4+1843*R^3+837*R^2+132*R+16
def denominator (R : ℝ) := 16*R^6+132*R^5+837*R^4+1843*R^3+1254*R^2+252*R+40
def correction (R : ℝ) := numerator R/denominator R

theorem numerator_pos (R : ℝ) (hR : 0 < R) : 0 < numerator R := by unfold numerator; positivity
theorem denominator_pos (R : ℝ) (hR : 0 < R) : 0 < denominator R := by unfold denominator; positivity
theorem correction_pos (R : ℝ) (hR : 0 < R) : 0 < correction R :=
  div_pos (numerator_pos R hR) (denominator_pos R hR)
theorem correction_one : correction 1=1 := by norm_num [correction,numerator,denominator]

/-- Polynomial form of the construction from the two Pandrosion endpoints. -/
theorem endpoint_construction (R : ℝ) (hR : 0 < R) :
    correction R=((2*R+1)/(R+2))*
      (9*(R+1)*((2*R+1)^2*(R+2)^2+81*R^2)+(R-1)*((2*R+1)^2*(R+2)^2-81*R^2))/
      (9*(R+1)*((2*R+1)^2*(R+2)^2+81*R^2)-(R-1)*((2*R+1)^2*(R+2)^2-81*R^2)) := by
  have hk : 0 < 9*(R+1)*((2*R+1)^2*(R+2)^2+81*R^2)-(R-1)*((2*R+1)^2*(R+2)^2-81*R^2) := by
    have he : 9*(R+1)*((2*R+1)^2*(R+2)^2+81*R^2)-(R-1)*((2*R+1)^2*(R+2)^2-81*R^2)=
      32*R^5+200*R^4+1274*R^3+1138*R^2+232*R+40 := by ring
    rw [he]; positivity
  have hd := (denominator_pos R hR).ne'
  have hr : R+2 ≠ 0 := by positivity
  unfold correction
  generalize hK : 9*(R+1)*((2*R+1)^2*(R+2)^2+81*R^2)-(R-1)*((2*R+1)^2*(R+2)^2-81*R^2)=K at *
  field_simp [hk.ne',hr,hd]
  subst K
  unfold numerator denominator
  ring

theorem reciprocal (R : ℝ) (hR : 0 < R) : correction R⁻¹=(correction R)⁻¹ := by
  unfold correction numerator denominator
  field_simp [hR.ne']
  ring

/-- This correction is strictly different from Halley on R>1. -/
theorem above_halley (R : ℝ) (hR : 1 < R) : (2*R+1)/(R+2) < correction R := by
  have hR0 : 0 < R := by linarith
  have hD := denominator_pos R hR0
  apply (div_lt_div_iff₀ (by linarith : 0 < R+2) hD).mpr
  have he : numerator R*(R+2)-(2*R+1)*denominator R=
      4*(R-1)^3*(R+2)*(2*R+1)*(R^2+7*R+1) := by
    unfold numerator denominator
    ring
  have hp : 0 < numerator R*(R+2)-(2*R+1)*denominator R := by
    rw [he]
    positivity
  linarith

/-- Denominator after substituting R = u⁻³. -/
def localDen (u : ℝ) := 16+132*u^3+837*u^6+1843*u^9+1254*u^12+252*u^15+40*u^18

def localFactor (u : ℝ) := 16*u^14+40*u^13+40*u^12+92*u^11+128*u^10-64*u^9-3*u^8+
  231*u^7-3*u^6-64*u^5+128*u^4+92*u^3+40*u^2+40*u+16

theorem localDen_pos (u : ℝ) (hu : 0 < u) : 0 < localDen u := by
  unfold localDen
  positivity

/-- Exact relative-error factorization, not a numerical Taylor fit. -/
theorem relative_error_factor (u : ℝ) (hu : 0 < u) :
    u * correction (u⁻¹ ^ 3) - 1 = (u-1)^5 * (localFactor u / localDen u) := by
  have hd := (denominator_pos (u⁻¹ ^ 3) (by positivity)).ne'
  have hb := (localDen_pos u hu).ne'
  unfold correction
  field_simp [hd, hb, hu.ne']
  unfold numerator denominator localDen localFactor
  field_simp [hu.ne']
  ring

/-- The nonzero leading coefficient proves exact local order five in relative error. -/
theorem order_five_coefficient :
    Tendsto (fun u : ℝ => localFactor u / localDen u) (𝓝 1) (𝓝 (1/6)) := by
  have hc : ContinuousAt (fun u : ℝ => localFactor u / localDen u) 1 := by
    apply ContinuousAt.div
    · unfold localFactor; fun_prop
    · unfold localDen; fun_prop
    · norm_num [localDen]
  convert hc.tendsto using 1; norm_num [localFactor, localDen]

def defect (R : ℝ) := 4096*R^14+57856*R^13+517888*R^12+2734016*R^11+10054496*R^10+
  22675388*R^9+32462241*R^8+35174922*R^7+32462241*R^6+22675388*R^5+
  10054496*R^4+2734016*R^3+517888*R^2+57856*R+4096

theorem residual_identity (R : ℝ) :
    numerator R ^ 3 - R * denominator R ^ 3 = -(R-1)^5 * defect R := by
  unfold numerator denominator defect
  ring

theorem cube_below_residual (R : ℝ) (hR : 1 < R) : correction R ^ 3 < R := by
  have hR0 : 0 < R := by linarith
  have hD := denominator_pos R hR0
  have hp : 0 < defect R := by unfold defect; positivity
  have hn : 0 < (R-1)^5 * defect R := by positivity
  have he := residual_identity R
  unfold correction
  rw [div_pow]
  apply (div_lt_iff₀ (pow_pos hD 3)).mpr
  nlinarith

end LeanMath.Papers.PandrosionMinimal


