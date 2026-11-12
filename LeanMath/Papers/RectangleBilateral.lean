import LeanMath.Papers.RectangleReports
import LeanMath.Papers.Bracket
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
namespace LeanMath.Papers.RectangleBilateral
open LeanMath.Papers.RectangleGeometry LeanMath.Papers.RectangleReports

def neutralAK (p : ℕ) (R : ℝ) := R*(ak p R 1)^(p-1)
def neutralRaw (p : ℕ) (R : ℝ) := R*(((p:ℝ)-1+R⁻¹)/(p:ℝ))^(p-1)
def centerAK (p : ℕ) (R : ℝ) := Real.sqrt (neutralAK p R / neutralAK p R⁻¹)
def centerRaw (p : ℕ) (R : ℝ) := Real.sqrt (neutralRaw p R / neutralRaw p R⁻¹)

theorem neutralAK_is_lower (p : ℕ) (R : ℝ) : neutralAK p R=Bracket.lower p R := by
  unfold neutralAK ak Bracket.lower; simp only [one_pow,mul_one]
  congr 2 <;> ring

theorem neutralRaw_is_upper (p : ℕ) (R : ℝ) : neutralRaw p R=Bracket.upper p R :=
  (Bracket.upper_formula p R).symm

theorem neutralAK_dual (p : ℕ) (R : ℝ) :
    (neutralAK p R⁻¹)⁻¹=neutralRaw p R := by
  rw [neutralAK_is_lower,neutralRaw_is_upper]; rfl

theorem neutralRaw_dual (p : ℕ) (R : ℝ) :
    (neutralRaw p R⁻¹)⁻¹=neutralAK p R := by
  rw [neutralRaw_is_upper,neutralAK_is_lower]; simp [Bracket.upper]

/-- Exact identity for all degrees, not just agreement of leading orders. -/
theorem bilateral_AK_equals_original (p : ℕ) (R : ℝ) : centerAK p R=centerRaw p R := by
  unfold centerAK centerRaw
  rw [div_eq_mul_inv,neutralAK_dual,div_eq_mul_inv,neutralRaw_dual,mul_comm]

/-- Circle with diameter (-l,0)--(h,0), altitude at the origin. -/
def circleCenter (l h : ℝ) : Point := ((h-l)/2,0)
def radius (l h : ℝ) := (h+l)/2
def altitude (l h : ℝ) : Point := (0,Real.sqrt (l*h))
def OnCircle (c : Point) (r : ℝ) (P : Point) : Prop :=
  (P.1-c.1)^2+(P.2-c.2)^2=r^2

theorem diameter_endpoints (l h : ℝ) :
    OnCircle (circleCenter l h) (radius l h) (-l,0) ∧
    OnCircle (circleCenter l h) (radius l h) (h,0) := by
  dsimp [OnCircle,circleCenter,radius]; constructor <;> ring

theorem altitude_on_circle (l h : ℝ) (hl : 0<l) (hh : 0<h) :
    OnCircle (circleCenter l h) (radius l h) (altitude l h) ∧
    On (vertical 0) (altitude l h) ∧ 0<(altitude l h).2 := by
  have hs := Real.sq_sqrt (mul_pos hl hh).le
  dsimp [OnCircle,circleCenter,radius,altitude,On,vertical]
  refine ⟨?_,by ring,Real.sqrt_pos.mpr (mul_pos hl hh)⟩
  nlinarith

theorem altitude_unique (l h : ℝ) (hl : 0<l) (hh : 0<h) (P : Point)
    (hc : OnCircle (circleCenter l h) (radius l h) P)
    (hv : On (vertical 0) P) (hu : 0≤P.2) : P=altitude l h := by
  have hx : P.1=0 := by simpa [On,vertical] using hv
  have hy : P.2^2=l*h := by
    dsimp [OnCircle,circleCenter,radius] at hc
    rw [hx] at hc; nlinarith
  have hs := Real.sq_sqrt (mul_pos hl hh).le
  have hnon := Real.sqrt_nonneg (l*h)
  have he : P.2=Real.sqrt (l*h) := by nlinarith
  exact Prod.ext hx he

theorem altitude_bilateral (p : ℕ) (R u : ℝ) (hu : 0≤u) :
    (altitude (u*neutralAK p R) (u/neutralAK p R⁻¹)).2=u*centerAK p R := by
  dsimp [altitude,centerAK]
  rw [show u*neutralAK p R*(u/neutralAK p R⁻¹)=u^2*(neutralAK p R/neutralAK p R⁻¹) by ring,
    Real.sqrt_mul (sq_nonneg u),Real.sqrt_sq hu]

theorem bilateral_bracket (p : ℕ) (X u r : ℝ) (hp : 1≤p)
    (hu : 0<u) (hr : 0<r) (hx : r^p=X) :
    u*neutralAK p (X/u^p)≤r ∧ r≤u/neutralAK p (X/u^p)⁻¹ := by
  have he : u/neutralAK p (X/u^p)⁻¹=u*Bracket.upper p (X/u^p) := by
    rw [div_eq_mul_inv,neutralAK_is_lower]
    rfl
  rw [neutralAK_is_lower,he]
  exact Bracket.kernel_independent_certificate p X u r hp hu hr hx

theorem cubic_center (R : ℝ) (hR : 0<R) : centerAK 3 R=(2*R+1)/(R+2) := by
  have hd : R+2 ≠ 0 := by positivity
  have he : neutralAK 3 R/neutralAK 3 R⁻¹=((2*R+1)/(R+2))^2 := by
    unfold neutralAK ak
    norm_num
    field_simp
    <;> ring
  unfold centerAK; rw [he,Real.sqrt_sq (by positivity)]
end LeanMath.Papers.RectangleBilateral
