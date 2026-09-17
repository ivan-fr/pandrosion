import LeanMath.Papers.RectangleNewton
import LeanMath.Papers.RectangleConstructible
import LeanMath.Papers.RawConvergence

/-! End-to-end bridges to the visible readout, and exact regression examples.
The formal model is Cartesian Euclidean incidence over the real numbers.
It does not certify HTML/GeoGebra code or historical attribution. -/
noncomputable section
namespace LeanMath.Papers.RectangleVerification
open LeanMath.Papers LeanMath.Papers.RectangleReports
open Filter Function
open scoped Topology

theorem raw_matches_existing (p : ℕ) (X s : ℝ) : RectangleRaw.raw p X s=Raw.step p X s := rfl

theorem raw_global (p : ℕ) (X s : ℝ) (hp : 2≤p) (hX : 1<X) (hs : 0<s) :
    Tendsto (fun n : ℕ => (RectangleRaw.raw p X)^[n] s) atTop
      (𝓝 ((X^((p:ℝ)⁻¹))⁻¹)) := (Raw.global_raw_convergence p X s hp hX hs).1

theorem target_identity (p : ℕ) (X : ℝ) (hp : 2≤p) (hX : 0<X) :
    X*(X⁻¹ ^ (1/(p:ℝ)))^p=1 := by
  have hp0 : (p:ℝ)≠0 := by exact_mod_cast (show p≠0 by omega)
  rw [← Real.rpow_natCast,one_div,Real.rpow_inv_rpow (inv_nonneg.mpr hX.le) hp0,
    mul_inv_cancel₀ hX.ne']

theorem ad_visible_convergence (p : ℕ) (X s : ℝ) (hp : 2≤p) (hX : 0<X) (hs : 0<s) :
    Tendsto (fun n : ℕ => X*((ad p X)^[n] s)^(p-1)) atTop (𝓝 (X^(1/(p:ℝ)))) := by
  have ha : 0<X⁻¹ ^ (1/(p:ℝ)) := Real.rpow_pos_of_pos (inv_pos.mpr hX) _
  have ht := ((RectangleDynamics.ad_global_convergence p X s hp hX hs).pow (p-1)).const_mul X
  rw [Raw.visible_readout p X _ (by omega) ha (target_identity p X hp hX)] at ht
  simpa [Real.inv_rpow hX.le] using ht

theorem ak_visible_convergence (p : ℕ) (X s : ℝ) (hp : 2≤p) (hX : 0<X) (hs : 0<s) :
    Tendsto (fun n : ℕ => X*((ak p X)^[n] s)^(p-1)) atTop (𝓝 (X^(1/(p:ℝ)))) := by
  have ha : 0<X⁻¹ ^ (1/(p:ℝ)) := Real.rpow_pos_of_pos (inv_pos.mpr hX) _
  have ht := ((RectangleNewton.ak_global_convergence p X s hp hX hs).pow (p-1)).const_mul X
  rw [Raw.visible_readout p X _ (by omega) ha (target_identity p X hp hX)] at ht
  simpa [Real.inv_rpow hX.le] using ht

theorem cubic_preview_D : movingD 2 4 2 (3/4) 3=(0,-27/16) := by
  norm_num [movingD]
theorem cubic_preview_AD : ad 3 2 (3/4)=273/344 := by norm_num [ad]
theorem cubic_preview_AK : ak 3 2 (3/4)=72/91 := by norm_num [ak]
theorem cubic_preview_intersection :
    RectangleGeometry.reportPoint 2 4 (3/4) (adSlope 2 4 2 (3/4) 3)
      (greenSlope 2 4 2 (3/4) 3)=(38/43,71/86) := by
  norm_num [RectangleGeometry.reportPoint,adSlope,greenSlope]
end LeanMath.Papers.RectangleVerification
