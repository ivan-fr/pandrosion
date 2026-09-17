import LeanMath.Papers.V14PowerError
import LeanMath.Papers.V14PolynomialCheck
import LeanMath.Papers.V14DiagonalContact
import LeanMath.Papers.V14HalleyThresholds

/-! Kernel-checkable finite inputs for small diagonal Padé degrees. -/
noncomputable section
namespace LeanMath.Papers.V14MinimalCheck
open Polynomial
open LeanMath.Papers.V14PolynomialGate LeanMath.Papers.V14PolynomialCheck
open LeanMath.Papers.V14PowerError

def certificate (as ds : List ℚ) (p rho c : ℚ) (n : ℕ)
    (hp : 0<p) (hr0 : 0≤rho) (hr1 : rho<1) (hc : 0≤c)
    (hL : 0<p-rho*mass ds rho) (hU : 0<p+rho*mass ds rho)
    (hpos : rho*mass as rho<1)
    (hN : equalCheck (numeratorList (1::as) p) (scale (-c) (power [0,1] n))=true)
    (hD : equalCheck (denominatorList (1::as) p) (p::ds)=true) :
    Certificate (ofCoeffs (1::as)) p rho n where
  c := c
  L := ((p-rho*mass ds rho:ℚ):ℝ)
  U := ((p+rho*mass ds rho:ℚ):ℝ)
  hp := by exact_mod_cast hp
  hr0 := by exact_mod_cast hr0
  hr1 := by exact_mod_cast hr1
  hc := by exact_mod_cast hc
  hL := by exact_mod_cast hL
  hU := by exact_mod_cast hU
  hpos := positive_on_gate as rho hr0 hpos
  hN := by
    have hh := equalCheck_sound _ _ hN
    rw [numeratorList_sound,of_scale,of_power] at hh
    simpa [ofCoeffs] using hh
  hD := by
    have hh := equalCheck_sound _ _ hD
    rw [denominatorList_sound] at hh
    intro y hy
    rw [hh]
    exact constant_mass_bounds p ds rho hr0 y hy

/-- Uniform threshold for the canonical diagonal Padé family, including degree zero. -/
def Meets (p rho : ℝ) (d : ℕ) : Prop :=
  ∀ y : ℝ, |y|≤rho →
    |LeanMath.Papers.V14DiagonalError.correction (1/p) d (LeanMath.Papers.Cayley.unchi y) /
      (LeanMath.Papers.Cayley.unchi y)^(1/p)-1|≤8/(2:ℝ)^52

end LeanMath.Papers.V14MinimalCheck
