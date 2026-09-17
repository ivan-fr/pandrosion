import LeanMath.Papers.V14DiagonalContact
import LeanMath.Papers.V14DiagonalOrdering
import LeanMath.Papers.MonotoneIteration

/-! Global monotone convergence of every classical diagonal Padé root iteration. -/
noncomputable section
namespace LeanMath.Papers.V14DiagonalConvergence
open Real Filter Function Polynomial
open scoped Topology
open LeanMath.Papers.V14DiagonalPolynomials LeanMath.Papers.V14DiagonalError
open LeanMath.Papers.V14DiagonalOrdering

def step (p : ℝ) (d : ℕ) (X u : ℝ) : ℝ := u*correction (1/p) d (X/u^p)

theorem reciprocal_exponent (p : ℝ) (hp : 1<p) : 0<1/p ∧ 1/p<1 := by
  constructor
  · positivity
  · exact (div_lt_one (by linarith)).mpr hp

theorem continuous_correction (a : ℝ) (ha : -1<a ∧ a<1) (d : ℕ) (R : ℝ) (hR : 0<R) :
    ContinuousAt (correction a d) R := by
  have ha' : -1 < -a ∧ -a<1 := by constructor <;> linarith [ha.1,ha.2]
  exact ((poly a d).continuousAt.mul continuousAt_const).div
    ((poly (-a) d).continuousAt.mul continuousAt_const)
    (mul_ne_zero (poly_pos (-a) ha' d R hR.le).ne' (poly_pos a ha d 1 (by norm_num)).ne')

theorem continuous_step (p : ℝ) (hp : 1<p) (d : ℕ) (X u : ℝ) (hX : 0<X) (hu : 0<u) :
    ContinuousAt (step p d X) u := by
  have ha := reciprocal_exponent p hp
  have huPow := rpow_pos_of_pos hu p
  have hf : ContinuousAt (fun u : ℝ => X/u^p) u :=
    continuousAt_const.div (continuousAt_id.rpow_const (Or.inr (by linarith))) huPow.ne'
  exact continuousAt_id.mul ((continuous_correction (1/p) ⟨by linarith [ha.1],ha.2⟩ d
    (X/u^p) (div_pos hX huPow)).comp (f := fun t : ℝ => X/t^p) hf)

theorem step_below (p : ℝ) (hp : 1<p) (d : ℕ) (hd : 0<d) (X r u : ℝ)
    (hr : 0<r) (hx : r^p=X) (hu : 0<u) (hur : u<r) :
    u<step p d X u ∧ step p d X u<r := by
  have ha := reciprocal_exponent p hp
  have hru : 1<r/u := (one_lt_div hu).mpr hur
  have hres : X/u^p=(r/u)^p := by rw [div_rpow hr.le hu.le,hx]
  have hroot : ((r/u)^p)^(1/p)=r/u := by
    rw [one_div,rpow_rpow_inv (div_pos hr hu).le (by linarith : p≠0)]
  obtain ⟨h1,h2⟩ := above_one_below_root (1/p) ha d hd ((r/u)^p)
    (one_lt_rpow hru (by linarith))
  rw [hroot] at h2
  unfold step; rw [hres]
  constructor
  · simpa using mul_lt_mul_of_pos_left h1 hu
  · have h := mul_lt_mul_of_pos_left h2 hu
    have he : u*(r/u)=r := by field_simp
    rwa [he] at h

theorem step_above (p : ℝ) (hp : 1<p) (d : ℕ) (hd : 0<d) (X r u : ℝ)
    (hr : 0<r) (hx : r^p=X) (hru : r<u) :
    r<step p d X u ∧ step p d X u<u := by
  have hu : 0<u := hr.trans hru
  have ha := reciprocal_exponent p hp
  have hq : r/u<1 := (div_lt_one hu).mpr hru
  have hq0 := div_pos hr hu
  have hres : X/u^p=(r/u)^p := by rw [div_rpow hr.le hu.le,hx]
  have hroot : ((r/u)^p)^(1/p)=r/u := by
    rw [one_div,rpow_rpow_inv hq0.le (by linarith : p≠0)]
  obtain ⟨h1,h2⟩ := below_one_above_root (1/p) ha d hd ((r/u)^p)
    (rpow_pos_of_pos hq0 _) (rpow_lt_one hq0.le hq (by linarith))
  rw [hroot] at h1
  unfold step; rw [hres]
  constructor
  · have h := mul_lt_mul_of_pos_left h1 hu
    have he : u*(r/u)=r := by field_simp
    rwa [he] at h
  · simpa using mul_lt_mul_of_pos_left h2 hu

/-- Every positive starting estimate converges, without a dyadic guard or entry assumption. -/
theorem global_convergence (p : ℝ) (hp : 1<p) (d : ℕ) (hd : 0<d) (X u : ℝ)
    (hX : 0<X) (hu : 0<u) :
    Tendsto (fun n : ℕ => (step p d X)^[n] u) atTop (𝓝 (X^(1/p))) := by
  let r := X^(1/p)
  have hr : 0<r := rpow_pos_of_pos hX _
  have hx : r^p=X := by dsimp [r]; rw [one_div,rpow_inv_rpow hX.le (by linarith : p≠0)]
  have ha := reciprocal_exponent p hp
  apply LeanMath.Papers.Iteration.converge (step p d X) r u hr hu
  · exact fun t ht => continuous_step p hp d X t hX ht
  · unfold step
    rw [← hx,div_self (rpow_pos_of_pos hr p).ne',correction_one (1/p) ⟨by linarith [ha.1],ha.2⟩ d,mul_one]
  · exact fun t ht htr => step_below p hp d hd X r t hr hx ht htr
  · exact fun t htr => step_above p hp d hd X r t hr hx htr

/-- The iteration just proved globally convergent uses a genuine classical diagonal pair. -/
theorem classical_diagonal (p : ℝ) (hp : 1<p) (d : ℕ) :
    LeanMath.Papers.V14PadeTheorem.IsDiagonal (1/p) d
      (LeanMath.Papers.V14DiagonalContact.numerator (1/p) d)
      (LeanMath.Papers.V14DiagonalContact.denominator (1/p) d) := by
  have ha := reciprocal_exponent p hp
  exact LeanMath.Papers.V14DiagonalContact.isDiagonal (1/p) ⟨by linarith [ha.1],ha.2⟩ d

end LeanMath.Papers.V14DiagonalConvergence
