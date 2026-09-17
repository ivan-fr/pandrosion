import LeanMath.Papers.CoupledPowers
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Topology.Algebra.Polynomial

/-! Exact defect and output-sensitivity formulas from the coupled-powers section. -/
noncomputable section
namespace LeanMath.Papers.V14CoupledOutputs
open Real Filter Asymptotics Polynomial
open scoped Topology

/-- The product residual and the coherence defect jointly determine the root error. -/
theorem log_defect (p X u w : ℝ) (hp : 0<p) (hX : 0<X) (hu : 0<u) (hw : 0<w) :
    log (u/X^(1/p)) = -(log (X/(u*w))+log (w/u^(p-1)))/p := by
  rw [log_div hu.ne' (rpow_pos_of_pos hX _).ne',log_rpow hX,
    log_div hX.ne' (mul_pos hu hw).ne',log_mul hu.ne' hw.ne',
    log_div hw.ne' (rpow_pos_of_pos hu _).ne',log_rpow hu]
  field_simp
  <;> ring

/-- A unit product residual leaves precisely the bias imposed by the invariant defect. -/
theorem product_fixed_bias (p X u w : ℝ) (hp : 0<p) (hX : 0<X) (hu : 0<u)
    (hw : 0<w) (hR : X/(u*w)=1) :
    u/X^(1/p) = (w/u^(p-1))^(-1/p) := by
  have hh := log_defect p X u w hp hX hu hw
  rw [hR,log_one,zero_add] at hh
  rw [← exp_log (div_pos hu (rpow_pos_of_pos hX _)),
    rpow_def_of_pos (div_pos hw (rpow_pos_of_pos hu _)),hh]
  congr 1
  ring

/-- Integer-degree specialization uses exactly the invariant w/u^(p-1) of the recurrence. -/
theorem log_defect_nat (p : ℕ) (hp : 1≤p) (X u w : ℝ)
    (hX : 0<X) (hu : 0<u) (hw : 0<w) :
    log (u/X^(1/(p:ℝ))) = -(log (X/(u*w))+log (w/u^(p-1)))/(p:ℝ) := by
  have hp0 : (0:ℝ)<p := by exact_mod_cast (show 0<p by omega)
  have he : (p:ℝ)-1=((p-1:ℕ):ℝ) := by simp [Nat.cast_sub hp]
  simpa only [he,rpow_natCast] using log_defect p X u w hp0 hX hu hw

/-- Bias formula for the integer-degree coupled iteration at unit product residual. -/
theorem product_fixed_bias_nat (p : ℕ) (hp : 1≤p) (X u w : ℝ)
    (hX : 0<X) (hu : 0<u) (hw : 0<w) (hR : X/(u*w)=1) :
    u/X^(1/(p:ℝ)) = (w/u^(p-1))^(-1/(p:ℝ)) := by
  have hp0 : (0:ℝ)<p := by exact_mod_cast (show 0<p by omega)
  have he : (p:ℝ)-1=((p-1:ℕ):ℝ) := by simp [Nat.cast_sub hp]
  simpa only [he,rpow_natCast] using product_fixed_bias p X u w hp0 hX hu hw hR

/-- The reciprocal second output has the exact relative error -delta/(1+delta). -/
theorem reciprocal_relative_error (p : ℕ) (hp : 1≤p) (r delta : ℝ)
    (hr : 0<r) (hd : -1<delta) :
    (r^p/(r*(1+delta)))/r^(p-1)-1 = -delta/(1+delta) := by
  have he : r^p=r*r^(p-1) := by rw [←pow_succ']; congr 1; omega
  have hd0 : 1+delta≠0 := by linarith
  rw [he]
  field_simp
  <;> ring

/-- Exact relative error of computing the complementary output by a power. -/
theorem power_relative_error (r delta : ℝ) (hr : 0<r) (n : ℕ) :
    (r*(1+delta))^n/r^n-1=(1+delta)^n-1 := by
  rw [mul_pow]
  field_simp

/-- A polynomial identity supplies the full quadratic remainder, including n=0 and n=1. -/
theorem power_remainder_factor (n : ℕ) :
    ∃ P : ℝ[X], ∀ x : ℝ, (1+x)^n-1-(n:ℝ)*x=x^2*P.eval x := by
  induction n with
  | zero => exact ⟨0,by simp⟩
  | succ n ih =>
    obtain ⟨P,hP⟩ := ih
    refine ⟨(1+Polynomial.X)*P+C (n:ℝ),?_⟩
    intro x
    have hh := hP x
    simp only [eval_add,eval_mul,eval_one,eval_X,eval_C,Nat.cast_add,Nat.cast_one,pow_succ]
    have hx := congrArg (fun t : ℝ => x*t) hh
    nlinarith [hx]

/-- The printed O(delta^2) sensitivity law holds for every nonnegative integer exponent. -/
theorem power_remainder (n : ℕ) :
    (fun delta : ℝ => (1+delta)^n-1-(n:ℝ)*delta) =O[𝓝 0] (fun delta => delta^2) := by
  obtain ⟨P,hP⟩ := power_remainder_factor n
  have hb := (P.continuous.tendsto 0).isBigO_one ℝ
  have hh := (isBigO_refl (fun x : ℝ => x^2) (𝓝 0)).mul hb
  simpa only [mul_one,← hP] using hh

/-- The actual powered second output has the same expansion, after normalization by r^n. -/
theorem powered_output_remainder (r : ℝ) (hr : 0<r) (n : ℕ) :
    (fun delta : ℝ => (r*(1+delta))^n/r^n-1-(n:ℝ)*delta)
      =O[𝓝 0] (fun delta => delta^2) := by
  simpa only [power_relative_error r _ hr n] using power_remainder n

end LeanMath.Papers.V14CoupledOutputs
