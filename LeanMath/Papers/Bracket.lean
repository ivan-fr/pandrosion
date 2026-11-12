import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic

/-! Reciprocal Geometry, Theorem 4.1. We use an explicit positive root q,
with R=q^p, rather than building root existence into the bracket proof. -/
noncomputable section
namespace LeanMath.Papers.Bracket

def lower (p : ℕ) (R : ℝ) : ℝ := R * ((p : ℝ) / (R + p - 1)) ^ (p-1)
def upper (p : ℕ) (R : ℝ) : ℝ := (lower p R⁻¹)⁻¹

/-- This is exactly the printed one-step closure L_p, not a replacement bound. -/
theorem upper_formula (p : ℕ) (R : ℝ) :
    upper p R = R * (((p:ℝ)-1+R⁻¹)/(p:ℝ))^(p-1) := by
  unfold upper lower
  simp only [mul_inv_rev, ← inv_pow, inv_div, inv_inv]
  rw [mul_comm]
  congr 1
  congr 1 <;> ring

theorem lower_pos (p : ℕ) (R : ℝ) (hp : 1 ≤ p) (hR : 0 < R) : 0 < lower p R := by
  have hp' : (1:ℝ) ≤ p := by exact_mod_cast hp
  have hd : 0 < R + p - 1 := by linarith
  unfold lower
  positivity

theorem power_tangent (p : ℕ) (q : ℝ) (hq : 0 < q) :
    (p : ℝ) * q ≤ q^p + p - 1 := by
  have h := one_add_mul_le_pow (show (-2:ℝ) ≤ q-1 by linarith) p
  rw [show 1+(q-1)=q by ring] at h
  linarith

theorem lower_le_root (p : ℕ) (q : ℝ) (hp : 1 ≤ p) (hq : 0 < q) :
    lower p (q^p) ≤ q := by
  have hp' : (1:ℝ) ≤ p := by exact_mod_cast hp
  have hd : 0 < q^p + p - 1 := by linarith [pow_pos hq p]
  have hbase : q * ((p:ℝ)/(q^p+p-1)) ≤ 1 := by
    rw [← mul_div_assoc]
    apply (div_le_one hd).mpr
    simpa [mul_comm] using power_tangent p q hq
  have hbase0 : 0 ≤ q * ((p:ℝ)/(q^p+p-1)) := by positivity
  have hpow : (q * ((p:ℝ)/(q^p+p-1)))^(p-1) ≤ 1 := pow_le_one₀ hbase0 hbase
  have hsplit : q^p = q * q^(p-1) := by
    rw [← pow_succ']
    congr 1
    omega
  calc lower p (q^p) = q * (q * ((p:ℝ)/(q^p+p-1)))^(p-1) := by
         unfold lower
         rw [mul_pow]
         rw [hsplit]
         ring
       _ ≤ q * 1 := mul_le_mul_of_nonneg_left hpow hq.le
       _ = q := mul_one q

theorem certified_bracket (p : ℕ) (q : ℝ) (hp : 1 ≤ p) (hq : 0 < q) :
    lower p (q^p) ≤ q ∧ q ≤ upper p (q^p) := by
  refine ⟨lower_le_root p q hp hq, ?_⟩
  have h := lower_le_root p q⁻¹ hp (inv_pos.mpr hq)
  have hd := lower_pos p (q⁻¹^p) hp (pow_pos (inv_pos.mpr hq) p)
  have hh := (inv_le_inv₀ (inv_pos.mpr hq) hd).mpr h
  simpa [upper, inv_pow] using hh

theorem kernel_independent_certificate (p : ℕ) (x u r : ℝ)
    (hp : 1 ≤ p) (hu : 0 < u) (hr : 0 < r) (hx : r^p = x) :
    u * lower p (x/u^p) ≤ r ∧ r ≤ u * upper p (x/u^p) := by
  have h := certified_bracket p (r/u) hp (div_pos hr hu)
  rw [div_pow, hx] at h
  have he : u*(r/u)=r := by field_simp
  constructor
  · have hh := mul_le_mul_of_nonneg_left h.1 hu.le
    rwa [he] at hh
  · have hh := mul_le_mul_of_nonneg_left h.2 hu.le
    rwa [he] at hh

end LeanMath.Papers.Bracket
