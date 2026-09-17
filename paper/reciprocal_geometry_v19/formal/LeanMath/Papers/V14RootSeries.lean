import LeanMath.Papers.V14Pade
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Inverse

/-! Explicit binomial root series and its reciprocal coordinate. -/
noncomputable section
namespace LeanMath.Papers.V14RootSeries
open PowerSeries
abbrev PS := PowerSeries ℝ

def rootSeries (a : ℝ) : PS := binomialSeries ℝ a * rescale (-1) (binomialSeries ℝ (-a))
def coordinate (a : ℝ) : PS := (rootSeries a-1)*(rootSeries a+1)⁻¹

theorem root_constant (a : ℝ) : constantCoeff (rootSeries a)=1 := by
  simp only [rootSeries,map_mul,binomialSeries_constantCoeff,one_mul]
  rw [← coeff_zero_eq_constantCoeff_apply,coeff_rescale]
  simp

theorem root_add (a b : ℝ) : rootSeries (a+b)=rootSeries a*rootSeries b := by
  simp only [rootSeries,neg_add,binomialSeries_add,map_mul]
  ring

theorem root_zero : rootSeries 0=1 := by simp [rootSeries]

theorem root_pow (a : ℝ) (n : ℕ) : (rootSeries a)^n=rootSeries ((n:ℝ)*a) := by
  induction n with
  | zero => simp [root_zero]
  | succ n ih => rw [pow_succ,ih,Nat.cast_add,Nat.cast_one,add_mul,one_mul,root_add]

theorem root_opposite (a : ℝ) : rootSeries a*rootSeries (-a)=1 := by
  rw [← root_add,add_neg_cancel,root_zero]

theorem root_reflection (a : ℝ) : rescale (-1) (rootSeries a)=rootSeries (-a) := by
  simp [rootSeries,rescale_rescale,mul_comm]

/-- The p-th power of the selected series is the residual (1+y)/(1-y). -/
theorem root_equation (p : ℕ) (hp : 0 < p) :
    (rootSeries (1/(p:ℝ)))^p*(1-X)=1+X := by
  have hp0 : (p:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
  rw [root_pow,mul_one_div_cancel hp0]
  have h1 : binomialSeries ℝ (1:ℝ)=1+X := by
    simpa using (binomialSeries_nat (R:=ℝ) (A:=ℝ) 1)
  have h := congrArg (rescale (-1:ℝ))
    (show binomialSeries ℝ (-1:ℝ)*binomialSeries ℝ (1:ℝ)=1 by rw [←binomialSeries_add]; norm_num)
  rw [h1] at h
  simp at h
  simp only [← sub_eq_add_neg] at h
  unfold rootSeries
  rw [h1,mul_assoc,h,mul_one]

theorem coordinate_equation (a : ℝ) : coordinate a*(rootSeries a+1)=rootSeries a-1 := by
  have hc : constantCoeff (rootSeries a+1) ≠ 0 := by simp [root_constant]
  unfold coordinate
  rw [mul_assoc,PowerSeries.inv_mul_cancel _ hc,mul_one]

theorem coordinate_odd (a : ℝ) : rescale (-1) (coordinate a) = -coordinate a := by
  have h := congrArg (rescale (-1:ℝ)) (coordinate_equation a)
  simp only [map_mul,map_add,map_sub,map_one,root_reflection] at h
  have h' := congrArg (fun t : PS => t*rootSeries a) h
  have hr := root_opposite (-a)
  simp only [neg_neg] at hr
  have he : rescale (-1) (coordinate a)*(rootSeries a+1)=1-rootSeries a := by
    calc
      _ = (rescale (-1) (coordinate a)*(rootSeries (-a)+1))*rootSeries a := by
        rw [mul_assoc,add_mul,hr,one_mul]; ring
      _ = _ := by rw [h]; rw [sub_mul,hr,one_mul]
  have hn : rootSeries a+1 ≠ 0 := by
    intro hh
    have hc := congrArg constantCoeff hh
    simp [root_constant] at hc
  apply mul_right_cancel₀ hn
  rw [neg_mul,coordinate_equation,he]
  ring

theorem even_coordinate_coeff (a : ℝ) (n : ℕ) : coeff (2*n) (coordinate a)=0 := by
  have hh := congrArg (coeff (2*n)) (coordinate_odd a)
  simp only [coeff_rescale,map_neg,pow_mul,neg_one_sq,one_pow,one_mul] at hh
  linarith

/-- The series in z=y² is extracted from the odd reciprocal coordinate. -/
def compressed (a : ℝ) : PS := mk fun n => coeff (2*n+1) (coordinate a)

theorem compressed_identity (a : ℝ) :
    coordinate a = X*expand 2 (by decide) (compressed a) := by
  ext k
  cases k with
  | zero => simpa using even_coordinate_coeff a 0
  | succ k =>
    rw [coeff_succ_X_mul]
    by_cases hk : 2 ∣ k
    · obtain ⟨n,rfl⟩ := hk
      rw [coeff_expand_mul]
      simp [compressed]
    · rw [coeff_expand_of_not_dvd 2 (by decide) _ hk]
      have hkmod : k % 2 ≠ 0 := by simpa only [Nat.dvd_iff_mod_eq_zero] using hk
      have he : 2 ∣ k+1 := by omega
      obtain ⟨n,hn⟩ := he
      rw [hn]
      exact even_coordinate_coeff a n

/-- The target relation required by the Padé lift is proved for the explicit root series. -/
theorem target_relation (a : ℝ) :
    rootSeries a-1 = X*expand 2 (by decide) (compressed a)*(rootSeries a+1) := by
  rw [← compressed_identity,coordinate_equation]

/-- Root-specific contact lifting, with no additional target-series hypothesis. -/
theorem root_lift_contact (a : ℝ) (P Q : Polynomial ℝ) (d : ℕ)
    (hmatch : V14Pade.Matches (compressed a) P Q d) :
    V14Pade.Matches (rootSeries a) (V14Pade.numerator P Q) (V14Pade.denominator P Q) (2*d+1) :=
  V14Pade.lift_contact _ _ _ _ _ hmatch (target_relation a)

/-- Identification with the diagonal member of the explicit binomial root series. -/
theorem root_diagonal_identification (a : ℝ) (P Q A B : Polynomial ℝ) (m n : ℕ)
    (hP : P.natDegree ≤ m) (hQ : Q.natDegree ≤ n) (hbal : n=m ∨ n=m+1)
    (hmatch : V14Pade.Matches (compressed a) P Q (m+n+1))
    (hA : A.natDegree ≤ m+n+1) (hB : B.natDegree ≤ m+n+1)
    (hdiag : V14Pade.Matches (rootSeries a) A B (2*(m+n+1)+1)) :
    V14Pade.numerator P Q*B=A*V14Pade.denominator P Q :=
  V14Pade.near_balanced_identification _ _ _ _ _ _ _ _ hP hQ hbal hmatch (target_relation a) hA hB hdiag

end LeanMath.Papers.V14RootSeries
