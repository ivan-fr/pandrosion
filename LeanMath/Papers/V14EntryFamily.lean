import LeanMath.Papers.V14Entry

/-! The exact ceiling-log denominator for the degree family in Proposition 13.2. -/
noncomputable section
namespace LeanMath.Papers.V14EntryFamily
open LeanMath.Papers

theorem clog_degree (k : ℕ) (hk : 2 ≤ k) : Nat.clog 2 (2^k-1)=k := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hk
  have hn : 2 ≤ 2^(n+1) := by
    have h : 1 ≤ 2^n := Nat.one_le_pow n 2 (by decide)
    rw [pow_succ]
    omega
  apply Nat.le_antisymm
  · apply Nat.clog_le_of_le_pow
    exact Nat.sub_le _ _
  · have h : n+1 < Nat.clog 2 (2^(2+n)-1) := by
      apply (Nat.lt_clog_iff_pow_lt (by decide : 1<2)).mpr
      have he : 2^(2+n) = 2^(n+1)*2 := by
        rw [← pow_succ]; congr 1; omega
      rw [he]
      omega
    omega

theorem denominator_degree (k : ℕ) (hk : 2 ≤ k) :
    Dyadic.denominator (2^k-1) 0 = (2^k-1)+1 := by
  rw [Dyadic.denominator,clog_degree k hk,Nat.add_zero]
  have h : 1 ≤ 2^k := Nat.one_le_pow k 2 (by decide)
  omega

theorem chosen_correction (k : ℕ) (hk : 2 ≤ k) (R : ℝ) :
    Dyadic.correction (2^k-1 : ℕ) (Dyadic.denominator (2^k-1) 0) R =
      R ^ (1/((2^k-1 : ℕ)+1 : ℝ)) := by
  have hpow : 4 ≤ (2:ℕ)^k := by
    calc 4 = (2:ℕ)^2 := by norm_num
         _ ≤ 2^k := Nat.pow_le_pow_right (by decide) hk
  have hp : (2:ℝ) < (2^k-1 : ℕ) := by exact_mod_cast (show 2 < (2:ℕ)^k-1 by omega)
  rw [denominator_degree k hk,Nat.cast_add,Nat.cast_one]
  exact V14Entry.entry_correction _ R hp

/-- The actual selected dyadic update has the recurrent residual used in Proposition 13.2. -/
theorem chosen_residual (k : ℕ) (hk : 2 ≤ k) (R : ℝ) (hR : 0 < R) :
    R / (Dyadic.correction (2^k-1 : ℕ) (Dyadic.denominator (2^k-1) 0) R)^(2^k-1 : ℕ) =
      R ^ (1/((2^k-1 : ℕ)+1 : ℝ)) := by
  rw [chosen_correction k hk R]
  rw [← Real.rpow_mul_natCast hR.le]
  have he : (1/((2^k-1 : ℕ)+1 : ℝ))*((2^k-1 : ℕ):ℝ) =
      1-1/((2^k-1 : ℕ)+1 : ℝ) := by
    field_simp
    ring
  rw [he,Real.rpow_sub hR,Real.rpow_one]
  exact div_div_cancel₀ hR.ne'

end LeanMath.Papers.V14EntryFamily
