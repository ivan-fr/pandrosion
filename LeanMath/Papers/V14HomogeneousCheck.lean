import LeanMath.Papers.V14PolynomialCheck

/-! Clearing denominators before exact polynomial checks. -/
namespace LeanMath.Papers.V14HomogeneousCheck
open Polynomial
open LeanMath.Papers.V14PolynomialGate LeanMath.Papers.V14PolynomialCheck
open LeanMath.Papers.V14BernsteinCertificate

def homogeneous (L W T : ℚ) : List ℚ → List ℚ
  | [] => []
  | a::as => add [a*T^(as.length+1)] (mul [L,W] (homogeneous L W T as))

def shift (k : ℕ) (a : List ℚ) : List ℚ := List.replicate k 0 ++ a

theorem shift_sound (k : ℕ) (a : List ℚ) : ofCoeffs (shift k a)=X^k*ofCoeffs a := by
  induction k with
  | zero => simp [shift]
  | succ k ih => simp [shift,List.replicate_succ,ofCoeffs] at *; rw [ih]; ring

def fastTerms (basis : ℕ → List ℚ) (n : ℕ) (b : ℕ → ℚ) : ℕ → List ℚ
  | 0 => []
  | k+1 => add (fastTerms basis n b k) (shift k (scale (b k*n.choose k) (basis (n-k))))

theorem fastTerms_sound (basis : ℕ → List ℚ) (n : ℕ) (b : ℕ → ℚ) (m : ℕ)
    (hbasis : ∀ j≤n, ofCoeffs (basis j)=(1-X)^j) :
    ofCoeffs (fastTerms basis n b m)=∑ k ∈ Finset.range m,
      C (b k:ℝ)*bernsteinPolynomial ℝ n k := by
  induction m with
  | zero => simp [fastTerms,ofCoeffs]
  | succ m ih =>
    rw [fastTerms,of_add,ih,Finset.sum_range_succ]
    congr 1
    rw [shift_sound,of_scale,hbasis (n-m) (Nat.sub_le _ _)]
    simp [bernsteinPolynomial]
    ring

theorem homogeneous_sound (a : List ℚ) (L W T : ℚ) (hT : T≠0) :
    ofCoeffs (homogeneous L W T a)=C ((T:ℝ)^a.length)*
      (ofCoeffs a).comp (C ((L/T:ℚ):ℝ)+C ((W/T:ℚ):ℝ)*X) := by
  have ht : (T:ℝ)≠0 := by exact_mod_cast hT
  have haff : C (T:ℝ)*(C ((L/T:ℚ):ℝ)+C ((W/T:ℚ):ℝ)*X)=C (L:ℝ)+C (W:ℝ)*X := by
    rw [mul_add,← mul_assoc,← map_mul,← map_mul]
    congr 1 <;> congr 1 <;> push_cast <;> field_simp
  induction a with
  | nil => simp [homogeneous,ofCoeffs]
  | cons a as ih =>
    simp only [homogeneous,of_add,of_mul,ofCoeffs,ih,List.length_cons]
    simp only [mul_zero,add_zero,add_comp,mul_comp,C_comp,X_comp]
    push_cast
    simp only [pow_succ,map_mul]
    have hh := congrArg (fun Q : ℝ[X] => (C ((T:ℝ)^as.length)*(ofCoeffs as).comp
      (C ((L/T:ℚ):ℝ)+C ((W/T:ℚ):ℝ)*X))*Q) haff
    push_cast at hh
    linear_combination -hh

theorem expansion_div (n : ℕ) (b : ℕ → ℚ) (s : ℚ) (hs : s≠0) :
    C (s:ℝ)*expansion n (fun k => b k/s)=expansion n b := by
  have hs' : (s:ℝ)≠0 := by exact_mod_cast hs
  simp only [expansion,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← mul_assoc,← map_mul]
  congr 1
  push_cast
  field_simp

/-- Integer-sized identities suffice after multiplying by positive denominators. -/
theorem scaled_identity_sound (a ai : List ℚ) (s T l r : ℚ) (hs : s≠0) (hT : T≠0)
    (n : ℕ) (b : ℕ → ℚ) (basis : ℕ → List ℚ)
    (hbasis : ∀ j≤n, ofCoeffs (basis j)=(1-X)^j)
    (hcoeff : equalCheck ai (scale s a)=true)
    (hid : equalCheck (homogeneous (T*l) (T*(r-l)) T ai) (fastTerms basis n b (n+1))=true) :
    (ofCoeffs a).comp (C (l:ℝ)+C ((r-l:ℚ):ℝ)*X)=
      expansion n (fun k => b k/(s*T^ai.length)) := by
  have hc := equalCheck_sound _ _ hcoeff
  rw [of_scale] at hc
  have hh := equalCheck_sound _ _ hid
  rw [homogeneous_sound _ _ _ _ hT,fastTerms_sound _ _ _ _ hbasis,hc] at hh
  have hl : T*l/T=l := by field_simp
  have hw : T*(r-l)/T=r-l := by field_simp
  rw [hl,hw,mul_comp,C_comp] at hh
  have hfactor : s*T^ai.length≠0 := mul_ne_zero hs (pow_ne_zero _ hT)
  have hC : (C ((s*T^ai.length:ℚ):ℝ):ℝ[X])≠0 := by
    simpa only [ne_eq,C_eq_zero] using (show ((s*T^ai.length:ℚ):ℝ)≠0 by exact_mod_cast hfactor)
  apply mul_left_cancel₀ hC
  rw [expansion_div n b _ hfactor]
  change _ = expansion n b at hh
  convert hh using 1 <;> push_cast <;> simp only [map_mul] <;> ring

def segmentOfScaledChecks (N D : List ℚ) (l r lo hi s T : ℚ)
    (hs : 0<s) (hT : 0<T) (aiL aiU : List ℚ) (n : ℕ) (bL bU : ℕ → ℚ)
    (basis : ℕ → List ℚ) (hbasis : ∀ j≤n, ofCoeffs (basis j)=(1-X)^j)
    (hcL : equalCheck aiL (scale s (add N (scale (-lo) D)))=true)
    (hcU : equalCheck aiU (scale s (add (scale hi D) (scale (-1) N)))=true)
    (hL : equalCheck (homogeneous (T*l) (T*(r-l)) T aiL) (fastTerms basis n bL (n+1))=true)
    (hU : equalCheck (homogeneous (T*l) (T*(r-l)) T aiU) (fastTerms basis n bU (n+1))=true)
    (hbL : nonnegCheck n bL=true) (hbU : nonnegCheck n bU=true) :
    Segment (ofCoeffs N) (ofCoeffs D) l r lo hi where
  degreeLower := n
  degreeUpper := n
  coeffLower := fun k => bL k/(s*T^aiL.length)
  coeffUpper := fun k => bU k/(s*T^aiU.length)
  identityLower := by
    have h := scaled_identity_sound _ aiL s T l r hs.ne' hT.ne' n bL basis hbasis hcL hL
    simpa [of_add,of_scale,sub_eq_add_neg] using h
  identityUpper := by
    have h := scaled_identity_sound _ aiU s T l r hs.ne' hT.ne' n bU basis hbasis hcU hU
    simpa [of_add,of_scale,sub_eq_add_neg] using h
  nonnegLower := fun k hk => div_nonneg (nonnegCheck_sound n bL hbL k hk)
    (mul_nonneg hs.le (pow_nonneg hT.le _))
  nonnegUpper := fun k hk => div_nonneg (nonnegCheck_sound n bU hbU k hk)
    (mul_nonneg hs.le (pow_nonneg hT.le _))

end LeanMath.Papers.V14HomogeneousCheck
