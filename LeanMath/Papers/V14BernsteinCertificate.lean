import LeanMath.Papers.V14RationalCertificate
import Mathlib.RingTheory.Polynomial.Bernstein

/-! Soundness of finite Bernstein certificates for derivative enclosures. -/
noncomputable section
namespace LeanMath.Papers.V14BernsteinCertificate
open Polynomial Finset Set

/-- A finite Bernstein expansion. The coefficients are exact rationals. -/
def expansion (n : ℕ) (b : ℕ → ℚ) : ℝ[X] :=
  ∑ k ∈ range (n+1), C (b k : ℝ)*bernsteinPolynomial ℝ n k

theorem basis_nonneg (n k : ℕ) (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    0≤(bernsteinPolynomial ℝ n k).eval x := by
  simp only [bernsteinPolynomial,eval_mul,eval_natCast,eval_pow,eval_X,eval_sub,eval_one]
  have hx0 := hx.1
  have h : 0≤1-x := by linarith [hx.2]
  positivity

theorem expansion_bounds (n : ℕ) (b : ℕ → ℚ) (lo hi : ℚ)
    (hb : ∀ k≤n, lo≤b k ∧ b k≤hi) (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    (lo:ℝ)≤(expansion n b).eval x ∧ (expansion n b).eval x≤(hi:ℝ) := by
  have hs : ∑ k ∈ range (n+1), (bernsteinPolynomial ℝ n k).eval x = 1 := by
    rw [← eval_finsetSum,bernsteinPolynomial.sum]; simp
  have hnon : ∀ k : ℕ, 0≤(bernsteinPolynomial ℝ n k).eval x :=
    fun k => basis_nonneg n k x hx
  simp only [expansion,eval_finsetSum,eval_mul,eval_C]
  constructor
  · calc
      (lo:ℝ) = ∑ k ∈ range (n+1), (lo:ℝ)*(bernsteinPolynomial ℝ n k).eval x := by rw [← mul_sum,hs,mul_one]
      _ ≤ _ := sum_le_sum fun k hk => mul_le_mul_of_nonneg_right
        (by exact_mod_cast (hb k (by simpa using hk)).1) (hnon k)
  · calc
      _ ≤ ∑ k ∈ range (n+1), (hi:ℝ)*(bernsteinPolynomial ℝ n k).eval x :=
        sum_le_sum fun k hk => mul_le_mul_of_nonneg_right
          (by exact_mod_cast (hb k (by simpa using hk)).2) (hnon k)
      _ = (hi:ℝ) := by rw [← mul_sum,hs,mul_one]

/-- A polynomial identity plus finite coefficient bounds certify an entire interval. -/
theorem interval_bounds (P : ℝ[X]) (l r : ℚ) (hlr : l<r) (n : ℕ) (b : ℕ → ℚ)
    (hid : P.comp (C (l:ℝ)+C ((r-l:ℚ):ℝ)*X)=expansion n b)
    (lo hi : ℚ) (hb : ∀ k≤n, lo≤b k ∧ b k≤hi)
    (y : ℝ) (hy : y ∈ Set.Icc (l:ℝ) (r:ℝ)) :
    (lo:ℝ)≤P.eval y ∧ P.eval y≤(hi:ℝ) := by
  have hd : (0:ℝ)<(r:ℝ)-(l:ℝ) := by exact_mod_cast sub_pos.mpr hlr
  let x : ℝ := (y-l)/(r-l)
  have hx : x ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hy.1) hd.le
    · exact (div_le_one hd).mpr (by linarith [hy.2])
  have he := congrArg (Polynomial.eval x) hid
  simp only [eval_comp,eval_add,eval_C,eval_mul,eval_X,Rat.cast_sub] at he
  have hxy : (l:ℝ)+((r:ℝ)-(l:ℝ))*x=y := by dsimp [x]; field_simp; ring
  rw [hxy] at he
  rw [he]
  exact expansion_bounds n b lo hi hb x hx

/-- Nonnegative Bernstein coefficients certify a nonnegative polynomial. -/
theorem interval_nonneg (P : ℝ[X]) (l r : ℚ) (hlr : l<r) (n : ℕ) (b : ℕ → ℚ)
    (hid : P.comp (C (l:ℝ)+C ((r-l:ℚ):ℝ)*X)=expansion n b)
    (hb : ∀ k≤n, 0≤b k) (y : ℝ) (hy : y ∈ Set.Icc (l:ℝ) (r:ℝ)) : 0≤P.eval y := by
  let hi := ∑ k ∈ range (n+1), b k
  have hhi : ∀ k≤n, b k≤hi := by
    intro k hk
    exact single_le_sum (fun i hi => hb i (by simpa using hi)) (by simpa using hk)
  simpa only [Rat.cast_zero] using (interval_bounds P l r hlr n b hid 0 hi (fun k hk => ⟨hb k hk,hhi k hk⟩) y hy).1

/-- Two polynomial nonnegativity certificates bound N/D, with no division rounding assumption. -/
theorem quotient_bounds (N D : ℝ[X]) (l r lo hi : ℚ) (hlr : l<r)
    (nL nU : ℕ) (bL bU : ℕ → ℚ)
    (hL : (N-C (lo:ℝ)*D).comp (C (l:ℝ)+C ((r-l:ℚ):ℝ)*X)=expansion nL bL)
    (hU : (C (hi:ℝ)*D-N).comp (C (l:ℝ)+C ((r-l:ℚ):ℝ)*X)=expansion nU bU)
    (hbL : ∀ k≤nL, 0≤bL k) (hbU : ∀ k≤nU, 0≤bU k)
    (y : ℝ) (hy : y ∈ Set.Icc (l:ℝ) (r:ℝ)) (hD : 0<D.eval y) :
    (lo:ℝ)≤N.eval y/D.eval y ∧ N.eval y/D.eval y≤(hi:ℝ) := by
  have hlow := interval_nonneg _ l r hlr nL bL hL hbL y hy
  have hupp := interval_nonneg _ l r hlr nU bU hU hbU y hy
  simp only [eval_sub,eval_mul,eval_C] at hlow hupp
  exact ⟨(le_div_iff₀ hD).mpr (by linarith),(div_le_iff₀ hD).mpr (by linarith)⟩

/-- The proof inputs for one subinterval. All numerical coefficient conditions are finite. -/
structure Segment (N D : ℝ[X]) (l r lo hi : ℚ) where
  degreeLower : ℕ
  degreeUpper : ℕ
  coeffLower : ℕ → ℚ
  coeffUpper : ℕ → ℚ
  identityLower : (N-C (lo:ℝ)*D).comp (C (l:ℝ)+C ((r-l:ℚ):ℝ)*X)=expansion degreeLower coeffLower
  identityUpper : (C (hi:ℝ)*D-N).comp (C (l:ℝ)+C ((r-l:ℚ):ℝ)*X)=expansion degreeUpper coeffUpper
  nonnegLower : ∀ k≤degreeLower, 0≤coeffLower k
  nonnegUpper : ∀ k≤degreeUpper, 0≤coeffUpper k

theorem segment_sound (N D : ℝ[X]) (l r lo hi : ℚ) (hlr : l<r)
    (s : Segment N D l r lo hi) (y : ℝ) (hy : y ∈ Set.Icc (l:ℝ) (r:ℝ)) (hD : 0<D.eval y) :
    (lo:ℝ)≤N.eval y/D.eval y ∧ N.eval y/D.eval y≤(hi:ℝ) :=
  quotient_bounds N D l r lo hi hlr s.degreeLower s.degreeUpper s.coeffLower s.coeffUpper
    s.identityLower s.identityUpper s.nonnegLower s.nonnegUpper y hy hD

def prefixSum (t v : ℕ → ℚ) (i : ℕ) : ℚ := ∑ j ∈ range i, v j*(t (j+1)-t j)

/-- End-to-end soundness: finite Bernstein witnesses and rational prefixSum checks imply
an error bound at every real point of the symmetric gate. -/
theorem uniform_from_segments (A : ℝ[X]) (p rho eta : ℚ) (t lo hi : ℕ → ℚ) (n : ℕ)
    (hp : 0<p) (hrho : rho<1) (he0 : 0≤eta) (he1 : eta<1) (hn : 0<n)
    (ht0 : t 0=0) (htn : t n=rho) (ht : ∀ i<n, t i<t (i+1))
    (hnodes : ∀ i≤n, 0≤t i ∧ t i≤rho)
    (hpos : ∀ y : ℝ, |y|≤(rho:ℝ) → 0<A.eval y)
    (segments : ∀ i<n, Segment
      (LeanMath.Papers.V14RationalCertificate.numerator A (A.comp (-X)) p)
      (LeanMath.Papers.V14RationalCertificate.denominator A (A.comp (-X)) p)
      (t i) (t (i+1)) (lo i) (hi i))
    (hcheck : ∀ i<n,
      |prefixSum t lo i+min 0 (lo i)*(t (i+1)-t i)|≤eta ∧
      |prefixSum t hi i+max 0 (hi i)*(t (i+1)-t i)|≤eta)
    (y : ℝ) (hy : |y|≤(rho:ℝ)) :
    |(A.eval y/A.eval (-y))/(LeanMath.Papers.Cayley.unchi y)^(1/(p:ℝ))-1| ≤ (eta:ℝ)/(1-eta) := by
  apply LeanMath.Papers.V14RationalCertificate.uniform_relative_error A p rho eta
    (fun i => (t i:ℝ)) (fun i => (lo i:ℝ)) (fun i => (hi i:ℝ)) n
    (by exact_mod_cast hp) (by exact_mod_cast hrho) (by exact_mod_cast he0) (by exact_mod_cast he1)
    hn (by simp [ht0]) (by simp [htn])
  · intro i hi; exact_mod_cast (ht i hi).le
  · intro i hi
    constructor
    · exact_mod_cast (hnodes i hi).1
    · exact_mod_cast (hnodes i hi).2
  · exact hpos
  · intro i hi z hz
    have hl : (0:ℝ)≤t i := by exact_mod_cast (hnodes i (by omega)).1
    have hu : (t (i+1):ℝ)≤rho := by exact_mod_cast (hnodes (i+1) (by omega)).2
    have hzr : |z|≤(rho:ℝ) := by rw [abs_of_nonneg (by linarith [hz.1])]; linarith [hz.2]
    have hZ : 0<(A.comp (-X)).eval z := by simpa using hpos (-z) (by simpa using hzr)
    have hmem : z ∈ Set.Ioo (-1) 1 := abs_lt.mp (hzr.trans_lt (by exact_mod_cast hrho))
    exact segment_sound _ _ _ _ _ _ (ht i hi) (segments i hi) z ⟨hz.1.le,hz.2.le⟩
      (LeanMath.Papers.V14RationalCertificate.denominator_pos A (A.comp (-X)) p z
        (by exact_mod_cast hp) hmem (hpos z hzr) hZ)
  · intro i hi
    have hh := hcheck i hi
    simp only [LeanMath.Papers.V14Uniform.lowerSum,LeanMath.Papers.V14Uniform.upperSum]
    unfold prefixSum at hh
    exact_mod_cast hh
  · exact hy

end LeanMath.Papers.V14BernsteinCertificate
