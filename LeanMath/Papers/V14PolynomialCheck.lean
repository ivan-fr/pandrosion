import LeanMath.Papers.V14PolynomialGate
import LeanMath.Papers.V14BernsteinCertificate

/-! Executable rational polynomial arithmetic with a proved real-polynomial interpretation. -/
namespace LeanMath.Papers.V14PolynomialCheck
open Polynomial
open LeanMath.Papers.V14PolynomialGate

def add : List ℚ → List ℚ → List ℚ
  | [], b => b
  | a, [] => a
  | a::as, b::bs => (a+b)::add as bs

def scale (s : ℚ) : List ℚ → List ℚ := List.map (s*·)

def mul : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | a::as, b => add (scale a b) (0::mul as b)

def power (a : List ℚ) : ℕ → List ℚ
  | 0 => [1]
  | n+1 => mul a (power a n)

def compose : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | a::as, b => add [a] (mul b (compose as b))

def deriv : List ℚ → List ℚ
  | [] => []
  | _::as => add as (0::deriv as)

def bernTerms (n : ℕ) (b : ℕ → ℚ) : ℕ → List ℚ
  | 0 => []
  | k+1 => add (bernTerms n b k)
      (scale (b k * n.choose k) (mul (power [0,1] k) (power [1,-1] (n-k))))

def zeroCheck (a : List ℚ) : Bool := a.all (fun x => x==0)
def equalCheck (a b : List ℚ) : Bool := zeroCheck (add a (scale (-1) b))

theorem of_add (a b : List ℚ) : ofCoeffs (add a b)=ofCoeffs a+ofCoeffs b := by
  induction a generalizing b with
  | nil => simp [add,ofCoeffs]
  | cons a as ih =>
    cases b with
    | nil => simp [add,ofCoeffs]
    | cons b bs => simp [add,ofCoeffs,ih]; ring

theorem of_scale (s : ℚ) (a : List ℚ) : ofCoeffs (scale s a)=C (s:ℝ)*ofCoeffs a := by
  induction a with
  | nil => simp [scale,ofCoeffs]
  | cons a as ih => simp only [scale,List.map_cons,ofCoeffs,Rat.cast_mul,map_mul] at *; rw [ih]; ring

theorem of_mul (a b : List ℚ) : ofCoeffs (mul a b)=ofCoeffs a*ofCoeffs b := by
  induction a with
  | nil => simp [mul,ofCoeffs]
  | cons a as ih => rw [mul,of_add,of_scale]; simp [ofCoeffs,ih]; ring

theorem of_power (a : List ℚ) (n : ℕ) : ofCoeffs (power a n)=(ofCoeffs a)^n := by
  induction n with
  | zero => simp [power,ofCoeffs]
  | succ n ih => rw [power,of_mul,ih,pow_succ'];

theorem of_compose (a b : List ℚ) : ofCoeffs (compose a b)=(ofCoeffs a).comp (ofCoeffs b) := by
  induction a with
  | nil => simp [compose,ofCoeffs]
  | cons a as ih => simp [compose,of_add,of_mul,ofCoeffs,ih]

theorem of_deriv (a : List ℚ) : ofCoeffs (deriv a)=(ofCoeffs a).derivative := by
  induction a with
  | nil => simp [deriv,ofCoeffs]
  | cons a as ih => simp [deriv,of_add,ofCoeffs,ih,derivative_mul]

theorem of_bernTerms (n : ℕ) (b : ℕ → ℚ) (m : ℕ) :
    ofCoeffs (bernTerms n b m)=∑ k ∈ Finset.range m,
      C (b k:ℝ)*bernsteinPolynomial ℝ n k := by
  induction m with
  | zero => simp [bernTerms,ofCoeffs]
  | succ m ih =>
    rw [bernTerms,of_add,ih,Finset.sum_range_succ]
    congr 1
    simp [of_scale,of_mul,of_power,ofCoeffs,bernsteinPolynomial]
    ring

theorem zeroCheck_sound (a : List ℚ) (h : zeroCheck a=true) : ofCoeffs a=0 := by
  induction a with
  | nil => rfl
  | cons a as ih =>
    simp only [zeroCheck,List.all_cons,Bool.and_eq_true,beq_iff_eq] at h
    simp [ofCoeffs,h.1,ih h.2]

theorem equalCheck_sound (a b : List ℚ) (h : equalCheck a b=true) : ofCoeffs a=ofCoeffs b := by
  have hh := zeroCheck_sound _ h
  rw [of_add,of_scale] at hh
  norm_num at hh
  exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using hh)

/-- A finite list computation certifies the exact Bernstein identity over the reals. -/
theorem identity_sound (a : List ℚ) (l r : ℚ) (n : ℕ) (b : ℕ → ℚ)
    (h : equalCheck (compose a [l,r-l]) (bernTerms n b (n+1))=true) :
    (ofCoeffs a).comp (C (l:ℝ)+C ((r-l:ℚ):ℝ)*X)=
      LeanMath.Papers.V14BernsteinCertificate.expansion n b := by
  have hh := equalCheck_sound _ _ h
  rw [of_compose,of_bernTerms] at hh
  simpa [ofCoeffs,LeanMath.Papers.V14BernsteinCertificate.expansion,mul_comm] using hh

def numeratorList (a : List ℚ) (p : ℚ) : List ℚ :=
  let z := compose a [0,-1]
  add (scale p (mul [1,0,-1] (add (mul (deriv a) z) (scale (-1) (mul a (deriv z))))))
    (scale (-2) (mul a z))

def denominatorList (a : List ℚ) (p : ℚ) : List ℚ :=
  scale p (mul [1,0,-1] (mul a (compose a [0,-1])))

theorem numeratorList_sound (a : List ℚ) (p : ℚ) : ofCoeffs (numeratorList a p)=
    LeanMath.Papers.V14RationalCertificate.numerator (ofCoeffs a) ((ofCoeffs a).comp (-X)) p := by
  simp [numeratorList,of_add,of_scale,of_mul,of_deriv,of_compose,ofCoeffs,
    LeanMath.Papers.V14RationalCertificate.numerator]
  ring

theorem denominatorList_sound (a : List ℚ) (p : ℚ) : ofCoeffs (denominatorList a p)=
    LeanMath.Papers.V14RationalCertificate.denominator (ofCoeffs a) ((ofCoeffs a).comp (-X)) p := by
  simp [denominatorList,of_scale,of_mul,of_compose,ofCoeffs,
    LeanMath.Papers.V14RationalCertificate.denominator]
  ring

def nonnegCheck (n : ℕ) (b : ℕ → ℚ) : Bool :=
  (List.range (n+1)).all (fun k => decide (0≤b k))

theorem nonnegCheck_sound (n : ℕ) (b : ℕ → ℚ) (h : nonnegCheck n b=true) :
    ∀ k≤n, 0≤b k := by
  simp only [nonnegCheck,List.all_eq_true,List.mem_range,decide_eq_true_eq] at h
  intro k hk
  exact h k (by omega)

/-- All inputs are checked by finite rational computations; no numerical premise is admitted. -/
def segmentOfChecks (N D : List ℚ) (l r lo hi : ℚ) (n : ℕ) (bL bU : ℕ → ℚ)
    (hL : equalCheck (compose (add N (scale (-lo) D)) [l,r-l]) (bernTerms n bL (n+1))=true)
    (hU : equalCheck (compose (add (scale hi D) (scale (-1) N)) [l,r-l]) (bernTerms n bU (n+1))=true)
    (hbL : nonnegCheck n bL=true) (hbU : nonnegCheck n bU=true) :
    LeanMath.Papers.V14BernsteinCertificate.Segment (ofCoeffs N) (ofCoeffs D) l r lo hi where
  degreeLower := n
  degreeUpper := n
  coeffLower := bL
  coeffUpper := bU
  identityLower := by
    have h := identity_sound _ l r n bL hL
    simpa [of_add,of_scale,sub_eq_add_neg] using h
  identityUpper := by
    have h := identity_sound _ l r n bU hU
    simpa [of_add,of_scale,sub_eq_add_neg] using h
  nonnegLower := nonnegCheck_sound n bL hbL
  nonnegUpper := nonnegCheck_sound n bU hbU

end LeanMath.Papers.V14PolynomialCheck
