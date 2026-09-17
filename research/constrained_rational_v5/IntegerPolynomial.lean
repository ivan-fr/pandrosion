import research.constrained_rational_v5.HornerPositive
set_option maxHeartbeats 0
namespace IntegerPolynomial
noncomputable def eval : List ℤ → ℝ → ℝ
 | [], _ => 0
 | a::p, y => (a:ℝ)+y*eval p y

def add : List ℤ → List ℤ → List ℤ
 | [], q => q
 | p, [] => p
 | a::p,b::q => (a+b)::add p q

def scale (a : ℤ) : List ℤ → List ℤ
 | [] => []
 | b::p => (a*b)::scale a p

def mul : List ℤ → List ℤ → List ℤ
 | [], _ => []
 | a::p,q => add (scale a q) (0::mul p q)

def pow (p : List ℤ) : ℕ → List ℤ
 | 0 => [1]
 | n+1 => mul p (pow p n)

def bern : List ℕ → List ℤ → List ℤ → List ℤ
 | [], _, _ => []
 | [a], _, _ => [a]
 | a::b::w,u,v => add (scale a (pow v (w.length+1))) (mul u (bern (b::w) u v))

theorem eval_add (p q : List ℤ) (y : ℝ) : eval (add p q) y = eval p y+eval q y := by
 induction p generalizing q with
 | nil => simp [add,eval]
 | cons a p ih =>
   cases q with
   | nil => simp [add,eval]
   | cons b q => simp only [add,eval,Int.cast_add,ih]; ring

theorem eval_scale (a : ℤ) (p : List ℤ) (y : ℝ) : eval (scale a p) y = (a:ℝ)*eval p y := by
 induction p with
 | nil => simp [scale,eval]
 | cons b p ih => simp only [scale,eval,Int.cast_mul,ih]; ring

theorem eval_mul (p q : List ℤ) (y : ℝ) : eval (mul p q) y = eval p y*eval q y := by
 induction p with
 | nil => simp [mul,eval]
 | cons a p ih => simp only [mul,eval_add,eval_scale,eval,Int.cast_zero,ih]; ring

theorem eval_pow (p : List ℤ) (n : ℕ) (y : ℝ) : eval (pow p n) y = eval p y^n := by
 induction n with
 | zero => simp [pow,eval]
 | succ n ih => simp only [pow,eval_mul,ih,pow_succ]; ring

theorem eval_bern (w : List ℕ) (u v : List ℤ) (y : ℝ) :
 eval (bern w u v) y = HornerCertificate.bern w (eval u y) (eval v y) := by
 induction w with
 | nil => simp [bern,eval,HornerCertificate.bern]
 | cons a w ih =>
   cases w with
   | nil => simp [bern,eval,HornerCertificate.bern]
   | cons b w =>
     rw [bern,eval_add,eval_scale,eval_mul,eval_pow,ih]
     simp [HornerCertificate.bern,List.length_cons]

theorem certificate (p : List ℤ) (k K : ℕ) (w : List ℕ) (L H D : ℤ) (y : ℝ)
 (hK : 0<K) (hy : 0≤y) (hl : 0≤(D:ℝ)*y-L) (hh : 0≤(H:ℝ)-D*y)
 (identity : scale K p = mul (pow [0,1] k) (bern w [-L,D] [H,-D])) : 0≤eval p y := by
 have hi := congrArg (fun q => eval q y) identity
 rw [eval_scale,eval_mul,eval_pow,eval_bern] at hi
 simp only [eval,Int.cast_natCast,Int.cast_zero,Int.cast_one,Int.cast_neg,mul_zero,add_zero,mul_one,zero_add] at hi
 have heq1 : -(L:ℝ)+y*D = (D:ℝ)*y-L := by ring
 have heq2 : (H:ℝ)+y*(-D) = (H:ℝ)-D*y := by ring
 rw [heq1,heq2] at hi
 have hp := mul_nonneg (pow_nonneg hy k) (HornerCertificate.bern_nonnegative w _ _ hl hh)
 rw [←hi] at hp
 exact nonneg_of_mul_nonneg_right hp (by exact_mod_cast hK)

example : pow [1,1] 3 = [1,3,3,1] := by decide +kernel
#print axioms certificate
end IntegerPolynomial
