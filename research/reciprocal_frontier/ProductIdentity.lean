import research.reciprocal_frontier.UniformTransfer

noncomputable section
namespace LeanMath.Research.ProductIdentity
open Polynomial
open LeanMath.Papers.V14DiagonalPolynomials

def productOperator (a : ℝ) (d : ℕ) (S : ℝ[X]) : ℝ[X] :=
  theta (theta (theta S)) - C (a^2)*theta S -
  2*X*(theta (theta (theta S)) - C (3*(d:ℝ))*theta (theta S) +
    C (2*(d:ℝ)^2-a^2-d)*theta S + C ((d:ℝ)*(a^2+d))*S) +
  X*(X*(theta (theta (theta S)) - C (6*(d:ℝ))*theta (theta S) +
    C (12*(d:ℝ)^2-a^2)*theta S + C (2*(d:ℝ)*(a^2-4*(d:ℝ)^2))*S))

/-- A third-order polynomial equation for the product, derived from the two
second-order equations without assuming a hypergeometric product formula. -/
theorem product_equation (a : ℝ) (ha : -1<a ∧ a<1) (d : ℕ) :
    productOperator a d (poly a d*poly (-a) d)=0 := by
  have hA := differential_equation a ha.2 d
  have hB := differential_equation (-a) (by linarith [ha.1]) d
  have hA' := congrArg Polynomial.derivative hA
  have hB' := congrArg Polynomial.derivative hB
  simp only [productOperator,theta,derivative_mul,derivative_add,derivative_sub,
    derivative_C,derivative_natCast,derivative_ofNat,derivative_X,derivative_zero,derivative_one,zero_mul,mul_zero,
    zero_add,add_zero,one_mul,mul_one,map_sub,map_add,map_mul,map_neg,map_ofNat,
    map_natCast,map_one,map_pow] at hA hB hA' hB' ⊢
  linear_combination
    X*(X*(1-X)*(hA'*(poly (-a) d)+hB'*(poly a d)) +
      3*(X*(1-X))*(hA*(poly (-a) d).derivative+hB*(poly a d).derivative) +
      (2*(1+(2*(d:ℝ[X])-1)*X)-(1-2*X)+C a*(1-X))*hA*(poly (-a) d) +
      (2*(1+(2*(d:ℝ[X])-1)*X)-(1-2*X)-C a*(1-X))*hB*(poly a d))

/-- No nonzero polynomial solution can have zero constant coefficient. -/
theorem solution_zero (a : ℝ) (ha : -1<a ∧ a<1) (d : ℕ) (S : ℝ[X])
    (h : productOperator a d S=0) (h0 : S.coeff 0=0) : S=0 := by
  apply Polynomial.ext
  intro n
  suffices S.coeff n=0 by simpa
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact h0
    | succ k =>
      have hh := congrArg (fun T : ℝ[X] => T.coeff (k+1)) h
      have hk : S.coeff k=0 := ih k (by omega)
      have hkn : (0:ℝ)≤k := Nat.cast_nonneg k
      have hn : (k:ℝ)+1>0 := by positivity
      have has : a^2<1 := by nlinarith [mul_pos (by linarith : 0<1-a) (by linarith : 0<1+a)]
      have hn2 : ((k:ℝ)+1)^2-a^2>0 := by nlinarith [sq_nonneg (k:ℝ)]
      have hprev : (X*S).coeff k=0 := by
        cases k with
        | zero => simp
        | succ j => simpa using ih j (by omega)
      simp only [productOperator,coeff_sub,coeff_add,coeff_C_mul,coeff_theta,
        mul_assoc,coeff_X_mul,coeff_ofNat_mul,coeff_zero,Nat.cast_add,Nat.cast_one] at hh
      cases k with
      | zero =>
        simp [h0,coeff_theta,coeff_add,coeff_sub,coeff_C_mul] at hh
        have hnz : 1-a^2≠0 := by linarith
        exact (mul_eq_zero.mp (by nlinarith [hh] : (1-a^2)*S.coeff 1=0)).resolve_left hnz
      | succ j =>
        have hj : S.coeff j=0 := ih j (by omega)
        simp only [coeff_X_mul,coeff_add,coeff_sub,coeff_C_mul,coeff_theta,hj,hk,mul_zero,zero_add,add_zero,sub_zero,Nat.cast_add,Nat.cast_one] at hh
        have hnz : ((↑(j+1):ℝ)+1)*(((↑(j+1):ℝ)+1)^2-a^2)≠0 := (mul_pos hn hn2).ne'
        simp only [Nat.cast_add,Nat.cast_one] at hnz ⊢
        apply (mul_eq_zero.mp ?_).resolve_left hnz
        nlinarith [hh]

theorem operator_on_eigenbasis (a : ℝ) (d k : ℕ) (B : ℝ[X])
    (h1 : (X-1)*theta B=(C (2*(d:ℝ)-k)*X-C (k:ℝ))*B) :
    (X-1)*productOperator a d B = (X+1)*B*
      (-C ((k:ℝ)*(k^2-a^2))*(X-1)^2+
        C (2*((d:ℝ)-k)*(2*k+1)*(d+k+1))*X) := by
  have h2 := congrArg theta h1
  have h3 := congrArg theta h2
  simp only [productOperator,theta,derivative_mul,derivative_C,derivative_X,
    derivative_natCast,derivative_ofNat,derivative_zero,derivative_one,
    map_sub,map_add,map_mul,map_neg,map_ofNat,map_natCast,map_one,map_pow,
    zero_mul,mul_zero,zero_add,add_zero,one_mul,mul_one] at h1 h2 h3 ⊢
  linear_combination
    (X-1)^2*h3 +
    (X-1)*((2*(d:ℝ[X])-k)*X-k-(6*(d:ℝ[X])+2)*X)*h2 +
    (-C a^2-2*X*(2*(d:ℝ[X])^2-C a^2-d)+X^2*(12*(d:ℝ[X])^2-C a^2)-
      (X-1)*(1-2*(2*(d:ℝ[X])-k))*X-
      ((2*(d:ℝ[X])-k)*X-k-(6*(d:ℝ[X])+2)*X)*(X-((2*(d:ℝ[X])-k)*X-k)))*h1

def basis (d k : ℕ) : ℝ[X] := X^k*(X-1)^(2*(d-k))

theorem theta_power_shift (n : ℕ) :
    (X-1)*(X : ℝ[X])*(derivative ((X-1 : ℝ[X])^n))=C (n:ℝ)*X*(X-1)^n := by
  cases n with
  | zero => simp
  | succ n => simp only [derivative_pow,derivative_sub,derivative_X,derivative_one,
      sub_zero,mul_one,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one]
              rw [pow_succ]
              ring

theorem basis_eigen (d k : ℕ) (hk : k≤d) :
    (X-1)*theta (basis d k)=(C (2*(d:ℝ)-k)*X-C (k:ℝ))*basis d k := by
  have hX : X*(X^k : ℝ[X]).derivative=C (k:ℝ)*X^k := by
    cases k with
    | zero => simp
    | succ k =>
      rw [derivative_X_pow]
      simp only [Nat.add_sub_cancel]
      rw [pow_succ]
      ring
  have hs := theta_power_shift (2*(d-k))
  have hn : ((2*(d-k):ℕ):ℝ)=2*(d:ℝ)-2*k := by rw [Nat.cast_mul,Nat.cast_sub hk]; norm_num; ring
  simp only [basis,theta,derivative_mul] at *
  rw [hn] at hs
  simp only [map_sub,map_mul,map_ofNat,map_natCast] at hX hs ⊢
  linear_combination (X-1)^(2*(d-k)+1)*hX + X^k*hs

def beta (d k : ℕ) : ℝ := 2*((d:ℝ)-k)*(2*k+1)*(d+k+1)

def q (a : ℝ) (d : ℕ) : ℕ → ℝ
  | 0 => 1
  | k+1 => q a d k * beta d k / (((k:ℝ)+1)*(((k:ℝ)+1)^2-a^2))

theorem q_recurrence (a : ℝ) (ha : -1<a ∧ a<1) (d k : ℕ) :
    q a d (k+1)*(((k:ℝ)+1)*(((k:ℝ)+1)^2-a^2))=q a d k*beta d k := by
  have hk : (0:ℝ)≤k := Nat.cast_nonneg k
  have has : a^2<1 := by nlinarith [mul_pos (by linarith : 0<1-a) (by linarith : 0<1+a)]
  have hn : ((k:ℝ)+1)^2-a^2>0 := by nlinarith [sq_nonneg (k:ℝ)]
  exact div_mul_cancel₀ _ (mul_pos (by positivity) hn).ne'

theorem operator_add (a : ℝ) (d : ℕ) (P Q : ℝ[X]) :
    productOperator a d (P+Q)=productOperator a d P+productOperator a d Q := by
  simp only [productOperator,theta,map_add,derivative_mul,derivative_X]
  ring

theorem operator_C_mul (a c : ℝ) (d : ℕ) (P : ℝ[X]) :
    productOperator a d (C c*P)=C c*productOperator a d P := by
  simp only [productOperator,theta,derivative_mul,derivative_C,derivative_X,map_add,map_sub,zero_mul,zero_add]
  ring

theorem basis_next (d k : ℕ) (hk : k<d) :
    basis d (k+1)*(X-1)^2=X*basis d k := by
  have he : 2*(d-k)=2*(d-(k+1))+2 := by omega
  simp only [basis]
  rw [he,pow_add,pow_succ]
  ring

def partialSum (a : ℝ) (d : ℕ) : ℕ → ℝ[X]
  | 0 => basis d 0
  | k+1 => partialSum a d k+C (q a d (k+1))*basis d (k+1)

theorem partial_equation (a : ℝ) (ha : -1<a ∧ a<1) (d n : ℕ) (hn : n≤d) :
    (X-1)*productOperator a d (partialSum a d n)=
      (X+1)*C (q a d n*beta d n)*X*basis d n := by
  induction n with
  | zero =>
    have hb := operator_on_eigenbasis a d 0 (basis d 0) (basis_eigen d 0 (Nat.zero_le _))
    simp only [Nat.cast_zero,zero_pow (by decide : 2≠0),zero_mul,C_0,neg_zero,zero_add,sub_zero,add_zero] at hb
    dsimp [partialSum,q,beta]
    rw [hb]
    simp only [map_mul,map_ofNat,map_natCast,map_one,map_add,map_zero,Nat.cast_zero,C_eq_natCast]
    ring_nf
    simp
    ring
  | succ n ih =>
    have hi := ih (by omega)
    have hb := operator_on_eigenbasis a d (n+1) (basis d (n+1)) (basis_eigen d (n+1) hn)
    have hnext := basis_next d n (by omega)
    have hq := congrArg Polynomial.C (q_recurrence a ha d n)
    simp only [map_mul,map_sub,map_pow,map_add,map_natCast,map_one,Nat.cast_add,Nat.cast_one] at hq hb
    simp only [partialSum,operator_add,operator_C_mul]
    have he : (X-1)*(productOperator a d (partialSum a d n)+C (q a d (n+1))*productOperator a d (basis d (n+1))) =
      (X+1)*C (q a d n*beta d n)*X*basis d n + C (q a d (n+1))*((X-1)*productOperator a d (basis d (n+1))) := by rw [←hi]; ring
    rw [he,hb]
    simp only [beta,map_mul,map_sub,map_add,map_natCast,map_ofNat,map_one,Nat.cast_add,Nat.cast_one] at hq ⊢
    linear_combination -(X+1)*C (q a d (n+1))*((n+1 : ℝ[X])*((n+1 : ℝ[X])^2-C a^2))*hnext -
      (X+1)*X*basis d n*hq

theorem sum_equation (a : ℝ) (ha : -1<a ∧ a<1) (d : ℕ) :
    productOperator a d (partialSum a d d)=0 := by
  have hh := partial_equation a ha d d le_rfl
  simp only [beta,sub_self,mul_zero,zero_mul,C_0] at hh
  exact (mul_eq_zero.mp hh).resolve_left (by exact X_sub_C_ne_zero 1)

theorem operator_sub (a : ℝ) (d : ℕ) (P Q : ℝ[X]) :
    productOperator a d (P-Q)=productOperator a d P-productOperator a d Q := by
  simp only [productOperator,theta,map_sub,map_add,derivative_mul,derivative_X]
  ring

theorem partial_at_zero (a : ℝ) (d n : ℕ) : (partialSum a d n).eval 0=1 := by
  induction n with
  | zero => simp [partialSum,basis,pow_mul]
  | succ n ih => simp [partialSum,ih,basis,pow_succ]

/-- Unconditional all-degree product representation in a positive even-power basis.
The coefficient recurrence is used directly, avoiding a dependency on Bailey's formula. -/
theorem product_identity (a : ℝ) (ha : -1<a ∧ a<1) (d : ℕ) :
    poly a d*poly (-a) d=partialSum a d d := by
  apply sub_eq_zero.mp
  apply solution_zero a ha d
  · rw [operator_sub,product_equation a ha d,sum_equation a ha d,sub_self]
  · rw [coeff_zero_eq_eval_zero,eval_sub,eval_mul,eval_at_zero,eval_at_zero,partial_at_zero]
    norm_num

theorem partial_eval (a : ℝ) (d n : ℕ) (R : ℝ) :
    (partialSum a d n).eval R=
      ∑ k ∈ Finset.range (n+1), q a d k*(basis d k).eval R := by
  induction n with
  | zero => simp [partialSum,q]
  | succ n ih => simp only [partialSum,eval_add,eval_mul,eval_C,ih,Finset.sum_range_succ]

open LeanMath.Research.UniformTransfer

theorem q_delta (a : ℝ) (ha : -1<a ∧ a<1) (d k : ℕ) :
    q a d k*delta a k=q 0 d k := by
  induction k with
  | zero => simp [q,delta]
  | succ k ih =>
    have hk : (0:ℝ)≤k := Nat.cast_nonneg k
    have has : a^2<1 := by nlinarith [mul_pos (by linarith : 0<1-a) (by linarith : 0<1+a)]
    have hn : ((k:ℝ)+1)^2-a^2≠0 := by nlinarith [sq_nonneg (k:ℝ)]
    have hk1 : (k:ℝ)+1≠0 := by positivity
    calc
      q a d (k+1)*delta a (k+1) =
          (q a d k*delta a k)*beta d k/(((k:ℝ)+1)*((k:ℝ)+1)^2) := by
        simp only [q,delta]
        field_simp [hn,hk1]
        <;> ring
      _ = q 0 d (k+1) := by rw [ih]; simp only [q,zero_pow (by decide : 2≠0),sub_zero]

theorem q_nonnegative (a : ℝ) (ha : -1<a ∧ a<1) (d k : ℕ) (hk : k≤d) :
    0≤q a d k := by
  induction k with
  | zero => norm_num [q]
  | succ k ih =>
    have hkd : (k:ℝ)≤d := by exact_mod_cast (show k≤d by omega)
    have hk0 : (0:ℝ)≤k := Nat.cast_nonneg k
    have has : a^2<1 := by nlinarith [mul_pos (by linarith : 0<1-a) (by linarith : 0<1+a)]
    have hn : 0<((k:ℝ)+1)^2-a^2 := by nlinarith [sq_nonneg (k:ℝ)]
    exact div_nonneg (mul_nonneg (ih (by omega)) (by dsimp [beta]; positivity))
      (mul_pos (by positivity) hn).le

theorem basis_nonnegative (d k : ℕ) (R : ℝ) (hR : 0≤R) : 0≤(basis d k).eval R := by
  simp only [basis,eval_mul,eval_pow,eval_X,eval_sub,eval_one,pow_mul]
  positivity

/-- The former conditional product sandwich is now unconditional for every degree. -/
theorem polynomial_bounds (a : ℝ) (ha : -1<a ∧ a<1) (d : ℕ) (R : ℝ) (hR : 0≤R) :
    ((poly 0 d).eval R)^2 ≤ (poly a d).eval R*(poly (-a) d).eval R ∧
    (poly a d).eval R*(poly (-a) d).eval R ≤ ((poly 0 d).eval R)^2/delta a d := by
  have hpa := congrArg (Polynomial.eval R) (product_identity a ha d)
  have hp0 := congrArg (Polynomial.eval R) (product_identity 0 (by norm_num) d)
  simp only [eval_mul,partial_eval,neg_zero] at hpa hp0
  rw [←pow_two] at hp0
  rw [hpa,hp0]
  have ht : ∀ k≤d, q 0 d k*(basis d k).eval R≤q a d k*(basis d k).eval R ∧
      q a d k*(basis d k).eval R≤(q 0 d k*(basis d k).eval R)/delta a d := by
    intro k hk
    have hdel := delta_positive a ha k
    have hd := delta_positive a ha d
    have hrel : q a d k=q 0 d k/delta a k := (eq_div_iff hdel.ne').mpr (q_delta a ha d k)
    rw [hrel,div_mul_eq_mul_div]
    have hw := mul_nonneg (q_nonnegative 0 (by norm_num) d k hk) (basis_nonnegative d k R hR)
    constructor
    · exact (le_div_iff₀ hdel).mpr (mul_le_of_le_one_right hw (delta_antitone a ha (Nat.zero_le k)))
    · exact div_le_div_of_nonneg_left hw hd (delta_antitone a ha hk)
  constructor
  · exact Finset.sum_le_sum (fun k hk => (ht k (by have := Finset.mem_range.mp hk; omega)).1)
  · rw [Finset.sum_div]
    exact Finset.sum_le_sum (fun k hk => (ht k (by have := Finset.mem_range.mp hk; omega)).2)

end LeanMath.Research.ProductIdentity

#print axioms LeanMath.Research.ProductIdentity.product_equation
#print axioms LeanMath.Research.ProductIdentity.solution_zero
#print axioms LeanMath.Research.ProductIdentity.operator_on_eigenbasis
#print axioms LeanMath.Research.ProductIdentity.theta_power_shift
#print axioms LeanMath.Research.ProductIdentity.basis_eigen
#print axioms LeanMath.Research.ProductIdentity.q_recurrence
#print axioms LeanMath.Research.ProductIdentity.operator_add
#print axioms LeanMath.Research.ProductIdentity.operator_C_mul
#print axioms LeanMath.Research.ProductIdentity.basis_next
#print axioms LeanMath.Research.ProductIdentity.partial_equation
#print axioms LeanMath.Research.ProductIdentity.sum_equation
#print axioms LeanMath.Research.ProductIdentity.operator_sub
#print axioms LeanMath.Research.ProductIdentity.partial_at_zero
#print axioms LeanMath.Research.ProductIdentity.product_identity
#print axioms LeanMath.Research.ProductIdentity.partial_eval
#print axioms LeanMath.Research.ProductIdentity.q_delta
#print axioms LeanMath.Research.ProductIdentity.q_nonnegative
#print axioms LeanMath.Research.ProductIdentity.basis_nonnegative
#print axioms LeanMath.Research.ProductIdentity.polynomial_bounds
