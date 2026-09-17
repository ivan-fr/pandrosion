import LeanMath.Papers.V14DiagonalPolynomials

/-! Exact sign identity for the logarithmic error of diagonal root approximants. -/
noncomputable section
namespace LeanMath.Papers.V14DiagonalWronskian
open Polynomial
open LeanMath.Papers.V14DiagonalPolynomials

def errorPolynomial (a : ℝ) (d : ℕ) : ℝ[X] :=
  C a*poly a d*poly (-a) d - X*((poly a d).derivative*poly (-a) d - poly a d*(poly (-a) d).derivative)

theorem error_ode (a : ℝ) (ha : -1<a ∧ a<1) (d : ℕ) :
    (X-1)*(errorPolynomial a d).derivative = C (2*(d:ℝ))*errorPolynomial a d := by
  have hA := differential_equation a ha.2 d
  have hB := differential_equation (-a) (by linarith [ha.1]) d
  simp only [errorPolynomial,derivative_mul,derivative_C,derivative_X,
    zero_mul,zero_add,one_mul,map_sub,map_add,map_mul,map_neg,map_ofNat,map_natCast,map_one] at hA hB ⊢
  linear_combination (poly (-a) d)*hA - (poly a d)*hB

/-- A polynomial Euler equation at one determines a pure power of X-1. -/
theorem euler_polynomial (P : ℝ[X]) (n : ℕ)
    (h : (X-1)*P.derivative = C (n:ℝ)*P) :
    ∃ c : ℝ, P=C c*(X-1)^n := by
  let Q := P.comp (X+1)
  have hQ : X*Q.derivative = C (n:ℝ)*Q := by
    have hh := congrArg (fun T : ℝ[X] => T.comp (X+1)) h
    simpa [Q,derivative_comp] using hh
  have hc : ∀ k : ℕ, k ≠ n → Q.coeff k=0 := by
    intro k hk
    have hh := congrArg (fun T : ℝ[X] => T.coeff k) hQ
    change (theta Q).coeff k = _ at hh
    rw [coeff_theta,coeff_C_mul] at hh
    have hkn : (k:ℝ) ≠ n := by exact_mod_cast hk
    exact (mul_eq_zero.mp (by nlinarith [hh] : ((k:ℝ)-n)*Q.coeff k=0)).resolve_left (sub_ne_zero.mpr hkn)
  have he : Q=monomial n (Q.coeff n) := by
    apply Polynomial.ext
    intro k
    by_cases hk : k=n
    · subst k; simp
    · simp [coeff_monomial,Ne.symm hk,hc k hk]
  refine ⟨Q.coeff n,?_⟩
  have hh := congrArg (fun T : ℝ[X] => T.comp (X-1)) he
  simpa [Q,Polynomial.comp_assoc,← C_mul_X_pow_eq_monomial] using hh

theorem error_identity (a : ℝ) (ha : -1<a ∧ a<1) (d : ℕ) :
    errorPolynomial a d=C a*(X-1)^(2*d) := by
  obtain ⟨c,hc⟩ := euler_polynomial (errorPolynomial a d) (2*d) (by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using error_ode a ha d)
  have hh := congrArg (Polynomial.eval (0:ℝ)) hc
  have hzero : ∀ b : ℝ, (poly b d).eval 0=1 := by
    intro b; rw [← coeff_zero_eq_eval_zero,coeff_poly,c_zero]
  simp [errorPolynomial,hzero,pow_mul] at hh
  simpa only [hh] using hc

theorem top_product (a : ℝ) (ha : 0<a ∧ a<1) (d : ℕ) : c a d d*c (-a) d d=1 := by
  have hh := congrArg (fun T : ℝ[X] => T.coeff (d+d))
    (error_identity a ⟨by linarith [ha.1],ha.2⟩ d)
  have he : errorPolynomial a d = C a*(poly a d*poly (-a) d) -
      theta (poly a d)*poly (-a) d + poly a d*theta (poly (-a) d) := by
    unfold errorPolynomial theta; ring
  rw [he] at hh
  simp only [coeff_add,coeff_sub,coeff_C_mul,
    coeff_mul_add_eq_of_natDegree_le (degree_le a d) (degree_le (-a) d),
    coeff_mul_add_eq_of_natDegree_le (theta_degree_le a d) (degree_le (-a) d),
    coeff_mul_add_eq_of_natDegree_le (degree_le a d) (theta_degree_le (-a) d),
    coeff_theta,coeff_poly] at hh
  have hp : ((X-1 : ℝ[X])^(2*d)).coeff (d+d)=1 := by
    have he' : (X-1 : ℝ[X])=X+C (-1) := by simp [sub_eq_add_neg]
    rw [he',coeff_X_add_C_pow]
    simp [two_mul]
  rw [hp] at hh
  nlinarith [ha.1]

end LeanMath.Papers.V14DiagonalWronskian
