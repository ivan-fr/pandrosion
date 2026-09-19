import LeanMath.Papers.RectangleDualTransport

/-! Post-V20 rational global order-seven protocol. Algebraic derivative and
incidence certificates; the analytic convergence argument is in the research note. -/
noncomputable section
namespace LeanMath.Papers.RectangleGlobalSeven
open RectangleGeometry

def A (p z : ℝ) := 15*p^3-(9*p^3-6*p)*z^2
def B (p z : ℝ) := 15*p^2-(4*p^2-1)*z^2
def N (p z : ℝ) := A p z-z*B p z
def Q (p z : ℝ) := A p z+z*B p z
def C (p z : ℝ) := N p z/Q p z
def K (p : ℝ) := (p^2-1)*(4*p^2-1)*(9*p^2-1)
def Nd (p z : ℝ) := (-18*p^3+12*p)*z+(12*p^2-3)*z^2-15*p^2

theorem denominator_decomposition (p z : ℝ) :
    B p z=11*p^2+1+(4*p^2-1)*(1-z^2) := by unfold B; ring

theorem lower_bound_certificate (p z : ℝ) :
    5*A p z-9*B p z = 3*(p-3)*(10*p^2-3*p+1) +
      ((p-3)*(45*p^2+99*p+267)+810)*(1-z^2) := by unfold A B; ring

theorem B_positive (p z : ℝ) (hp : 3≤p) (hz : z^2≤1) : 0<B p z := by
  rw [denominator_decomposition]
  have h : 0≤4*p^2-1 := by nlinarith
  have := mul_nonneg h (sub_nonneg.mpr hz)
  nlinarith [sq_nonneg p]

theorem A_lower (p z : ℝ) (hp : 3≤p) (hz : z^2≤1) : 9*B p z≤5*A p z := by
  have h1 : 0≤10*p^2-3*p+1 := by nlinarith [sq_nonneg (p-1)]
  have h2 : 0≤45*p^2+99*p+267 := by positivity
  have h3 := mul_nonneg (sub_nonneg.mpr hp) h2
  have h4 := mul_nonneg (show 0≤3*(p-3) by linarith) h1
  have h5 := mul_nonneg (show 0≤(p-3)*(45*p^2+99*p+267)+810 by linarith) (sub_nonneg.mpr hz)
  have := lower_bound_certificate p z
  linarith

theorem positive_numerator_denominator (p z : ℝ) (hp : 3≤p)
    (hzl : -1<z) (hzu : z<1) : 0<N p z ∧ 0<Q p z := by
  have hz : z^2≤1 := by nlinarith
  have hb := B_positive p z hp hz
  have ha := A_lower p z hp hz
  have h1 := mul_lt_mul_of_pos_right hzu hb
  have h2 := mul_lt_mul_of_pos_right hzl hb
  unfold N Q
  constructor <;> nlinarith

theorem correction_positive (p z : ℝ) (hp : 3≤p)
    (hzl : -1<z) (hzu : z<1) : 0<C p z := by
  have h := positive_numerator_denominator p z hp hzl hzu
  exact div_pos h.1 h.2

theorem correction_factorization_identity (p z : ℝ) :
    C p z=N p z/(N p z-(-2*z*B p z)) := by
  unfold C
  congr 1
  unfold N Q
  ring

theorem fixed_point (p : ℝ) (hp : p≠0) : C p 0=1 := by
  simp [C,N,Q,A,B,hp]

theorem reciprocity (p z : ℝ) (hn : N p z≠0) (hq : Q p z≠0) :
    C p z*C p (-z)=1 := by
  have h1 : N p (-z)=Q p z := by unfold N Q A B; ring
  have h2 : Q p (-z)=N p z := by unfold N Q A B; ring
  unfold C; rw [h1,h2]; field_simp

/-- Numerator of the derivative of 2 atanh(z)/p + log C. -/
theorem global_derivative_certificate (p z : ℝ) :
    2*N p z*Q p z+p*(1-z^2)*(Nd p z*Q p z+Nd p (-z)*N p z)=2*K p*z^6 := by
  unfold N Q A B Nd K; ring

theorem order_seven_coefficient_positive (p : ℝ) (hp : 3≤p) : 0<K p/100800 := by
  have h1 : 0<p^2-1 := by nlinarith
  have h2 : 0<4*p^2-1 := by nlinarith
  have h3 : 0<9*p^2-1 := by nlinarith
  exact div_pos (mul_pos (mul_pos h1 h2) h3) (by norm_num)

theorem affine_transfer (u β : ℝ) :
    On (join (0,1-u) (-1,1+β)) (1,1-(2*u+β)) := by
  dsimp [On,join]; ring

theorem top_projection (v a b : ℝ) (h : b-v≠0) :
    On (join (1,1-v) (a,1-b)) ((b-a*v)/(b-v),1) := by
  dsimp [On,join]; field_simp; ring

theorem first_cayley_join (t X : ℝ) (hX : X≠0) (ht : 2+t≠0) :
    On (join (1,1-t/X) (-2,1+2/X)) (2*(1-t)/(2+t),1) := by
  dsimp [On,join]; field_simp; ring

theorem second_cayley_join (t : ℝ) (ht : 2+t≠0) (h1 : t+1≠0) :
    On (join (2*(1-t)/(2+t),1) (4,-2)) (0,1-(t-1)/(t+1)) := by
  dsimp [On,join]; field_simp; ring

theorem square_center (z : ℝ) (hz : z-2≠0) :
    On (join (0,1-z) (1,-1)) (z/(z-2),1) := by
  dsimp [On,join]; field_simp; ring

theorem square_readout (z : ℝ) (hz : z-2≠0) :
    On (join (1,1-2*z) (z/(z-2),1)) (0,1-z^2) := by
  dsimp [On,join]; field_simp; ring

theorem ratio_readout (z d : ℝ) (hd : d≠0) (h2 : 1-2*d≠0) :
    On (join (1,1-2*z) (1/(1-2*d),1)) (0,1-z/d) := by
  dsimp [On,join]; field_simp; ring

theorem final_readout (s v : ℝ) (h1 : 1+v≠0) (h7 : 7+9*v≠0) :
    On (join (0,1-8*s) (8*(1+v)/(7+9*v),1)) (1,1-s*(1-v)/(1+v)) := by
  have hn : 7+v*9≠0 := by simpa only [mul_comm] using h7
  dsimp [On,join]; field_simp; ring_nf

end LeanMath.Papers.RectangleGlobalSeven
