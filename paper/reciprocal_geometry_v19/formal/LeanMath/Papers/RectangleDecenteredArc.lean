import LeanMath.Papers.RectangleFixedCircle

/-! Algebraic certificates for the decentered AD arc. The analytic global
convergence proof and full geometric protocol are stated in the paper. -/
namespace LeanMath.Papers.RectangleDecenteredArc
noncomputable section

def rad (p t : ℝ) := ((p-2)*(t^2+1)+(10*p+4)*t)/(12*p)
def auxA (p t : ℝ) := (p-1)*(t^2+1)+(10*p+2)*t
def auxB (p t : ℝ) := (t+1)*(6*p*t-(t-1)^2)
def auxK (p t : ℝ) := (p^2-5*p-2)*(t-1)^2+12*p*(3*p+1)*t

theorem rad_one (p : ℝ) (hp : p≠0) : rad p 1=1 := by
  unfold rad; field_simp; ring

theorem reciprocal_radicand (p t : ℝ) (hp : p≠0) (ht : t≠0) :
    rad p (1/t)=rad p t/t^2 := by
  unfold rad; field_simp; ring

theorem square_certificate (p t : ℝ) (hp : p≠0) :
    rad p t*(auxA p t)^2-(auxB p t)^2 =
      (p+1)*(t-1)^4*auxK p t/(12*p) := by
  unfold rad auxA auxB auxK; field_simp; ring

theorem sign_decomposition (p t : ℝ) :
    auxK p t=6*p^2*(p+1)*t+(p^2-5*p-2)*((t-1)^2-6*p*t) := by
  unfold auxK; ring

theorem derivative_numerator (p t q : ℝ) (hp : p≠0)
    (hq : q^2=rad p t) :
    let g := (p-1)*q
    g*(1+g)*(t+g) + p*t*((t-1)*(p-1)^2*((p-2)*2*t+10*p+4)/(24*p)-g*(1+g)) =
      (p-2)*(p-1)^2/(12*p)*(q*auxA p t-auxB p t) := by
  dsimp
  have hid :
      ((p-1)*q)*(1+(p-1)*q)*(t+(p-1)*q) +
        p*t*((t-1)*(p-1)^2*((p-2)*2*t+10*p+4)/(24*p)-((p-1)*q)*(1+(p-1)*q)) -
        (p-2)*(p-1)^2/(12*p)*(q*auxA p t-auxB p t) =
      (p-1)^2*(p*q-p*t-q+t+1)*(q^2-rad p t) := by
    unfold auxA auxB rad; field_simp; ring
  rw [hq] at hid
  nlinarith

theorem circle_height (alpha t : ℝ) :
    (t+alpha)^2-(alpha^2-1)=t^2+2*alpha*t+1 := by ring

theorem report_identity (t g : ℝ) :
    (1+g)/(1+g-1+t)=(1+g)/(t+g) := by ring_nf

theorem correction_direction (t g : ℝ) (h : t+g≠0) :
    (1+g)/(t+g)-1=(1-t)/(t+g) := by field_simp; ring

theorem reciprocal_correction (t g : ℝ) (ht : t≠0)
    (h1 : 1+g≠0) (h2 : t+g≠0) :
    ((1+g/t)/(1/t+g/t))*((1+g)/(t+g))=1 := by
  field_simp

theorem cubic_error_coefficient :
    ((3:ℝ)-2)*(3^2-1)*(3*3+1)/1440=1/18 := by norm_num

end
end LeanMath.Papers.RectangleDecenteredArc
