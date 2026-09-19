import LeanMath.Papers.RectangleInitialization

/-! Exact centered arithmetic identities for the behavioral analog prototype.
These do not certify physical analog errors, circuit timing or transistor behavior. -/
noncomputable section
namespace LeanMath.Papers.AnalogFastAD

theorem centered_square (p n d : ℝ) (hp : p≠0) (hn : n≠0) :
    p/(2*n)*((1+n*d/p)^2-1)=d+n*d^2/(2*p) := by
  field_simp; ring

theorem centered_multiply (p n d q : ℝ) (hp : p≠0) (hn : n+1≠0) :
    p/(n+1)*((1+n*d/p)*(1+q/p)-1)=
      d+(q-d)/(n+1)+n*d*q/(p*(n+1)) := by
  field_simp; ring

theorem centered_ad (p q t : ℝ) (hp : p≠0)
    (hd : p-1+(p+1)*t≠0) (he : 1+t+(t-1)/p≠0) :
    p*((1+q/p)*((p+1+(p-1)*t)/(p-1+(p+1)*t))-1)=
      q+2*(1+q/p)*(1-t)/(1+t+(t-1)/p) := by
  have hn : -1+p+p*t+t≠0 := by convert hd using 1 <;> ring
  field_simp <;> ring_nf <;> field_simp [hn] <;> ring

theorem scaled_decode (p q c : ℝ) :
    c*(1+q/p)=c+c*q/p := by ring

theorem normalized_product (p : ℕ) (X c u : ℝ) :
    X*(c*u)^p=(X*c^p)*u^p := by rw [mul_pow]; ring

theorem error_scaling (p q δ : ℝ) :
    (1+(q+δ)/p)-(1+q/p)=δ/p := by ring

end LeanMath.Papers.AnalogFastAD
