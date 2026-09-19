import LeanMath.Papers.RectangleDualTransport

/-! Exact algebraic jets for two reciprocal one-radical candidates.
The analytic step converting denominator jets into local convergence orders is
written in research/geometric_factorization/report.md, not asserted by these
finite algebraic certificates. Neither candidate is globally real. -/
noncomputable section
namespace LeanMath.Papers.RectangleFactorizationJets

def a7 (p : ℝ) := 3*p*(p^2+1)/(2*(4*p^2-1))
def c7 (p : ℝ) := 5*p*(p^2-1)/(2*(4*p^2-1))
def d7 (p : ℝ) := -4*(4*p^2-1)/(15*p^2)
def a9 (p : ℝ) := 3*p*(71*p^4+90*p^2-26)/(5*(11*p^2-2)^2)
def b9 (p : ℝ) := (p^2-4)*(p^2-1)/(15*p*(11*p^2-2))
def c9 (p : ℝ) := 98*p*(p^2-1)*(4*p^2-1)/(5*(11*p^2-2)^2)
def d9 (p : ℝ) := -2*(11*p^2-2)/(21*p^2)
def target2 (p : ℝ) := -(p^2-1)/(3*p)
def target4 (p : ℝ) := -(p^2-1)*(4*p^2-1)/(45*p^3)
def target6 (p : ℝ) := -(p^2-1)*(4*p^2-1)*(11*p^2-2)/(945*p^5)
def target8 (p : ℝ) := -(p^2-1)*(4*p^2-1)*(107*p^4-35*p^2+3)/(14175*p^7)
def cayley (z D : ℝ) := (D-z)/(D+z)

theorem correction_factorization_identity (z D : ℝ) :
    cayley z D=(D-z)/((D-z)-(-2*z)) := by
  unfold cayley; congr 1; ring

theorem fixed_point_identity (D : ℝ) (h : D≠0) : cayley 0 D=1 := by
  simp [cayley,h]

theorem reciprocal_identity (z D : ℝ) (hm : D-z≠0) (hp : D+z≠0) :
    cayley z D*cayley (-z) D=1 := by
  unfold cayley
  have hn : D + -z ≠ 0 := by simpa only [sub_eq_add_neg] using hm
  field_simp [hm, hp, hn] <;> ring

theorem seven_jet (p : ℝ) (hp : p≠0) (h4 : 4*p^2-1≠0) :
    a7 p+c7 p=p ∧ c7 p*d7 p/2=target2 p ∧
    -c7 p*(d7 p)^2/8=target4 p := by
  have hn : -1 + p^2*4 ≠ 0 := by convert h4 using 1 <;> ring
  unfold a7 c7 d7 target2 target4
  refine ⟨?_,?_,?_⟩ <;> field_simp [hp, h4] <;> ring_nf <;> field_simp [hn] <;> ring

theorem seven_first_defect (p : ℝ) (hp : p≠0) (h4 : 4*p^2-1≠0) :
    c7 p*(d7 p)^3/16-target6 p =
      -(p^2-4)*(p^2-1)*(4*p^2-1)/(4725*p^5) := by
  unfold c7 d7 target6; field_simp; ring

theorem nine_jet (p : ℝ) (hp : p≠0) (h11 : 11*p^2-2≠0) :
    a9 p+c9 p=p ∧ b9 p+c9 p*d9 p/2=target2 p ∧
    -c9 p*(d9 p)^2/8=target4 p ∧ c9 p*(d9 p)^3/16=target6 p := by
  have hn : -2 + p^2*11 ≠ 0 := by convert h11 using 1 <;> ring
  have hs : 4-p^2*44+p^4*121 ≠ 0 := by
    convert pow_ne_zero 2 h11 using 1 <;> ring
  unfold a9 b9 c9 d9 target2 target4 target6
  refine ⟨?_,?_,?_,?_⟩ <;> field_simp [hp, h11] <;> ring_nf <;> field_simp [hn, hs] <;> ring

theorem nine_first_defect (p : ℝ) (hp : p≠0) (h11 : 11*p^2-2≠0) :
    -5*c9 p*(d9 p)^4/128-target8 p =
      -(p^2-4)*(p^2-1)*(4*p^2-1)*(29*p^2-4)/(396900*p^7) := by
  unfold c9 d9 target8; field_simp; ring

theorem seven_domain_obstruction (p : ℝ) (hp : p≠0) :
    1+d7 p=-(p^2-4)/(15*p^2) := by unfold d7; field_simp; ring

theorem nine_domain_obstruction (p : ℝ) (hp : p≠0) :
    1+d9 p=-(p^2-4)/(21*p^2) := by unfold d9; field_simp; ring

theorem explicit_seven_nonreal : 1+d7 3*((1000-1)/(1000+1))^2<0 := by
  norm_num [d7]

theorem explicit_nine_nonreal : 1+d9 3*((1000-1)/(1000+1))^2<0 := by
  norm_num [d9]

end LeanMath.Papers.RectangleFactorizationJets
