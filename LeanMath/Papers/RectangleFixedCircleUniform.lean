import LeanMath.Papers.RectangleFixedCircleBranch
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Sequences

/-! The real-parameter whole-branch theorem of V23.
The logarithmic Cayley coordinate gives an inequality uniform in every real `p > 2`.
-/
noncomputable section
namespace LeanMath.Papers.RectangleFixedCircleUniform
open LeanMath.Papers.RectangleFixedCircle LeanMath.Papers.RectangleFixedCircleBranch
open Set Filter Function
open scoped Topology

/-- Twice the hyperbolic arctangent on `(-1,1)`. -/
def cayleyLog (x : ℝ) := Real.log (1+x) - Real.log (1-x)

theorem cayleyLog_zero : cayleyLog 0 = 0 := by simp [cayleyLog]

theorem cayleyLog_derivative (x : ℝ) (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt cayleyLog (2/(1-x^2)) x := by
  have h1 : 1+x ≠ 0 := by linarith [hx.1]
  have h2 : 1-x ≠ 0 := by linarith [hx.2]
  convert! (((hasDerivAt_id x).const_add 1).log h1).sub
    (((hasDerivAt_id x).const_sub 1).log h2) using 1
  have h3 : 1-x^2≠0 := by nlinarith [hx.1, hx.2]
  simp only [id_eq]; field_simp [h1, h2, h3]; ring

theorem cayleyLog_strictMono : StrictMonoOn cayleyLog (Ioo (-1 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
  · intro x hx; exact (cayleyLog_derivative x hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioo] at hx
    rw [(cayleyLog_derivative x hx).deriv]
    apply div_pos (by norm_num)
    nlinarith [hx.1, hx.2]

/-- Strict convex scaling, proved from the first derivative (no series or degree split). -/
theorem cayleyLog_scaled (c x : ℝ) (hc : 1 < c) (hx : 0 < x) (hcx : c*x < 1) :
    c*cayleyLog x < cayleyLog (c*x) := by
  have hx1 : x < 1 := by nlinarith
  let g := fun z : ℝ => cayleyLog (c*z)-c*cayleyLog z
  have hd (z : ℝ) (hz : z ∈ Icc 0 x) :
      HasDerivAt g (2/(1-(c*z)^2)*c-c*(2/(1-z^2))) z := by
    have hz1 : z ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hz.1], lt_of_le_of_lt hz.2 hx1⟩
    have hcz : c*z ∈ Ioo (-1 : ℝ) 1 := by
      constructor
      · nlinarith [hz.1]
      · nlinarith [hz.2]
    convert! ((cayleyLog_derivative (c*z) hcz).comp z
      ((hasDerivAt_id z).const_mul c)).sub ((cayleyLog_derivative z hz1).const_mul c) using 1 <;> ring
  have hm : StrictMonoOn g (Icc 0 x) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · intro z hz; exact (hd z hz).continuousAt.continuousWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      rw [(hd z ⟨hz.1.le, hz.2.le⟩).deriv]
      have hcz : 0 < c*z ∧ c*z < 1 := ⟨mul_pos (by linarith) hz.1, by nlinarith [hz.2]⟩
      have hz1 : z < 1 := lt_trans hz.2 hx1
      have hb : 0 < 1-(c*z)^2 := by nlinarith [hcz.1, hcz.2]
      have hab : 1-(c*z)^2 < 1-z^2 := by
        have : z < c*z := by nlinarith [hz.1]
        nlinarith [hz.1]
      have hi : 2/(1-z^2) < 2/(1-(c*z)^2) :=
        div_lt_div_of_pos_left (by norm_num) hb hab
      nlinarith
  have hh := hm ⟨le_rfl, hx.le⟩ ⟨hx.le, le_rfl⟩ hx
  simpa [g, cayleyLog_zero] using hh

/-- Real-degree endpoint and interior upper-error inequality. -/
theorem uniform_upper (p v : ℝ) (hp : 2 < p) (hv : 1 < v) (hQ : Q p v ≤ 0) :
    p*Real.log v + 2*Real.log (N p v/D p v) < 0 := by
  have hN := (positive_quadratics p v hp).1
  have hD := (positive_quadratics p v hp).2
  have hvp : 0 < v+1 := by linarith
  let x := (v-1)/(v+1)
  let y := (D p v-N p v)/(D p v+N p v)
  have hx : 0 < x := div_pos (by linarith) hvp
  have hx1 : x < 1 := (div_lt_one hvp).mpr (by linarith)
  have hDN : D p v-N p v = 6*p*(v^2-1) := by unfold D N A B C; ring
  have hy : 0 < y := by
    apply div_pos _ (by positivity)
    rw [hDN]; have : 0 < v^2-1 := by nlinarith
    positivity
  have hy1 : y < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  have hbranch : (p^2-1)*x^2 ≤ 3 := by
    have he : ((p^2-1)*x^2-3)*(v+1)^2 = Q p v := by
      dsimp [x]; unfold Q; field_simp; ring
    have hvp2 : 0 < (v+1)^2 := sq_pos_of_pos hvp
    nlinarith
  have hden : 0 < 3+(p^2-1)*x^2 := by
    have : 0 < p^2-1 := by nlinarith
    positivity
  have hye : y = 3*p*x/(3+(p^2-1)*x^2) := by
    apply (eq_div_iff hden.ne').mpr
    dsimp [y, x]
    field_simp [(show D p v+N p v≠0 by positivity), hvp.ne']
    unfold D N A B C; ring
  have hcy : p/2*x ≤ y := by
    rw [hye, le_div_iff₀ hden]
    have := mul_nonneg (show 0≤p*x by positivity) (show 0≤3-(p^2-1)*x^2 by linarith)
    nlinarith
  have hcx : p/2*x < 1 := lt_of_le_of_lt hcy hy1
  have hscale := cayleyLog_scaled (p/2) x (by linarith) hx hcx
  have hmono : cayleyLog (p/2*x) ≤ cayleyLog y :=
    cayleyLog_strictMono.monotoneOn ⟨by nlinarith [show 0 < p/2*x from mul_pos (by linarith) hx], hcx⟩ ⟨by linarith, hy1⟩ hcy
  have hxlog : cayleyLog x = Real.log v := by
    rw [cayleyLog, ← Real.log_div (by linarith : 1+x≠0) (by linarith : 1-x≠0)]
    congr 1
    dsimp [x]; field_simp; ring
  have hylog : cayleyLog y = -Real.log (N p v/D p v) := by
    rw [cayleyLog, ← Real.log_div (by linarith : 1+y≠0) (by linarith : 1-y≠0)]
    have he : (1+y)/(1-y) = D p v/N p v := by
      dsimp [y]; field_simp [hN.ne', (show D p v+N p v≠0 by positivity)]; ring
    rw [he, Real.log_div hD.ne' hN.ne', Real.log_div hN.ne' hD.ne']; ring
  rw [hxlog] at hscale
  rw [hylog] at hmono
  linarith

/-- Input logarithmic error, parameterized by the selected correction `v`. -/
def input (p v : ℝ) := (Real.log (N p v)-Real.log (D p v))/p
/-- Output logarithmic error after multiplying the current estimate by `v`. -/
def output (p v : ℝ) := input p v+Real.log v

theorem input_one (p : ℝ) : input p 1 = 0 := by simp [input, (at_one p).1, (at_one p).2]
theorem output_one (p : ℝ) : output p 1 = 0 := by simp [output, input_one]

theorem input_eq_log_residual (p v : ℝ) (hp : 2 < p) :
    input p v = Real.log (N p v/D p v)/p := by
  rw [Real.log_div (positive_quadratics p v hp).1.ne' (positive_quadratics p v hp).2.ne']
  rfl

theorem input_deriv (p v : ℝ) (hp : 2 < p) :
    HasDerivAt (input p) (12*Q p v/(N p v*D p v)) v := by
  have hN := (positive_quadratics p v hp).1.ne'
  have hD := (positive_quadratics p v hp).2.ne'
  have hp0 : p≠0 := by linarith
  convert! (((N_hasDerivAt p v).log hN).sub ((D_hasDerivAt p v).log hD)).div_const p using 1
  field_simp [hN, hD, hp0]
  linear_combination -(branch_derivative p v)

theorem output_deriv (p v : ℝ) (hp : 2 < p) (hv : v≠0) :
    HasDerivAt (output p) (A p*C p*(v-1)^4/(v*N p v*D p v)) v := by
  have hN := (positive_quadratics p v hp).1.ne'
  have hD := (positive_quadratics p v hp).2.ne'
  convert! (input_deriv p v hp).add (Real.hasDerivAt_log hv) using 1
  field_simp [hN, hD, hv]
  linear_combination -(ND_branch p v)

theorem input_reciprocal (p v : ℝ) (hp : 2 < p) (hv : 0 < v) :
    input p (1/v) = -input p v := by
  have hN := (positive_quadratics p v hp).1
  have hD := (positive_quadratics p v hp).2
  have hr := reciprocity p v hv.ne'
  have e1 : N p (1/v) = D p v/v^2 := (eq_div_iff (by positivity)).mpr hr.1
  have e2 : D p (1/v) = N p v/v^2 := (eq_div_iff (by positivity)).mpr hr.2
  unfold input
  rw [e1, e2, Real.log_div hD.ne' (by positivity), Real.log_div hN.ne' (by positivity)]
  ring

theorem output_reciprocal (p v : ℝ) (hp : 2 < p) (hv : 0 < v) :
    output p (1/v) = -output p v := by
  unfold output
  rw [input_reciprocal p v hp hv]
  simp only [one_div, Real.log_inv]; ring

/-- The Padé defect has positive sign above the root. -/
theorem output_pos (p v : ℝ) (hp : 2 < p) (hv : 1 < v) : 0 < output p v := by
  have hm : StrictMonoOn (output p) (Icc 1 v) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · intro w hw
      exact (output_deriv p w hp (by linarith [hw.1])).continuousAt.continuousWithinAt
    · intro w hw
      rw [interior_Icc] at hw
      have hw0 : 0 < w := by linarith [hw.1]
      rw [(output_deriv p w hp hw0.ne').deriv]
      exact div_pos (mul_pos (AC_pos p hp) (pow_pos (by linarith [hw.1]) _))
        (mul_pos (mul_pos hw0 (positive_quadratics p w hp).1) (positive_quadratics p w hp).2)
  simpa [output_one] using hm ⟨le_rfl, hv.le⟩ ⟨hv.le, le_rfl⟩ hv

theorem positive_half_bounds (p v : ℝ) (hp : 2 < p) (hv : 1 < v) (hQ : Q p v≤0) :
    0 < output p v ∧ output p v < -input p v := by
  refine ⟨output_pos p v hp hv, ?_⟩
  have he : Real.log (N p v/D p v) = p*input p v := by
    rw [input_eq_log_residual p v hp]; field_simp
  have hu := uniform_upper p v hp hv hQ
  rw [he] at hu
  have : 0 < p := by linarith
  unfold output
  nlinarith

/-- Full V23 one-step result, including both endpoints of the scalar branch. -/
theorem real_branch_alternation_contraction (p v : ℝ) (hp : 2 < p) (hv0 : 0 < v)
    (hv1 : v≠1) (hQ : Q p v≤0) :
    input p v*output p v < 0 ∧ |output p v| < |input p v| := by
  rcases lt_or_gt_of_ne hv1 with hv | hv
  · have hw : 1 < 1/v := (lt_div_iff₀ hv0).mpr (by linarith)
    have hQi : Q p (1/v)≤0 := by
      have := Q_reciprocal p v hv0.ne'
      have : 0 < v^2 := by positivity
      nlinarith
    have hb := positive_half_bounds p (1/v) hp hw hQi
    rw [input_reciprocal p v hp hv0, output_reciprocal p v hp hv0] at hb
    have hi : 0 < input p v := by linarith [hb.1, hb.2]
    have ho : output p v < 0 := by linarith [hb.1]
    constructor
    · exact mul_neg_of_pos_of_neg hi ho
    · rw [abs_of_pos hi, abs_of_neg ho]; linarith [hb.2]
  · have hb := positive_half_bounds p v hp hv hQ
    have hi : input p v < 0 := by linarith [hb.1, hb.2]
    constructor
    · exact mul_neg_of_neg_of_pos hi hb.1
    · rw [abs_of_neg hi, abs_of_pos hb.1]; exact hb.2

end LeanMath.Papers.RectangleFixedCircleUniform
