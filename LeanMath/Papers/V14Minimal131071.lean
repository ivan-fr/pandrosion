import LeanMath.Papers.V14MinimalCheck

/-! Exact gate and minimal diagonal degree for p=131071; generated rational proof inputs. -/
noncomputable section
namespace LeanMath.Papers.V14Minimal131071
open Polynomial
open LeanMath.Papers.V14PolynomialGate LeanMath.Papers.V14MinimalCheck
open LeanMath.Papers.V14PowerError LeanMath.Papers.V14DiagonalPolynomials
open LeanMath.Papers.V14DiagonalError LeanMath.Papers.Cayley
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def rho : ℝ := (((6109166815012951/2305843009213693952) : ℚ) : ℝ)

def A0 : ℝ[X] := ofCoeffs [1]

def cert0 : Certificate A0 ((131071:ℚ):ℝ) rho 0 :=
  certificate [] [0,-131071] 131071 (6109166815012951/2305843009213693952) 2 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [mass]) (by norm_num [mass]) (by norm_num [mass])
    (by decide +kernel) (by decide +kernel)

theorem diagonal0 (y : ℝ) (hy : |y|≤rho) :
    correction (1/131071) 0 (unchi y)=A0.eval y/A0.eval (-y) := by
  have hm : y ∈ Set.Ioo (-1) 1 := abs_lt.mp (hy.trans_lt cert0.hr1)
  have hz := (cert0.hpos (-y) (by simpa using hy)).ne'
  have hden := mul_ne_zero
    (poly_pos (-(1/131071)) (by norm_num) 0 (unchi y) (unchi_pos y hm).le).ne'
    (poly_pos (1/131071) (by norm_num) 0 1 (by norm_num)).ne'
  unfold correction
  apply (div_eq_div_iff hden hz).mpr
  have h1 : 1-y≠0 := by linarith [hm.2]
  norm_num [poly,c,Finset.sum_range_succ,A0,ofCoeffs,unchi]
  <;> field_simp
  <;> ring

theorem excludes0 : ¬Meets 131071 rho 0 := by
  have hb : 8/(2:ℝ)^52<etaLower cert0/(1+etaLower cert0) := by
    norm_num [etaLower,primitive,cert0,certificate,mass,rho]
  intro h
  have hu := h rho (by rw [abs_of_nonneg cert0.hr0])
  rw [diagonal0 rho (by rw [abs_of_nonneg cert0.hr0])] at hu
  have hl := hb.trans_le (endpoint_bound cert0)
  simp only [Rat.cast_ofNat] at hl
  exact (not_lt_of_ge hu) hl

def A1 : ℝ[X] := ofCoeffs [1,(1/131071)]

def cert1 : Certificate A1 ((131071:ℚ):ℝ) rho 2 :=
  certificate [(1/131071)] [0,(-17179607042/131071),0,(1/131071)] 131071 (6109166815012951/2305843009213693952) (34359214080/17179607041) 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [mass]) (by norm_num [mass]) (by norm_num [mass])
    (by decide +kernel) (by decide +kernel)

theorem diagonal1 (y : ℝ) (hy : |y|≤rho) :
    correction (1/131071) 1 (unchi y)=A1.eval y/A1.eval (-y) := by
  have hm : y ∈ Set.Ioo (-1) 1 := abs_lt.mp (hy.trans_lt cert1.hr1)
  have hz := (cert1.hpos (-y) (by simpa using hy)).ne'
  have hden := mul_ne_zero
    (poly_pos (-(1/131071)) (by norm_num) 1 (unchi y) (unchi_pos y hm).le).ne'
    (poly_pos (1/131071) (by norm_num) 1 1 (by norm_num)).ne'
  unfold correction
  apply (div_eq_div_iff hden hz).mpr
  have h1 : 1-y≠0 := by linarith [hm.2]
  norm_num [poly,c,Finset.sum_range_succ,A1,ofCoeffs,unchi]
  <;> field_simp
  <;> ring

theorem excludes1 : ¬Meets 131071 rho 1 := by
  have hb : 8/(2:ℝ)^52<etaLower cert1/(1+etaLower cert1) := by
    norm_num [etaLower,primitive,cert1,certificate,mass,rho]
  intro h
  have hu := h rho (by rw [abs_of_nonneg cert1.hr0])
  rw [diagonal1 rho (by rw [abs_of_nonneg cert1.hr0])] at hu
  have hl := hb.trans_le (endpoint_bound cert1)
  simp only [Rat.cast_ofNat] at hl
  exact (not_lt_of_ge hu) hl

def A2 : ℝ[X] := ofCoeffs [1,(1/131071),(-5726535680/17179607041)]

def cert2 : Certificate A2 ((131071:ℚ):ℝ) rho 4 :=
  certificate [(1/131071),(-5726535680/17179607041)] [0,(-28632678402/131071),0,(229552476288824115201/2251748274470911),0,(-32793210894313062400/2251748274470911)] 131071 (6109166815012951/2305843009213693952) (262345687165957570560/295138898083176775681) 4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [mass]) (by norm_num [mass]) (by norm_num [mass])
    (by decide +kernel) (by decide +kernel)

theorem diagonal2 (y : ℝ) (hy : |y|≤rho) :
    correction (1/131071) 2 (unchi y)=A2.eval y/A2.eval (-y) := by
  have hm : y ∈ Set.Ioo (-1) 1 := abs_lt.mp (hy.trans_lt cert2.hr1)
  have hz := (cert2.hpos (-y) (by simpa using hy)).ne'
  have hden := mul_ne_zero
    (poly_pos (-(1/131071)) (by norm_num) 2 (unchi y) (unchi_pos y hm).le).ne'
    (poly_pos (1/131071) (by norm_num) 2 1 (by norm_num)).ne'
  unfold correction
  apply (div_eq_div_iff hden hz).mpr
  have h1 : 1-y≠0 := by linarith [hm.2]
  norm_num [poly,c,Finset.sum_range_succ,A2,ofCoeffs,unchi]
  <;> field_simp
  <;> ring

theorem uniform : Meets 131071 rho 2 := by
  have he : etaUpper cert2<1 := by norm_num [etaUpper,primitive,cert2,certificate,mass,rho]
  have hb : etaUpper cert2/(1-etaUpper cert2)<8/(2:ℝ)^52 := by
    norm_num [etaUpper,primitive,cert2,certificate,mass,rho]
  intro y hy
  rw [diagonal2 y hy]
  simpa only [Rat.cast_ofNat] using ((uniform_bound cert2 he y hy).trans_lt hb).le

/-- The selected degree works; every smaller nonnegative diagonal degree fails. -/
theorem minimal_degree : Meets 131071 rho 2 ∧ ∀ j : ℕ, j<2 → ¬Meets 131071 rho j := by
  refine ⟨uniform,?_⟩
  intro j hj
  interval_cases j
  · exact excludes0
  · exact excludes1

/-- The frozen gate contains the full exact one-entry image of the stated workload. -/
theorem gate_contains_entry (X : ℝ) (hX : 0<X) (hwork : |Real.log X|≤1000*Real.log 2) :
    |chi (LeanMath.Papers.V14Entry.residual 131071 X 1)|≤rho := by
  apply (LeanMath.Papers.V14HalleyThresholds.entry_radius 131071 X (by norm_num) hX hwork).trans
  norm_num [LeanMath.Papers.V14HalleyThresholds.radius,rho]

end LeanMath.Papers.V14Minimal131071
