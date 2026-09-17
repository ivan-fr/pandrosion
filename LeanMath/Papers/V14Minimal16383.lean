import LeanMath.Papers.V14MinimalCheck

/-! Exact gate and minimal diagonal degree for p=16383; generated rational proof inputs. -/
noncomputable section
namespace LeanMath.Papers.V14Minimal16383
open Polynomial
open LeanMath.Papers.V14PolynomialGate LeanMath.Papers.V14MinimalCheck
open LeanMath.Papers.V14PowerError LeanMath.Papers.V14DiagonalPolynomials
open LeanMath.Papers.V14DiagonalError LeanMath.Papers.Cayley
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def rho : ℝ := (((3054135008713607/144115188075855872) : ℚ) : ℝ)

def A0 : ℝ[X] := ofCoeffs [1]

def cert0 : Certificate A0 ((16383:ℚ):ℝ) rho 0 :=
  certificate [] [0,-16383] 16383 (3054135008713607/144115188075855872) 2 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [mass]) (by norm_num [mass]) (by norm_num [mass])
    (by decide +kernel) (by decide +kernel)

theorem diagonal0 (y : ℝ) (hy : |y|≤rho) :
    correction (1/16383) 0 (unchi y)=A0.eval y/A0.eval (-y) := by
  have hm : y ∈ Set.Ioo (-1) 1 := abs_lt.mp (hy.trans_lt cert0.hr1)
  have hz := (cert0.hpos (-y) (by simpa using hy)).ne'
  have hden := mul_ne_zero
    (poly_pos (-(1/16383)) (by norm_num) 0 (unchi y) (unchi_pos y hm).le).ne'
    (poly_pos (1/16383) (by norm_num) 0 1 (by norm_num)).ne'
  unfold correction
  apply (div_eq_div_iff hden hz).mpr
  have h1 : 1-y≠0 := by linarith [hm.2]
  norm_num [poly,c,Finset.sum_range_succ,A0,ofCoeffs,unchi]
  <;> field_simp
  <;> ring

theorem excludes0 : ¬Meets 16383 rho 0 := by
  have hb : 8/(2:ℝ)^52<etaLower cert0/(1+etaLower cert0) := by
    norm_num [etaLower,primitive,cert0,certificate,mass,rho]
  intro h
  have hu := h rho (by rw [abs_of_nonneg cert0.hr0])
  rw [diagonal0 rho (by rw [abs_of_nonneg cert0.hr0])] at hu
  have hl := hb.trans_le (endpoint_bound cert0)
  simp only [Rat.cast_ofNat] at hl
  exact (not_lt_of_ge hu) hl

def A1 : ℝ[X] := ofCoeffs [1,(1/16383)]

def cert1 : Certificate A1 ((16383:ℚ):ℝ) rho 2 :=
  certificate [(1/16383)] [0,(-268402690/16383),0,(1/16383)] 16383 (3054135008713607/144115188075855872) (536805376/268402689) 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [mass]) (by norm_num [mass]) (by norm_num [mass])
    (by decide +kernel) (by decide +kernel)

theorem diagonal1 (y : ℝ) (hy : |y|≤rho) :
    correction (1/16383) 1 (unchi y)=A1.eval y/A1.eval (-y) := by
  have hm : y ∈ Set.Ioo (-1) 1 := abs_lt.mp (hy.trans_lt cert1.hr1)
  have hz := (cert1.hpos (-y) (by simpa using hy)).ne'
  have hden := mul_ne_zero
    (poly_pos (-(1/16383)) (by norm_num) 1 (unchi y) (unchi_pos y hm).le).ne'
    (poly_pos (1/16383) (by norm_num) 1 1 (by norm_num)).ne'
  unfold correction
  apply (div_eq_div_iff hden hz).mpr
  have h1 : 1-y≠0 := by linarith [hm.2]
  norm_num [poly,c,Finset.sum_range_succ,A1,ofCoeffs,unchi]
  <;> field_simp
  <;> ring

theorem excludes1 : ¬Meets 16383 rho 1 := by
  have hb : 8/(2:ℝ)^52<etaLower cert1/(1+etaLower cert1) := by
    norm_num [etaLower,primitive,cert1,certificate,mass,rho]
  intro h
  have hu := h rho (by rw [abs_of_nonneg cert1.hr0])
  rw [diagonal1 rho (by rw [abs_of_nonneg cert1.hr0])] at hu
  have hl := hb.trans_le (endpoint_bound cert1)
  simp only [Rat.cast_ofNat] at hl
  exact (not_lt_of_ge hu) hl

def A2 : ℝ[X] := ofCoeffs [1,(1/16383),(-268402688/805208067)]

def cert2 : Certificate A2 ((16383:ℚ):ℝ) rho 4 :=
  certificate [(1/16383),(-268402688/805208067)] [0,(-1342013446/49149),0,(504280024505417737/39575171284983),0,(-72040002925625344/39575171284983)] 16383 (3054135008713607/144115188075855872) (576320025015418880/648360031161876489) 4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [mass]) (by norm_num [mass]) (by norm_num [mass])
    (by decide +kernel) (by decide +kernel)

theorem diagonal2 (y : ℝ) (hy : |y|≤rho) :
    correction (1/16383) 2 (unchi y)=A2.eval y/A2.eval (-y) := by
  have hm : y ∈ Set.Ioo (-1) 1 := abs_lt.mp (hy.trans_lt cert2.hr1)
  have hz := (cert2.hpos (-y) (by simpa using hy)).ne'
  have hden := mul_ne_zero
    (poly_pos (-(1/16383)) (by norm_num) 2 (unchi y) (unchi_pos y hm).le).ne'
    (poly_pos (1/16383) (by norm_num) 2 1 (by norm_num)).ne'
  unfold correction
  apply (div_eq_div_iff hden hz).mpr
  have h1 : 1-y≠0 := by linarith [hm.2]
  norm_num [poly,c,Finset.sum_range_succ,A2,ofCoeffs,unchi]
  <;> field_simp
  <;> ring

theorem excludes2 : ¬Meets 16383 rho 2 := by
  have hb : 8/(2:ℝ)^52<etaLower cert2/(1+etaLower cert2) := by
    norm_num [etaLower,primitive,cert2,certificate,mass,rho]
  intro h
  have hu := h rho (by rw [abs_of_nonneg cert2.hr0])
  rw [diagonal2 rho (by rw [abs_of_nonneg cert2.hr0])] at hu
  have hl := hb.trans_le (endpoint_bound cert2)
  simp only [Rat.cast_ofNat] at hl
  exact (not_lt_of_ge hu) hl

def A3 : ℝ[X] := ofCoeffs [1,(1/16383),(-161041613/268402689),(-214722151/13191723761661)]

def cert3 : Certificate A3 ((16383:ℚ):ℝ) rho 6 :=
  certificate [(1/16383),(-161041613/268402689),(-214722151/13191723761661)] [0,(-590485916/16383),0,(337147216408161818/13191723761661),0,(-62647767370114523672502604/10622082390525022519287),0,(46105602130066801/10622082390525022519287)] 16383 (3054135008713607/144115188075855872) (55686903974874048786595840/174021575803971443933478921) 6
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [mass]) (by norm_num [mass]) (by norm_num [mass])
    (by decide +kernel) (by decide +kernel)

theorem diagonal3 (y : ℝ) (hy : |y|≤rho) :
    correction (1/16383) 3 (unchi y)=A3.eval y/A3.eval (-y) := by
  have hm : y ∈ Set.Ioo (-1) 1 := abs_lt.mp (hy.trans_lt cert3.hr1)
  have hz := (cert3.hpos (-y) (by simpa using hy)).ne'
  have hden := mul_ne_zero
    (poly_pos (-(1/16383)) (by norm_num) 3 (unchi y) (unchi_pos y hm).le).ne'
    (poly_pos (1/16383) (by norm_num) 3 1 (by norm_num)).ne'
  unfold correction
  apply (div_eq_div_iff hden hz).mpr
  have h1 : 1-y≠0 := by linarith [hm.2]
  norm_num [poly,c,Finset.sum_range_succ,A3,ofCoeffs,unchi]
  <;> field_simp
  <;> ring

theorem uniform : Meets 16383 rho 3 := by
  have he : etaUpper cert3<1 := by norm_num [etaUpper,primitive,cert3,certificate,mass,rho]
  have hb : etaUpper cert3/(1-etaUpper cert3)<8/(2:ℝ)^52 := by
    norm_num [etaUpper,primitive,cert3,certificate,mass,rho]
  intro y hy
  rw [diagonal3 y hy]
  simpa only [Rat.cast_ofNat] using ((uniform_bound cert3 he y hy).trans_lt hb).le

/-- The selected degree works; every smaller nonnegative diagonal degree fails. -/
theorem minimal_degree : Meets 16383 rho 3 ∧ ∀ j : ℕ, j<3 → ¬Meets 16383 rho j := by
  refine ⟨uniform,?_⟩
  intro j hj
  interval_cases j
  · exact excludes0
  · exact excludes1
  · exact excludes2

/-- The frozen gate contains the full exact one-entry image of the stated workload. -/
theorem gate_contains_entry (X : ℝ) (hX : 0<X) (hwork : |Real.log X|≤1000*Real.log 2) :
    |chi (LeanMath.Papers.V14Entry.residual 16383 X 1)|≤rho := by
  apply (LeanMath.Papers.V14HalleyThresholds.entry_radius 16383 X (by norm_num) hX hwork).trans
  norm_num [LeanMath.Papers.V14HalleyThresholds.radius,rho]

end LeanMath.Papers.V14Minimal16383
