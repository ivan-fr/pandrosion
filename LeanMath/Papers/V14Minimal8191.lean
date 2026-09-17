import LeanMath.Papers.V14MinimalCheck

/-! Exact gate and minimal diagonal degree for p=8191; generated rational proof inputs. -/
noncomputable section
namespace LeanMath.Papers.V14Minimal8191
open Polynomial
open LeanMath.Papers.V14PolynomialGate LeanMath.Papers.V14MinimalCheck
open LeanMath.Papers.V14PowerError LeanMath.Papers.V14DiagonalPolynomials
open LeanMath.Papers.V14DiagonalError LeanMath.Papers.Cayley
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def rho : ℝ := (((6105538867673031/144115188075855872) : ℚ) : ℝ)

def A0 : ℝ[X] := ofCoeffs [1]

def cert0 : Certificate A0 ((8191:ℚ):ℝ) rho 0 :=
  certificate [] [0,-8191] 8191 (6105538867673031/144115188075855872) 2 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [mass]) (by norm_num [mass]) (by norm_num [mass])
    (by decide +kernel) (by decide +kernel)

theorem diagonal0 (y : ℝ) (hy : |y|≤rho) :
    correction (1/8191) 0 (unchi y)=A0.eval y/A0.eval (-y) := by
  have hm : y ∈ Set.Ioo (-1) 1 := abs_lt.mp (hy.trans_lt cert0.hr1)
  have hz := (cert0.hpos (-y) (by simpa using hy)).ne'
  have hden := mul_ne_zero
    (poly_pos (-(1/8191)) (by norm_num) 0 (unchi y) (unchi_pos y hm).le).ne'
    (poly_pos (1/8191) (by norm_num) 0 1 (by norm_num)).ne'
  unfold correction
  apply (div_eq_div_iff hden hz).mpr
  have h1 : 1-y≠0 := by linarith [hm.2]
  norm_num [poly,c,Finset.sum_range_succ,A0,ofCoeffs,unchi]
  <;> field_simp
  <;> ring

theorem excludes0 : ¬Meets 8191 rho 0 := by
  have hb : 8/(2:ℝ)^52<etaLower cert0/(1+etaLower cert0) := by
    norm_num [etaLower,primitive,cert0,certificate,mass,rho]
  intro h
  have hu := h rho (by rw [abs_of_nonneg cert0.hr0])
  rw [diagonal0 rho (by rw [abs_of_nonneg cert0.hr0])] at hu
  have hl := hb.trans_le (endpoint_bound cert0)
  simp only [Rat.cast_ofNat] at hl
  exact (not_lt_of_ge hu) hl

def A1 : ℝ[X] := ofCoeffs [1,(1/8191)]

def cert1 : Certificate A1 ((8191:ℚ):ℝ) rho 2 :=
  certificate [(1/8191)] [0,(-67092482/8191),0,(1/8191)] 8191 (6105538867673031/144115188075855872) (134184960/67092481) 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [mass]) (by norm_num [mass]) (by norm_num [mass])
    (by decide +kernel) (by decide +kernel)

theorem diagonal1 (y : ℝ) (hy : |y|≤rho) :
    correction (1/8191) 1 (unchi y)=A1.eval y/A1.eval (-y) := by
  have hm : y ∈ Set.Ioo (-1) 1 := abs_lt.mp (hy.trans_lt cert1.hr1)
  have hz := (cert1.hpos (-y) (by simpa using hy)).ne'
  have hden := mul_ne_zero
    (poly_pos (-(1/8191)) (by norm_num) 1 (unchi y) (unchi_pos y hm).le).ne'
    (poly_pos (1/8191) (by norm_num) 1 1 (by norm_num)).ne'
  unfold correction
  apply (div_eq_div_iff hden hz).mpr
  have h1 : 1-y≠0 := by linarith [hm.2]
  norm_num [poly,c,Finset.sum_range_succ,A1,ofCoeffs,unchi]
  <;> field_simp
  <;> ring

theorem excludes1 : ¬Meets 8191 rho 1 := by
  have hb : 8/(2:ℝ)^52<etaLower cert1/(1+etaLower cert1) := by
    norm_num [etaLower,primitive,cert1,certificate,mass,rho]
  intro h
  have hu := h rho (by rw [abs_of_nonneg cert1.hr0])
  rw [diagonal1 rho (by rw [abs_of_nonneg cert1.hr0])] at hu
  have hl := hb.trans_le (endpoint_bound cert1)
  simp only [Rat.cast_ofNat] at hl
  exact (not_lt_of_ge hu) hl

def A2 : ℝ[X] := ofCoeffs [1,(1/8191),(-22364160/67092481)]

def cert2 : Certificate A2 ((8191:ℚ):ℝ) rho 4 :=
  certificate [(1/8191),(-22364160/67092481)] [0,(-111820802/8191),0,(3501089679360001/549554511871),0,(-500155652505600/549554511871)] 8191 (6105538867673031/144115188075855872) (4001245264773120/4501401006735361) 4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [mass]) (by norm_num [mass]) (by norm_num [mass])
    (by decide +kernel) (by decide +kernel)

theorem diagonal2 (y : ℝ) (hy : |y|≤rho) :
    correction (1/8191) 2 (unchi y)=A2.eval y/A2.eval (-y) := by
  have hm : y ∈ Set.Ioo (-1) 1 := abs_lt.mp (hy.trans_lt cert2.hr1)
  have hz := (cert2.hpos (-y) (by simpa using hy)).ne'
  have hden := mul_ne_zero
    (poly_pos (-(1/8191)) (by norm_num) 2 (unchi y) (unchi_pos y hm).le).ne'
    (poly_pos (1/8191) (by norm_num) 2 1 (by norm_num)).ne'
  unfold correction
  apply (div_eq_div_iff hden hz).mpr
  have h1 : 1-y≠0 := by linarith [hm.2]
  norm_num [poly,c,Finset.sum_range_succ,A2,ofCoeffs,unchi]
  <;> field_simp
  <;> ring

theorem excludes2 : ¬Meets 8191 rho 2 := by
  have hb : 8/(2:ℝ)^52<etaLower cert2/(1+etaLower cert2) := by
    norm_num [etaLower,primitive,cert2,certificate,mass,rho]
  intro h
  have hu := h rho (by rw [abs_of_nonneg cert2.hr0])
  rw [diagonal2 rho (by rw [abs_of_nonneg cert2.hr0])] at hu
  have hl := hb.trans_le (endpoint_bound cert2)
  simp only [Rat.cast_ofNat] at hl
  exact (not_lt_of_ge hu) hl

def A3 : ℝ[X] := ofCoeffs [1,(1/8191),(-201277441/335462405),(-89456641/2747772559355)]

def cert3 : Certificate A3 ((8191:ℚ):ℝ) rho 6 :=
  certificate [(1/8191),(-201277441/335462405),(-89456641/2747772559355)] [0,(-738017292/40955),0,(175554639687598126/13738862796775),0,(-2718091467664316391997452/921774391154233548775),0,(8002490619002881/921774391154233548775)] 8191 (6105538867673031/144115188075855872) (483216248625385888284672/1510050807588865399603205) 6
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [mass]) (by norm_num [mass]) (by norm_num [mass])
    (by decide +kernel) (by decide +kernel)

theorem diagonal3 (y : ℝ) (hy : |y|≤rho) :
    correction (1/8191) 3 (unchi y)=A3.eval y/A3.eval (-y) := by
  have hm : y ∈ Set.Ioo (-1) 1 := abs_lt.mp (hy.trans_lt cert3.hr1)
  have hz := (cert3.hpos (-y) (by simpa using hy)).ne'
  have hden := mul_ne_zero
    (poly_pos (-(1/8191)) (by norm_num) 3 (unchi y) (unchi_pos y hm).le).ne'
    (poly_pos (1/8191) (by norm_num) 3 1 (by norm_num)).ne'
  unfold correction
  apply (div_eq_div_iff hden hz).mpr
  have h1 : 1-y≠0 := by linarith [hm.2]
  norm_num [poly,c,Finset.sum_range_succ,A3,ofCoeffs,unchi]
  <;> field_simp
  <;> ring

theorem uniform : Meets 8191 rho 3 := by
  have he : etaUpper cert3<1 := by norm_num [etaUpper,primitive,cert3,certificate,mass,rho]
  have hb : etaUpper cert3/(1-etaUpper cert3)<8/(2:ℝ)^52 := by
    norm_num [etaUpper,primitive,cert3,certificate,mass,rho]
  intro y hy
  rw [diagonal3 y hy]
  simpa only [Rat.cast_ofNat] using ((uniform_bound cert3 he y hy).trans_lt hb).le

/-- The selected degree works; every smaller nonnegative diagonal degree fails. -/
theorem minimal_degree : Meets 8191 rho 3 ∧ ∀ j : ℕ, j<3 → ¬Meets 8191 rho j := by
  refine ⟨uniform,?_⟩
  intro j hj
  interval_cases j
  · exact excludes0
  · exact excludes1
  · exact excludes2

/-- The frozen gate contains the full exact one-entry image of the stated workload. -/
theorem gate_contains_entry (X : ℝ) (hX : 0<X) (hwork : |Real.log X|≤1000*Real.log 2) :
    |chi (LeanMath.Papers.V14Entry.residual 8191 X 1)|≤rho := by
  apply (LeanMath.Papers.V14HalleyThresholds.entry_radius 8191 X (by norm_num) hX hwork).trans
  norm_num [LeanMath.Papers.V14HalleyThresholds.radius,rho]

end LeanMath.Papers.V14Minimal8191
