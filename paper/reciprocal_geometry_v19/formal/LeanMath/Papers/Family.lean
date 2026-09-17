import LeanMath.Papers.Comparison
import LeanMath.Papers.CertifiedConvergence

noncomputable section
namespace LeanMath.Papers.Cayley
open Real Set Filter Function
open scoped Topology

def truncation (j : Fin 3) (p y : ℝ) := ![P₁ p y,P₃ p y,P₅ p y] j
def family (j : Fin 3) (p R : ℝ) := unchi (truncation j p (chi R))

theorem family_identification (p R : ℝ) :
    family 0 p R=C₃ p R ∧ family 1 p R=C₅ p R ∧ family 2 p R=C₇ p R := by
  simp [family,truncation,C₃,C₅,C₇]

theorem truncation_zero (j : Fin 3) (p : ℝ) : truncation j p 0=0 := by
  fin_cases j <;> simp [truncation,P₁,P₃,P₅]

theorem truncation_odd (j : Fin 3) (p y : ℝ) : truncation j p (-y) = -truncation j p y := by
  fin_cases j <;> simp [truncation,P₁_odd,P₃_odd,P₅_odd]

theorem truncation_between (j : Fin 3) (p y : ℝ) (hp : 1 < p) (hy : 0 < y) :
    0 < truncation j p y ∧ truncation j p y ≤ P₅ p y := by
  obtain ⟨h1,h13,h35⟩ := truncations_ordered p y hp hy
  fin_cases j <;> simp only [truncation,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  · exact ⟨h1,(h13.trans h35).le⟩
  · exact ⟨h1.trans h13,h35.le⟩
  · exact ⟨h1.trans (h13.trans h35),le_rfl⟩

theorem truncation_mem (j : Fin 3) (p y : ℝ) (hp : 1 < p) (hy : y ∈ Ioo (-1) 1) :
    truncation j p y ∈ Ioo (-1) 1 := by
  have hpos : ∀ t, 0 < t → t < 1 → truncation j p t ∈ Ioo (-1) 1 := by
    intro t ht ht1
    have hb := truncation_between j p t hp ht
    exact ⟨by linarith [hb.1],hb.2.trans_lt (P₅_bounds p t hp ht.le ht1.le).2⟩
  rcases lt_trichotomy y 0 with h | h | h
  · have hh := hpos (-y) (by linarith) (by linarith [hy.1])
    rw [truncation_odd] at hh
    exact ⟨by linarith [hh.2],by linarith [hh.1]⟩
  · rw [h,truncation_zero]
    norm_num
  · exact hpos y h hy.2

theorem continuous_truncation (j : Fin 3) (p : ℝ) : Continuous (truncation j p) := by
  fin_cases j
  · change Continuous (fun y : ℝ => a₁ p*y)
    fun_prop
  · change Continuous (fun y : ℝ => a₁ p*y+a₃ p*y^3)
    fun_prop
  · change Continuous (fun y : ℝ => a₁ p*y+a₃ p*y^3+a₅ p*y^5)
    fun_prop

theorem family_pos (j : Fin 3) (p R : ℝ) (hp : 1 < p) (hR : 0 < R) : 0 < family j p R :=
  unchi_pos _ (truncation_mem j p (chi R) hp (chi_mem R hR))

theorem family_reciprocal (j : Fin 3) (p R : ℝ) (hR : 0 < R) :
    family j p R⁻¹ = (family j p R)⁻¹ := by
  simp only [family,chi_inv R hR,truncation_odd,unchi_neg]

theorem family_one (j : Fin 3) (p : ℝ) : family j p 1 = 1 := by
  simp [family,chi,truncation_zero,unchi]

theorem family_above (j : Fin 3) (p R : ℝ) (hp : 1 < p) (hR : 1 < R) :
    1 < family j p R ∧ family j p R < R^(1/p) := by
  have hR0 : 0 < R := by linarith
  have hy0 : 0 < chi R := by unfold chi; positivity
  have hy := chi_mem R hR0
  have ht := truncation_mem j p (chi R) hp hy
  have h5 := P₅_mem p (chi R) hp hy
  have hb := truncation_between j p (chi R) hp hy0
  have hle : family j p R ≤ C₇ p R :=
    strictMonoOn_one_add_div_one_sub.monotoneOn ht h5 hb.2
  refine ⟨?_,hle.trans_lt (C₇_above_one_below_root p R hp hR).2⟩
  unfold family unchi
  apply (one_lt_div (by linarith [ht.2] : 0 < 1-truncation j p (chi R))).mpr
  linarith [hb.1]

theorem family_below (j : Fin 3) (p R : ℝ) (hp : 1 < p) (hR0 : 0 < R) (hR1 : R < 1) :
    R^(1/p) < family j p R ∧ family j p R < 1 := by
  have hc := family_pos j p R hp hR0
  have hr := rpow_pos_of_pos hR0 (1/p)
  obtain ⟨h1,h2⟩ := family_above j p R⁻¹ hp ((one_lt_inv₀ hR0).mpr hR1)
  rw [family_reciprocal j p R hR0] at h1 h2
  rw [inv_rpow hR0.le] at h2
  exact ⟨(inv_lt_inv₀ hc hr).mp h2,(one_lt_inv₀ hc).mp h1⟩

theorem continuousAt_family (j : Fin 3) (p R : ℝ) (hp : 1 < p) (hR : 0 < R) :
    ContinuousAt (family j p) R := by
  have ht := truncation_mem j p (chi R) hp (chi_mem R hR)
  have hchi : ContinuousAt chi R := by
    unfold chi
    exact (continuousAt_id.sub continuousAt_const).div
      (continuousAt_id.add continuousAt_const) (by linarith)
  have hf := (continuous_truncation j p).continuousAt.comp hchi
  exact (continuousAt_const.add hf).div (continuousAt_const.sub hf) (by linarith [ht.2])

/-- All three rational Cayley kernels converge globally for all real p>1. -/
theorem family_global_convergence (j : Fin 3) (p x u : ℝ)
    (hp : 1 < p) (hx : 0 < x) (hu : 0 < u) :
    Tendsto (fun n : ℕ => (Certified.step (family j p) p x)^[n] u)
      atTop (𝓝 (x^(1/p))) :=
  Certified.global (family j p) p x u (by linarith) hx hu
    (fun R hR => continuousAt_family j p R hp hR) (family_one j p)
    (fun R hR => family_above j p R hp hR) (fun R hR0 hR1 => family_below j p R hp hR0 hR1)

end LeanMath.Papers.Cayley
