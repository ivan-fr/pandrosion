import LeanMath.Papers.RefinementOrdering
import LeanMath.Papers.StrictBracket

noncomputable section
namespace LeanMath.Papers.RealBracket
open Real Set
open LeanMath.Papers.Cayley

def crossGap (p R : ℝ) := logHalley p R-(log R+(p-1)*(log p-log (R+p-1)))

theorem crossGap_one (p : ℝ) : crossGap p 1=0 := by
  unfold crossGap logHalley
  rw [show (1:ℝ)+p-1=p by ring]
  simp
  congr 1
  ring

theorem crossGap_derivative (p R : ℝ) (hp : 1 < p) (hR : 0 < R) :
    HasDerivAt (crossGap p)
      ((R-1)*(p-1)*((p-2)*(p+1)*R^2+(2*p^2-3*p+3)*R+(p^2-1))/
        (R*(R+p-1)*((p-1)*R+p+1)*((p+1)*R+p-1))) R := by
  have hA : 0 < (p+1)*R+p-1 := by nlinarith [mul_pos (by linarith : 0 < p+1) hR]
  have hB : 0 < (p-1)*R+p+1 := by positivity
  have hC : 0 < R+p-1 := by linarith
  have hdA := (((hasDerivAt_id R).const_mul (p+1)).add_const p).sub_const 1
  have hdB := (((hasDerivAt_id R).const_mul (p-1)).add_const p).add_const 1
  have hdC := ((hasDerivAt_id R).add_const p).sub_const 1
  convert! ((hdA.log hA.ne').sub (hdB.log hB.ne')).sub
    ((hasDerivAt_log hR.ne').add ((hdC.log hC.ne').const_sub (log p) |>.const_mul (p-1))) using 1
  simp only [id_eq]
  generalize ha : (p+1)*R+p-1=A at *
  generalize hb : (p-1)*R+p+1=B at *
  generalize hc : R+p-1=C at *
  field_simp [hA.ne',hB.ne',hC.ne',hR.ne']
  subst A B C
  ring

theorem lower_lt_halley (p R : ℝ) (hp : 2 ≤ p) (hR : 1 < R) : lower p R < C₃ p R := by
  have hp1 : 1 < p := by linarith
  have hm : StrictMonoOn (crossGap p) (Ici 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 1)
    · intro t ht
      change 1 ≤ t at ht
      exact (crossGap_derivative p t hp1 (by linarith)).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      change 1 < t at ht
      have ht0 : 0 < t := by linarith
      have ht1 : 0 < t-1 := by linarith
      have hp0 : 0 < p := by linarith
      have hp2 : 0 ≤ p-2 := by linarith
      have hp1' : 0 < p-1 := by linarith
      have hP : 0 < 2*p^2-3*p+3 := by nlinarith [sq_nonneg (p-1)]
      have hQ : 0 < p^2-1 := by nlinarith
      have hA : 0 < (p+1)*t+p-1 := by nlinarith [mul_pos (by linarith : 0 < p+1) ht0]
      have hB : 0 < (p-1)*t+p+1 := by positivity
      have hC : 0 < t+p-1 := by linarith
      rw [(crossGap_derivative p t hp1 ht0).deriv]
      positivity
  have h := hm (by simp) hR.le hR
  rw [crossGap_one] at h
  have hR0 : 0 < R := by linarith
  have hC : 0 < C₃ p R := by
    simpa [Cayley.family,Cayley.truncation,C₃] using Cayley.family_pos 0 p R hp1 hR0
  apply (log_lt_log_iff (lower_pos p R hp1 hR0) hC).mp
  rw [log_lower p R hp1 hR0,log_C₃ p R hp1 hR0]
  exact sub_pos.mp h

theorem halley_le_family (j : Fin 3) (p R : ℝ) (hp : 1 < p) (hR : 1 < R) :
    C₃ p R ≤ family j p R := by
  have hR0 : 0 < R := by linarith
  have hy := chi_mem R hR0
  have hy0 : 0 < chi R := by unfold chi; positivity
  have hord := truncations_ordered p (chi R) hp hy0
  have hle : P₁ p (chi R) ≤ truncation j p (chi R) := by
    fin_cases j <;> simp only [truncation,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
    · exact le_rfl
    · exact hord.2.1.le
    · exact (hord.2.1.trans hord.2.2).le
  have h1 : P₁ p (chi R) ∈ Ioo (-1) 1 := by
    simpa [truncation] using truncation_mem 0 p (chi R) hp hy
  exact strictMonoOn_one_add_div_one_sub.monotoneOn h1 (truncation_mem j p (chi R) hp hy) hle

/-- The full strict chain for each of the three Cayley kernels. -/
theorem refinement_above (j : Fin 3) (p R : ℝ) (hp : 2 ≤ p) (hR : 1 < R) :
    lower p R < family j p R ∧ family j p R < R^(1/p) ∧ R^(1/p) < upper p R := by
  have hp1 : 1 < p := by linarith
  exact ⟨(lower_lt_halley p R hp hR).trans_le (halley_le_family j p R hp1 hR),
    (family_above j p R hp1 hR).2,upper_strict p R hp1 (by linarith) (by linarith)⟩

theorem refinement_below (j : Fin 3) (p R : ℝ) (hp : 2 ≤ p) (hR : 0 < R) (hR1 : R < 1) :
    lower p R < R^(1/p) ∧ R^(1/p) < family j p R ∧ family j p R < upper p R := by
  have hp1 : 1 < p := by linarith
  have h := (refinement_above j p R⁻¹ hp ((one_lt_inv₀ hR).mpr hR1)).1
  rw [family_reciprocal j p R hR] at h
  have hi := (inv_lt_inv₀ (inv_pos.mpr (family_pos j p R hp1 hR))
    (lower_pos p R⁻¹ hp1 (inv_pos.mpr hR))).mpr h
  refine ⟨lower_strict p R hp1 hR (by linarith),(family_below j p R hp1 hR hR1).1,?_⟩
  simpa [upper] using hi

theorem refined_interval_above (j : Fin 3) (p R : ℝ) (hp : 2 ≤ p) (hR : 1 < R) :
    R^(1/p) ∈ Icc (family j p R) (upper p R) ∧
      Icc (family j p R) (upper p R) ⊂ Icc (lower p R) (upper p R) := by
  obtain ⟨h1,h2,h3⟩ := refinement_above j p R hp hR
  refine ⟨⟨h2.le,h3.le⟩,ssubset_iff_subset_ne.mpr ⟨?_,?_⟩⟩
  · intro t ht
    exact ⟨h1.le.trans ht.1,ht.2⟩
  · intro he
    have hm : lower p R ∈ Icc (family j p R) (upper p R) := by
      rw [he]
      exact ⟨le_rfl,(h1.trans (h2.trans h3)).le⟩
    linarith [hm.1]

theorem refined_interval_below (j : Fin 3) (p R : ℝ) (hp : 2 ≤ p) (hR : 0 < R) (hR1 : R < 1) :
    R^(1/p) ∈ Icc (lower p R) (family j p R) ∧
      Icc (lower p R) (family j p R) ⊂ Icc (lower p R) (upper p R) := by
  obtain ⟨h1,h2,h3⟩ := refinement_below j p R hp hR hR1
  refine ⟨⟨h1.le,h2.le⟩,ssubset_iff_subset_ne.mpr ⟨?_,?_⟩⟩
  · intro t ht
    exact ⟨ht.1,ht.2.trans h3.le⟩
  · intro he
    have hm : upper p R ∈ Icc (lower p R) (family j p R) := by
      rw [he]
      exact ⟨(h1.trans (h2.trans h3)).le,le_rfl⟩
    linarith [hm.2]

end LeanMath.Papers.RealBracket
