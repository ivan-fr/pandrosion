import LeanMath.Papers.ExtremalBracket

noncomputable section
namespace LeanMath.Papers.Extremal
open Real MeasureTheory Set

def endpointLaw (m n μ : ℝ) : Measure ℝ :=
  ENNReal.ofReal ((n-μ)/(n-m)) • Measure.dirac m +
  ENNReal.ofReal ((μ-m)/(n-m)) • Measure.dirac n

theorem weights_nonneg (m n μ : ℝ) (hm : m < μ) (hn : μ < n) :
    0 ≤ (n-μ)/(n-m) ∧ 0 ≤ (μ-m)/(n-m) := by
  have hmn := hm.trans hn
  constructor <;> positivity

theorem endpointLaw_probability (m n μ : ℝ) (hm : m < μ) (hn : μ < n) :
    IsProbabilityMeasure (endpointLaw m n μ) := by
  obtain ⟨hw1,hw2⟩ := weights_nonneg m n μ hm hn
  constructor
  calc endpointLaw m n μ univ = ENNReal.ofReal ((n-μ)/(n-m))+ENNReal.ofReal ((μ-m)/(n-m)) := by
         simp [endpointLaw]
       _ = ENNReal.ofReal ((n-μ)/(n-m)+(μ-m)/(n-m)) := (ENNReal.ofReal_add hw1 hw2).symm
       _ = 1 := by rw [weights_sum m n μ (hm.trans hn)]; norm_num

theorem endpointLaw_supported (m n μ : ℝ) (hm : m < μ) (hn : μ < n) :
    ∀ᵐ k ∂endpointLaw m n μ, m ≤ k ∧ k ≤ n := by
  rw [endpointLaw,ae_add_measure_iff]
  have hmn := (hm.trans hn).le
  constructor <;> apply Measure.ae_smul_measure <;> simp [hmn]

theorem endpointLaw_integral (m n μ : ℝ) (hm : m < μ) (hn : μ < n) (f : ℝ → ℝ) :
    (∫ k, f k ∂endpointLaw m n μ) = (n-μ)/(n-m)*f m+(μ-m)/(n-m)*f n := by
  obtain ⟨hw1,hw2⟩ := weights_nonneg m n μ hm hn
  unfold endpointLaw
  rw [integral_add_measure ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)
    ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure,integral_dirac,ENNReal.toReal_ofReal hw1,
    ENNReal.toReal_ofReal hw2,smul_eq_mul]

theorem endpointLaw_mean (m n μ : ℝ) (hm : m < μ) (hn : μ < n) :
    (∫ k, k ∂endpointLaw m n μ)=μ := by
  rw [endpointLaw_integral m n μ hm hn]
  exact weights_mean m n μ (hm.trans hn)

theorem endpointLaw_moment (m n μ t : ℝ) (hm : m < μ) (hn : μ < n) :
    (∫ k, exp (k*t) ∂endpointLaw m n μ)=endpointMGF m n μ t :=
  endpointLaw_integral m n μ hm hn _

/-- The new lower endpoint is attained, for every admissible set of data. -/
theorem lower_attained (m n μ h : ℝ) (hm : m < μ) (hn : μ < n) (hμ : 0 < μ) (hh : 0 < h) :
    ∃ β : ℝ, 0 < β ∧ endpointMGF m n μ β=exp h ∧
      IsProbabilityMeasure (endpointLaw m n μ) ∧
      (∀ᵐ k ∂endpointLaw m n μ, m ≤ k ∧ k ≤ n) ∧
      (∫ k, k ∂endpointLaw m n μ)=μ ∧
      (∫ k, exp (k*β) ∂endpointLaw m n μ)=exp h := by
  obtain ⟨β,hβ,_⟩ := exists_unique_beta m n μ h hm hn hμ hh
  refine ⟨β,hβ.1,hβ.2,endpointLaw_probability m n μ hm hn,
    endpointLaw_supported m n μ hm hn,endpointLaw_mean m n μ hm hn,?_⟩
  rw [endpointLaw_moment m n μ β hm hn,hβ.2]

/-- The upper endpoint is attained by a point mass at the mean in the class
of laws supported in [m,n]. No exact-support convention is silently added. -/
theorem upper_attained (m n μ h : ℝ) (hm : m < μ) (hn : μ < n) (hμ : 0 < μ) :
    IsProbabilityMeasure (Measure.dirac μ) ∧
      (∀ᵐ k ∂Measure.dirac μ, m ≤ k ∧ k ≤ n) ∧
      (∫ k, k ∂Measure.dirac μ)=μ ∧
      (∫ k, exp (k*(h/μ)) ∂Measure.dirac μ)=exp h := by
  refine ⟨inferInstance,by simp [hm.le,hn.le],by simp,?_⟩
  rw [integral_dirac]
  congr 1
  field_simp

end LeanMath.Papers.Extremal
