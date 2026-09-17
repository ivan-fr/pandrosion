import Mathlib

namespace PandrosionCertificate

/-- A Farkas witness excludes every real solution, not merely rational ones. -/
theorem farkas_real {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (b w : Fin m → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hz : ∀ j, ∑ i, w i * A i j = 0)
    (hb : ∑ i, w i * b i < 0) :
    ¬ ∃ x : Fin n → ℝ, ∀ i, ∑ j, A i j * x j ≤ b i := by
  rintro ⟨x, hx⟩
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => mul_le_mul_of_nonneg_left (hx i) (hw i))
  have heq : ∑ i, w i * (∑ j, A i j * x j) = 0 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc, ← Finset.sum_mul, hz, zero_mul]
    simp
  rw [heq] at h
  exact (not_le_of_gt hb) h

/-- Rational certificate data may be checked before casting to the reals. -/
theorem farkas_rat {m n : ℕ} (A : Fin m → Fin n → ℚ) (b w : Fin m → ℚ)
    (hw : ∀ i, 0 ≤ w i)
    (hz : ∀ j, ∑ i, w i * A i j = 0)
    (hb : ∑ i, w i * b i < 0) :
    ¬ ∃ x : Fin n → ℝ, ∀ i, ∑ j, (A i j : ℝ) * x j ≤ (b i : ℝ) := by
  apply farkas_real (fun i j => (A i j : ℝ)) (fun i => (b i : ℝ)) (fun i => (w i : ℝ))
  · intro i; exact_mod_cast hw i
  · intro j; exact_mod_cast hz j
  · exact_mod_cast hb

/-- Any independently proved relaxation transfers the certificate to the intended class. -/
theorem excludes_class {m n : ℕ} {S : Type*}
    (A : Fin m → Fin n → ℚ) (b w : Fin m → ℚ)
    (hw : ∀ i, 0 ≤ w i) (hz : ∀ j, ∑ i, w i * A i j = 0)
    (hb : ∑ i, w i * b i < 0)
    (admissible : S → Prop) (encode : S → Fin n → ℝ)
    (relax : ∀ s, admissible s → ∀ i, ∑ j, (A i j : ℝ) * encode s j ≤ (b i : ℝ)) :
    ¬ ∃ s, admissible s := by
  rintro ⟨s, hs⟩
  exact farkas_rat A b w hw hz hb ⟨encode s, relax s hs⟩

#print axioms farkas_real
#print axioms farkas_rat
#print axioms excludes_class
end PandrosionCertificate
