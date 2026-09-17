import LeanMath.Papers.Dyadic
import LeanMath.Papers.V14Defect

/-! Exact entry recurrence of Proposition 13.2. -/
noncomputable section
namespace LeanMath.Papers.V14Entry
open Real

/-- Recurrent implementation for the p+1 dyadic case: u←u*v, R←v. -/
def state (p X : ℝ) : ℕ → ℝ × ℝ
  | 0 => (1, X)
  | n+1 => let s := state p X n
           let v := s.2 ^ (1/(p+1))
           (s.1*v, v)

def residual (p X : ℝ) (n : ℕ) := X^((1/(p+1))^n)
def approximation (p X : ℝ) (n : ℕ) := X^((1-(1/(p+1))^n)/p)

/-- Closed forms for both components, for every entry count. -/
theorem state_closed (p X : ℝ) (hp : 0 < p) (hX : 0 < X) (n : ℕ) :
    state p X n = (approximation p X n, residual p X n) := by
  have hp0 := hp.ne'
  have hd : p+1 ≠ 0 := by linarith
  induction n with
  | zero => simp [state, approximation, residual]
  | succ n ih =>
    simp only [state, ih, approximation, residual]
    rw [← rpow_mul hX.le, ← rpow_add hX]
    apply Prod.ext
    · change X^_ = X^_
      congr 1
      rw [pow_succ]
      field_simp
      <;> ring
    · change X^_ = X^_
      rw [pow_succ]

/-- The recurrent residual remains coherent in exact arithmetic. -/
theorem coherence (p X : ℝ) (hp : 0 < p) (hX : 0 < X) (n : ℕ) :
    residual p X n * (approximation p X n)^p = X := by
  unfold residual approximation
  rw [← rpow_mul hX.le, ← rpow_add hX]
  convert rpow_one X using 1
  field_simp
  <;> ring

/-- Equation 13.7, the exact root-error formula. -/
theorem log_error (p X : ℝ) (hp : 0 < p) (hX : 0 < X) (n : ℕ) :
    log (approximation p X n / X^(1/p)) = -log X/(p*(p+1)^n) := by
  unfold approximation
  rw [log_div (rpow_pos_of_pos hX _).ne' (rpow_pos_of_pos hX _).ne',
    log_rpow hX, log_rpow hX, div_pow, one_pow]
  have hd : p+1 ≠ 0 := by linarith
  field_simp
  <;> ring

/-- Exact Cayley coordinate after n entries (before any rounding). -/
theorem residual_coordinate (p X : ℝ) (hX : 0 < X) (n : ℕ) :
    LeanMath.Papers.Cayley.chi (residual p X n) =
      tanh (log X/(2*(p+1)^n)) := by
  have hR : 0 < residual p X n := rpow_pos_of_pos hX _
  have hm := LeanMath.Papers.Cayley.chi_mem (residual p X n) hR
  have h := V14Defect.log_unchi _ hm
  rw [LeanMath.Papers.Cayley.unchi_chi _ hR] at h
  unfold residual at h
  rw [log_rpow hX, div_pow, one_pow] at h
  rw [← tanh_artanh hm]
  congr 1
  calc
    artanh (LeanMath.Papers.Cayley.chi (residual p X n)) =
        (log X * (1/(p+1)^n))/2 := by
          unfold residual
          rw [div_pow, one_pow]
          linarith
    _ = log X/(2*(p+1)^n) := by ring

/-- The nearest-integer multiplier in this degree family is exactly one. -/
theorem entry_multiplier (p : ℝ) (hp : 2 < p) : round ((p+1)/p) = 1 := by
  apply round_eq_iff.mpr
  norm_num only [Int.cast_one]
  constructor
  · apply (le_div_iff₀ (by linarith : 0 < p)).mpr; linarith
  · apply (div_lt_iff₀ (by linarith : 0 < p)).mpr; nlinarith

theorem entry_correction (p R : ℝ) (hp : 2 < p) :
    LeanMath.Papers.Dyadic.correction p (p+1) R = R^(1/(p+1)) := by
  unfold LeanMath.Papers.Dyadic.correction
  rw [entry_multiplier p hp]; norm_num

theorem entry_contraction (p : ℝ) (hp : 2 < p) :
    LeanMath.Papers.Dyadic.rho p (p+1) = 1/(p+1) := by
  unfold LeanMath.Papers.Dyadic.rho
  rw [entry_multiplier p hp]
  norm_num
  field_simp
  <;> ring

theorem tanh_monotone : Monotone tanh := by
  intro x y h
  apply (artanh_le_artanh_iff
    ⟨neg_one_lt_tanh x,tanh_lt_one x⟩ ⟨neg_one_lt_tanh y,tanh_lt_one y⟩).mp
  simpa only [artanh_tanh] using h

theorem abs_tanh (x : ℝ) : |tanh x| = tanh |x| := by
  have hp : ∀ t : ℝ, 0 ≤ t → 0 ≤ tanh t := by
    intro t ht
    simpa only [tanh_zero] using tanh_monotone ht
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx,abs_of_nonneg (hp x hx)]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    have ht : tanh x ≤ 0 := by simpa using tanh_monotone hx'
    rw [abs_of_nonpos hx',tanh_neg,abs_of_nonpos ht]

/-- Equation 13.8 bounds every input in the stated logarithmic workload. -/
theorem worst_radius_bound (p X B : ℝ) (hp : 0 < p) (hX : 0 < X)
    (hB : |log X| ≤ B) (n : ℕ) :
    |LeanMath.Papers.Cayley.chi (residual p X n)| ≤ tanh (B/(2*(p+1)^n)) := by
  rw [residual_coordinate p X hX n,abs_tanh,abs_div,
    abs_of_pos (by positivity : 0 < 2*(p+1)^n)]
  exact tanh_monotone ((div_le_div_iff_of_pos_right (by positivity)).mpr hB)

/-- The upper workload endpoint attains the radius, so the bound is sharp. -/
theorem worst_radius_attained (p B : ℝ) (hp : 0 < p) (hB : 0 ≤ B) (n : ℕ) :
    |LeanMath.Papers.Cayley.chi (residual p (exp B) n)| = tanh (B/(2*(p+1)^n)) := by
  rw [residual_coordinate p (exp B) (exp_pos B) n,log_exp,abs_tanh,
    abs_of_nonneg (by positivity : 0 ≤ B/(2*(p+1)^n))]

end LeanMath.Papers.V14Entry
