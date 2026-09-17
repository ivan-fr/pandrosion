import LeanMath.Papers.V14Halley

/-! Proposition 11.2: interval derivative bounds certify every point, including
points between partition nodes. The numerical certificate instances are separate. -/
noncomputable section
namespace LeanMath.Papers.V14Uniform
open Real Set

def lowerSum (t lo : ℕ → ℝ) (n : ℕ) := ∑ j ∈ Finset.range n, lo j*(t (j+1)-t j)
def upperSum (t hi : ℕ → ℝ) (n : ℕ) := ∑ j ∈ Finset.range n, hi j*(t (j+1)-t j)

theorem partition_cover (t : ℕ → ℝ) (n : ℕ) (hn : 0 < n) (y : ℝ)
    (hy0 : t 0 ≤ y) (hyn : y ≤ t n) :
    ∃ i < n, t i ≤ y ∧ y ≤ t (i+1) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n=0
    · subst n; exact ⟨0,by omega,hy0,hyn⟩
    · by_cases hy : y ≤ t n
      · obtain ⟨i,hi,hlo,hhi⟩ := ih (by omega) hy
        exact ⟨i,by omega,hlo,hhi⟩
      · exact ⟨n,by omega,(lt_of_not_ge hy).le,hyn⟩

theorem segment_increment (f : ℝ → ℝ) (a b lo hi y : ℝ)
    (hab : a ≤ b) (hy : y ∈ Icc a b) (hc : ContinuousOn f (Icc a b))
    (hd : DifferentiableOn ℝ f (Ioo a b))
    (hb : ∀ x ∈ Ioo a b, lo ≤ deriv f x ∧ deriv f x ≤ hi) :
    lo*(y-a) ≤ f y-f a ∧ f y-f a ≤ hi*(y-a) := by
  have hdi : DifferentiableOn ℝ f (interior (Icc a b)) := by simpa only [interior_Icc] using hd
  exact ⟨(convex_Icc a b).mul_sub_le_image_sub_of_le_deriv hc hdi
    (fun x hx => (hb x (by simpa only [interior_Icc] using hx)).1) a ⟨le_rfl,hab⟩ y hy hy.1,
    (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le hc hdi
    (fun x hx => (hb x (by simpa only [interior_Icc] using hx)).2) a ⟨le_rfl,hab⟩ y hy hy.1⟩

theorem prefix_enclosures (f : ℝ → ℝ) (t lo hi : ℕ → ℝ) (n : ℕ)
    (hzero : f (t 0)=0) (ht : ∀ i < n, t i ≤ t (i+1))
    (hc : ∀ i < n, ContinuousOn f (Icc (t i) (t (i+1))))
    (hd : ∀ i < n, DifferentiableOn ℝ f (Ioo (t i) (t (i+1))))
    (hb : ∀ i < n, ∀ y ∈ Ioo (t i) (t (i+1)), lo i ≤ deriv f y ∧ deriv f y ≤ hi i) :
    ∀ k ≤ n, lowerSum t lo k ≤ f (t k) ∧ f (t k) ≤ upperSum t hi k := by
  intro k hk
  induction k with
  | zero => simp [lowerSum,upperSum,hzero]
  | succ k ih =>
    have hk' : k < n := by omega
    have hprev := ih (by omega)
    have hs := segment_increment f (t k) (t (k+1)) (lo k) (hi k) (t (k+1))
      (ht k hk') ⟨ht k hk',le_rfl⟩ (hc k hk') (hd k hk') (hb k hk')
    simp only [lowerSum,upperSum,Finset.sum_range_succ] at *
    exact ⟨by linarith [hprev.1,hs.1],by linarith [hprev.2,hs.2]⟩

/-- The partial interval increments in Proposition 11.2. -/
theorem partial_increment_bounds (lo hi a b y : ℝ) (hy : y ∈ Icc a b) :
    min 0 lo*(b-a) ≤ lo*(y-a) ∧ hi*(y-a) ≤ max 0 hi*(b-a) := by
  constructor
  · by_cases hl : 0 ≤ lo
    · rw [min_eq_left hl]; nlinarith [hy.1]
    · rw [min_eq_right (le_of_not_ge hl)]; nlinarith [hy.2]
  · by_cases hh : 0 ≤ hi
    · rw [max_eq_right hh]; nlinarith [hy.2]
    · rw [max_eq_left (le_of_not_ge hh)]; nlinarith [hy.1]

/-- All-points positive-half bound from the paper's exact prefix certificates. -/
theorem positive_uniform_bound (f : ℝ → ℝ) (t lo hi : ℕ → ℝ) (n : ℕ) (eta y : ℝ)
    (hn : 0 < n) (hzero : f (t 0)=0) (hy : y ∈ Icc (t 0) (t n))
    (ht : ∀ i < n, t i ≤ t (i+1))
    (hc : ∀ i < n, ContinuousOn f (Icc (t i) (t (i+1))))
    (hd : ∀ i < n, DifferentiableOn ℝ f (Ioo (t i) (t (i+1))))
    (hb : ∀ i < n, ∀ x ∈ Ioo (t i) (t (i+1)), lo i ≤ deriv f x ∧ deriv f x ≤ hi i)
    (hcert : ∀ i < n,
      |lowerSum t lo i+min 0 (lo i)*(t (i+1)-t i)| ≤ eta ∧
      |upperSum t hi i+max 0 (hi i)*(t (i+1)-t i)| ≤ eta) : |f y| ≤ eta := by
  obtain ⟨i,hi',hyi,hyj⟩ := partition_cover t n hn y hy.1 hy.2
  have hp := prefix_enclosures f t lo hi n hzero ht hc hd hb i (by omega)
  have hs := segment_increment f (t i) (t (i+1)) (lo i) (hi i) y
    (ht i hi') ⟨hyi,hyj⟩ (hc i hi') (hd i hi') (hb i hi')
  have hpart := partial_increment_bounds (lo i) (hi i) (t i) (t (i+1)) y ⟨hyi,hyj⟩
  have hl := (abs_le.mp (hcert i hi').1).1
  have hh := (abs_le.mp (hcert i hi').2).2
  apply abs_le.mpr
  exact ⟨by linarith [hp.1,hs.1,hpart.1],by linarith [hp.2,hs.2,hpart.2]⟩

/-- Oddness extends an all-points half-cell bound to the symmetric gate. -/
theorem symmetric_bound (f : ℝ → ℝ) (rho eta : ℝ)
    (hodd : ∀ y, f (-y) = -f y) (hb : ∀ y ∈ Icc 0 rho, |f y| ≤ eta)
    (y : ℝ) (hy : |y| ≤ rho) : |f y| ≤ eta := by
  have h := hb |y| ⟨abs_nonneg y,hy⟩
  by_cases hy0 : 0 ≤ y
  · simpa only [abs_of_nonneg hy0] using h
  · simpa only [abs_of_nonpos (le_of_not_ge hy0),hodd,abs_neg] using h

/-- Final implication of Proposition 11.2, for any positive exact-function ratio. -/
theorem certified_relative_error (v eta : ℝ) (hv : 0 < v) (he0 : 0 ≤ eta)
    (he1 : eta < 1) (hlog : |log v| ≤ eta) : |v-1| ≤ eta/(1-eta) :=
  V14Halley.relative_of_log_bound v eta hv he0 he1 hlog

end LeanMath.Papers.V14Uniform
