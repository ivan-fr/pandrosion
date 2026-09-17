import LeanMath.Papers.MonotoneIteration

noncomputable section
namespace LeanMath.Papers.IntervalIteration
open Filter Set Function
open scoped Topology

/-- Convergence inside a closed invariant interval, allowing an exact hit of the root. -/
theorem converge (f : ℝ → ℝ) (a b r u : ℝ) (hr : r ∈ Icc a b) (hu : u ∈ Icc a b)
    (hc : ∀ t ∈ Icc a b, ContinuousAt f t) (hfix : f r=r)
    (hbelow : ∀ t ∈ Icc a b, t < r → t < f t ∧ f t ≤ r)
    (habove : ∀ t ∈ Icc a b, r < t → r ≤ f t ∧ f t < t) :
    Tendsto (fun n : ℕ => f^[n] u) atTop (𝓝 r) := by
  have unique : ∀ t ∈ Icc a b, f t=t → t=r := by
    intro t ht he
    rcases lt_trichotomy t r with h | h | h
    · have hh := (hbelow t ht h).1
      linarith
    · exact h
    · have hh := (habove t ht h).2
      linarith
  by_cases hstart : u ≤ r
  · have hsub : Icc u r ⊆ Icc a b := fun t ht => ⟨hu.1.trans ht.1,ht.2.trans hr.2⟩
    have inv : ∀ n : ℕ, f^[n] u ∈ Icc u r := by
      intro n
      induction n with
      | zero => simpa using hstart
      | succ n ih =>
        rw [iterate_succ_apply']
        rcases lt_or_eq_of_le ih.2 with h | h
        · have hh := hbelow _ (hsub ih) h
          exact ⟨ih.1.trans hh.1.le,hh.2⟩
        · rw [h,hfix]
          exact ⟨hstart,le_rfl⟩
    have hm : Monotone (fun n : ℕ => f^[n] u) := by
      apply monotone_nat_of_le_succ
      intro n
      rw [iterate_succ_apply']
      rcases lt_or_eq_of_le (inv n).2 with h | h
      · exact (hbelow _ (hsub (inv n)) h).1.le
      · rw [h,hfix]
    have hb : BddAbove (range (fun n : ℕ => f^[n] u)) := ⟨r,by
      rintro _ ⟨n,rfl⟩; exact (inv n).2⟩
    have ht := tendsto_atTop_ciSup hm hb
    have hi := isClosed_Icc.mem_of_tendsto ht (Eventually.of_forall inv)
    have ht' := ht.comp (tendsto_add_atTop_nat 1)
    have hft := (hc _ (hsub hi)).tendsto.comp ht
    have he : f (⨆ n : ℕ, f^[n] u)=⨆ n : ℕ, f^[n] u := by
      apply tendsto_nhds_unique hft
      simpa only [Function.comp_def,iterate_succ_apply'] using ht'
    rwa [unique _ (hsub hi) he] at ht
  · have hstart' : r ≤ u := le_of_not_ge hstart
    have hsub : Icc r u ⊆ Icc a b := fun t ht => ⟨hr.1.trans ht.1,ht.2.trans hu.2⟩
    have inv : ∀ n : ℕ, f^[n] u ∈ Icc r u := by
      intro n
      induction n with
      | zero => simpa using hstart'
      | succ n ih =>
        rw [iterate_succ_apply']
        rcases lt_or_eq_of_le ih.1 with h | h
        · have hh := habove _ (hsub ih) h
          exact ⟨hh.1,hh.2.le.trans ih.2⟩
        · rw [←h,hfix]
          exact ⟨le_rfl,hstart'⟩
    have hm : Antitone (fun n : ℕ => f^[n] u) := by
      apply antitone_nat_of_succ_le
      intro n
      rw [iterate_succ_apply']
      rcases lt_or_eq_of_le (inv n).1 with h | h
      · exact (habove _ (hsub (inv n)) h).2.le
      · rw [←h,hfix]
    have hb : BddBelow (range (fun n : ℕ => f^[n] u)) := ⟨r,by
      rintro _ ⟨n,rfl⟩; exact (inv n).1⟩
    have ht := tendsto_atTop_ciInf hm hb
    have hi := isClosed_Icc.mem_of_tendsto ht (Eventually.of_forall inv)
    have ht' := ht.comp (tendsto_add_atTop_nat 1)
    have hft := (hc _ (hsub hi)).tendsto.comp ht
    have he : f (⨅ n : ℕ, f^[n] u)=⨅ n : ℕ, f^[n] u := by
      apply tendsto_nhds_unique hft
      simpa only [Function.comp_def,iterate_succ_apply'] using ht'
    rwa [unique _ (hsub hi) he] at ht

end LeanMath.Papers.IntervalIteration
