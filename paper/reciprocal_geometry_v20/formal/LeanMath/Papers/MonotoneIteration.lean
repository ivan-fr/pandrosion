import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

noncomputable section
namespace LeanMath.Papers.Iteration
open Filter Set Function
open scoped Topology

/-- A continuous scalar update which moves strictly toward a positive fixed
point from both sides converges from every positive starting point. -/
theorem converge (f : ℝ → ℝ) (r u : ℝ) (hr : 0 < r) (hu : 0 < u)
    (hc : ∀ t, 0 < t → ContinuousAt f t) (hfix : f r = r)
    (hbelow : ∀ t, 0 < t → t < r → t < f t ∧ f t < r)
    (habove : ∀ t, r < t → r < f t ∧ f t < t) :
    Tendsto (fun n : ℕ => f^[n] u) atTop (𝓝 r) := by
  have unique : ∀ t, 0 < t → f t = t → t = r := by
    intro t ht he
    rcases lt_trichotomy t r with h | h | h
    · have hh := (hbelow t ht h).1
      linarith
    · exact h
    · have hh := (habove t h).2
      linarith
  by_cases hstart : u ≤ r
  · have inv : ∀ n : ℕ, f^[n] u ∈ Icc u r := by
      intro n
      induction n with
      | zero => simpa using hstart
      | succ n ih =>
        rw [iterate_succ_apply']
        rcases lt_or_eq_of_le ih.2 with h | h
        · have hh := hbelow (f^[n] u) (hu.trans_le ih.1) h
          exact ⟨ih.1.trans hh.1.le,hh.2.le⟩
        · rw [h,hfix]
          exact ⟨hstart,le_rfl⟩
    have hm : Monotone (fun n : ℕ => f^[n] u) := by
      apply monotone_nat_of_le_succ
      intro n
      rw [iterate_succ_apply']
      rcases lt_or_eq_of_le (inv n).2 with h | h
      · exact (hbelow _ (hu.trans_le (inv n).1) h).1.le
      · rw [h,hfix]
    have hb : BddAbove (range (fun n : ℕ => f^[n] u)) := ⟨r,by
      rintro _ ⟨n,rfl⟩; exact (inv n).2⟩
    have ht := tendsto_atTop_ciSup hm hb
    have hi := isClosed_Icc.mem_of_tendsto ht (Eventually.of_forall inv)
    have hpos : 0 < ⨆ n : ℕ, f^[n] u := hu.trans_le hi.1
    have ht' := ht.comp (tendsto_add_atTop_nat 1)
    have hft := (hc _ hpos).tendsto.comp ht
    have hsame : f (⨆ n : ℕ, f^[n] u) = ⨆ n : ℕ, f^[n] u := by
      apply tendsto_nhds_unique hft
      simpa only [Function.comp_def,iterate_succ_apply'] using ht'
    rwa [unique _ hpos hsame] at ht
  · have hstart' : r ≤ u := le_of_not_ge hstart
    have inv : ∀ n : ℕ, f^[n] u ∈ Icc r u := by
      intro n
      induction n with
      | zero => simpa using hstart'
      | succ n ih =>
        rw [iterate_succ_apply']
        rcases lt_or_eq_of_le ih.1 with h | h
        · have hh := habove (f^[n] u) h
          exact ⟨hh.1.le,hh.2.le.trans ih.2⟩
        · rw [←h,hfix]
          exact ⟨le_rfl,hstart'⟩
    have hm : Antitone (fun n : ℕ => f^[n] u) := by
      apply antitone_nat_of_succ_le
      intro n
      rw [iterate_succ_apply']
      rcases lt_or_eq_of_le (inv n).1 with h | h
      · exact (habove _ h).2.le
      · rw [←h,hfix]
    have hb : BddBelow (range (fun n : ℕ => f^[n] u)) := ⟨r,by
      rintro _ ⟨n,rfl⟩; exact (inv n).1⟩
    have ht := tendsto_atTop_ciInf hm hb
    have hi := isClosed_Icc.mem_of_tendsto ht (Eventually.of_forall inv)
    have hpos : 0 < ⨅ n : ℕ, f^[n] u := hr.trans_le hi.1
    have ht' := ht.comp (tendsto_add_atTop_nat 1)
    have hft := (hc _ hpos).tendsto.comp ht
    have hsame : f (⨅ n : ℕ, f^[n] u) = ⨅ n : ℕ, f^[n] u := by
      apply tendsto_nhds_unique hft
      simpa only [Function.comp_def,iterate_succ_apply'] using ht'
    rwa [unique _ hpos hsame] at ht

end LeanMath.Papers.Iteration
