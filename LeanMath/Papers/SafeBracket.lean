import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

noncomputable section
namespace LeanMath.Papers.SafeBracket
open Filter Function
open scoped Topology

def midpoint (ab : ℝ × ℝ) := (ab.1+ab.2)/2
def step (f : ℝ → ℝ) (c : ℝ) (ab : ℝ × ℝ) :=
  if f (midpoint ab) ≤ c then (midpoint ab,ab.2) else (ab.1,midpoint ab)

/-- Every iteration keeps the selected root inside the bracket. -/
theorem preserves (f : ℝ → ℝ) (c r : ℝ) (ab : ℝ × ℝ)
    (hm : StrictMonoOn f (Set.Icc ab.1 ab.2))
    (hr : f r=c) (hb : ab.1 ≤ r ∧ r ≤ ab.2) :
    (step f c ab).1 ≤ r ∧ r ≤ (step f c ab).2 := by
  have hmid : midpoint ab ∈ Set.Icc ab.1 ab.2 := by
    unfold midpoint
    constructor <;> linarith
  unfold step
  split_ifs with h
  · refine ⟨?_,hb.2⟩
    by_contra! hbad
    have hh := hm hb hmid hbad
    rw [hr] at hh
    linarith
  · refine ⟨hb.1,?_⟩
    by_contra! hbad
    have hh := hm hmid hb hbad
    rw [hr] at hh
    linarith

theorem contained (f : ℝ → ℝ) (c : ℝ) (ab : ℝ × ℝ) (hab : ab.1 ≤ ab.2) :
    ab.1 ≤ (step f c ab).1 ∧ (step f c ab).2 ≤ ab.2 := by
  unfold step midpoint
  split_ifs <;> simp only [Prod.fst,Prod.snd] <;> constructor <;> linarith

theorem width_halved (f : ℝ → ℝ) (c : ℝ) (ab : ℝ × ℝ) :
    (step f c ab).2-(step f c ab).1=(ab.2-ab.1)/2 := by
  unfold step midpoint
  split_ifs <;> simp only [Prod.fst,Prod.snd] <;> ring

theorem orbit_certificate (f : ℝ → ℝ) (c r a b : ℝ)
    (hm : StrictMonoOn f (Set.Icc a b)) (hr : f r=c) (hb : a ≤ r ∧ r ≤ b) :
    ∀ n : ℕ, let ab := (step f c)^[n] (a,b)
      a ≤ ab.1 ∧ ab.1 ≤ r ∧ r ≤ ab.2 ∧ ab.2 ≤ b ∧ ab.2-ab.1=(b-a)/2^n := by
  intro n
  induction n with
  | zero => simp; exact ⟨hb.1,hb.2⟩
  | succ n ih =>
    dsimp only at ih ⊢
    rw [iterate_succ_apply']
    have hsub : Set.Icc ((step f c)^[n] (a,b)).1 ((step f c)^[n] (a,b)).2 ⊆ Set.Icc a b := by
      intro t ht
      exact ⟨ih.1.trans ht.1,ht.2.trans ih.2.2.2.1⟩
    have hroot := preserves f c r _ (hm.mono hsub) hr ⟨ih.2.1,ih.2.2.1⟩
    have hcont := contained f c ((step f c)^[n] (a,b)) (ih.2.1.trans ih.2.2.1)
    refine ⟨ih.1.trans hcont.1,hroot.1,hroot.2,hcont.2.trans ih.2.2.2.1,?_⟩
    rw [width_halved,ih.2.2.2.2,pow_succ]
    ring

theorem midpoint_error (f : ℝ → ℝ) (c r a b : ℝ)
    (hm : StrictMonoOn f (Set.Icc a b)) (hr : f r=c) (hb : a ≤ r ∧ r ≤ b) (n : ℕ) :
    |midpoint ((step f c)^[n] (a,b))-r| ≤ (b-a)/2^(n+1) := by
  have h := orbit_certificate f c r a b hm hr hb n
  dsimp only at h
  have hw := h.2.2.2.2
  rw [pow_succ,←div_div,←hw]
  unfold midpoint
  apply abs_le.mpr
  constructor <;> linarith [h.2.1,h.2.2.1]

/-- A finite iteration budget exists for every strictly positive requested tolerance. -/
theorem finite_tolerance (f : ℝ → ℝ) (c r a b ε : ℝ)
    (hm : StrictMonoOn f (Set.Icc a b)) (hr : f r=c) (hb : a ≤ r ∧ r ≤ b) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, |midpoint ((step f c)^[n] (a,b))-r| < ε := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1:ℝ)/2 < 1)
  have ht := hp.mul_const ((b-a)/2)
  have hev : ∀ᶠ n : ℕ in atTop, (1/2:ℝ)^n*((b-a)/2) < ε := by
    apply (tendsto_order.mp ht).2 ε
    simpa using hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp hev
  refine ⟨N,fun n hn => (midpoint_error f c r a b hm hr hb n).trans_lt ?_⟩
  have h := hN n hn
  have he : (b-a)/(2:ℝ)^(n+1)=(1/2:ℝ)^n*((b-a)/2) := by
    rw [pow_succ,div_pow]
    simp only [one_pow]
    ring
  rwa [he]

end LeanMath.Papers.SafeBracket
