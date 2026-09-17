import LeanMath.Papers.SafeBracket
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
namespace LeanMath.Papers.GuardedBracket
open Real Filter Function Set
open scoped Topology

def middle (ab : ℝ × ℝ) := (ab.1+ab.2)/2
def central (ab : ℝ × ℝ) (x : ℝ) := (3*ab.1+ab.2)/4 ≤ x ∧ x ≤ (ab.1+3*ab.2)/4

def trial (proposal : ℝ → ℝ) (ab : ℝ × ℝ) : ℝ := by
  classical
  exact if central ab (proposal (middle ab)) then proposal (middle ab) else middle ab

def step (f : ℝ → ℝ) (c : ℝ) (proposal : ℝ → ℝ) (ab : ℝ × ℝ) :=
  if f (trial proposal ab) ≤ c then (trial proposal ab,ab.2) else (ab.1,trial proposal ab)

theorem trial_central (proposal : ℝ → ℝ) (ab : ℝ × ℝ) (hab : ab.1 ≤ ab.2) :
    central ab (trial proposal ab) := by
  unfold trial
  split_ifs with h
  · exact h
  · unfold central middle
    constructor <;> linarith

theorem trial_mem (proposal : ℝ → ℝ) (ab : ℝ × ℝ) (hab : ab.1 ≤ ab.2) :
    trial proposal ab ∈ Icc ab.1 ab.2 := by
  have h := trial_central proposal ab hab
  unfold central at h
  constructor <;> linarith [h.1,h.2]

theorem preserves (f : ℝ → ℝ) (c r : ℝ) (proposal : ℝ → ℝ) (ab : ℝ × ℝ)
    (hm : StrictMonoOn f (Icc ab.1 ab.2)) (hr : f r=c) (hb : r ∈ Icc ab.1 ab.2) :
    r ∈ Icc (step f c proposal ab).1 (step f c proposal ab).2 := by
  have ht := trial_mem proposal ab (hb.1.trans hb.2)
  unfold step
  split_ifs with h
  · refine ⟨?_,hb.2⟩
    by_contra! hbad
    have hh := hm hb ht hbad
    rw [hr] at hh
    linarith
  · refine ⟨hb.1,?_⟩
    by_contra! hbad
    have hh := hm ht hb hbad
    rw [hr] at hh
    linarith

theorem contained (f : ℝ → ℝ) (c : ℝ) (proposal : ℝ → ℝ) (ab : ℝ × ℝ)
    (hab : ab.1 ≤ ab.2) :
    ab.1 ≤ (step f c proposal ab).1 ∧ (step f c proposal ab).2 ≤ ab.2 := by
  have ht := trial_mem proposal ab hab
  unfold step
  split_ifs <;> simp only [Prod.fst,Prod.snd] <;> constructor <;> linarith [ht.1,ht.2]

/-- The guard ensures a uniform contraction, regardless of the candidate's quality. -/
theorem width_contracts (f : ℝ → ℝ) (c : ℝ) (proposal : ℝ → ℝ) (ab : ℝ × ℝ)
    (hab : ab.1 ≤ ab.2) :
    (step f c proposal ab).2-(step f c proposal ab).1 ≤ (3/4:ℝ)*(ab.2-ab.1) := by
  have ht := trial_central proposal ab hab
  unfold central at ht
  unfold step
  split_ifs <;> simp only [Prod.fst,Prod.snd] <;> linarith [ht.1,ht.2]

def orbit (f : ℝ → ℝ) (c : ℝ) (proposal : ℝ → ℝ) (a b : ℝ) (n : ℕ) :=
  (step f c proposal)^[n] (a,b)

theorem orbit_certificate (f : ℝ → ℝ) (c r a b : ℝ) (proposal : ℝ → ℝ)
    (hm : StrictMonoOn f (Icc a b)) (hr : f r=c) (hb : r ∈ Icc a b) :
    ∀ n : ℕ, let ab := orbit f c proposal a b n
      a ≤ ab.1 ∧ ab.1 ≤ r ∧ r ≤ ab.2 ∧ ab.2 ≤ b ∧ ab.2-ab.1 ≤ (3/4:ℝ)^n*(b-a) := by
  intro n
  induction n with
  | zero => simpa [orbit] using And.intro hb.1 hb.2
  | succ n ih =>
    dsimp only at ih ⊢
    have he : orbit f c proposal a b (n+1)=step f c proposal (orbit f c proposal a b n) := by
      exact iterate_succ_apply' _ _ _
    rw [he]
    have hsub : Icc (orbit f c proposal a b n).1 (orbit f c proposal a b n).2 ⊆ Icc a b := by
      intro t ht
      exact ⟨ih.1.trans ht.1,ht.2.trans ih.2.2.2.1⟩
    have hroot := preserves f c r proposal _ (hm.mono hsub) hr ⟨ih.2.1,ih.2.2.1⟩
    have hc := contained f c proposal (orbit f c proposal a b n) (ih.2.1.trans ih.2.2.1)
    have hw := width_contracts f c proposal (orbit f c proposal a b n) (ih.2.1.trans ih.2.2.1)
    refine ⟨ih.1.trans hc.1,hroot.1,hroot.2,hc.2.trans ih.2.2.2.1,?_⟩
    rw [pow_succ]
    nlinarith [ih.2.2.2.2]

theorem midpoint_error (f : ℝ → ℝ) (c r a b : ℝ) (proposal : ℝ → ℝ)
    (hm : StrictMonoOn f (Icc a b)) (hr : f r=c) (hb : r ∈ Icc a b) (n : ℕ) :
    |middle (orbit f c proposal a b n)-r| ≤ (3/4:ℝ)^n*(b-a)/2 := by
  have h := orbit_certificate f c r a b proposal hm hr hb n
  unfold middle
  apply abs_le.mpr
  constructor <;> linarith [h.2.1,h.2.2.1,h.2.2.2.2]

/-- A finite observable width stopping test is eventually satisfied. -/
theorem finite_width (f : ℝ → ℝ) (c r a b ε : ℝ) (proposal : ℝ → ℝ)
    (hm : StrictMonoOn f (Icc a b)) (hr : f r=c) (hb : r ∈ Icc a b) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, (orbit f c proposal a b n).2-(orbit f c proposal a b n).1 < 2*ε := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 3/4)
    (by norm_num : (3:ℝ)/4 < 1)
  have ht := hp.mul_const (b-a)
  have hev : ∀ᶠ n : ℕ in atTop, (3/4:ℝ)^n*(b-a) < 2*ε := by
    apply (tendsto_order.mp ht).2 (2*ε)
    simpa using (mul_pos (by norm_num : (0:ℝ)<2) hε)
  obtain ⟨N,hN⟩ := eventually_atTop.mp hev
  exact ⟨N,fun n hn => (orbit_certificate f c r a b proposal hm hr hb n).2.2.2.2.trans_lt (hN n hn)⟩

theorem convergence (f : ℝ → ℝ) (c r a b : ℝ) (proposal : ℝ → ℝ)
    (hm : StrictMonoOn f (Icc a b)) (hr : f r=c) (hb : r ∈ Icc a b) :
    Tendsto (fun n => middle (orbit f c proposal a b n)) atTop (𝓝 r) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := finite_width f c r a b ε proposal hm hr hb hε
  refine ⟨N,fun n hn => ?_⟩
  have h := orbit_certificate f c r a b proposal hm hr hb n
  rw [Real.dist_eq]
  apply abs_lt.mpr
  unfold middle
  constructor <;> linarith [h.2.1,h.2.2.1,hN n hn]

def stopped (f : ℝ → ℝ) (c : ℝ) (proposal : ℝ → ℝ) (a b ε : ℝ) (n : ℕ) :=
  (orbit f c proposal a b n).2-(orbit f c proposal a b n).1 < 2*ε

/-- First successful width test; the impossible branch is excluded by the termination theorem. -/
def stopIndex (f : ℝ → ℝ) (c : ℝ) (proposal : ℝ → ℝ) (a b ε : ℝ) : ℕ := by
  classical
  exact if h : ∃ n, stopped f c proposal a b ε n then Nat.find h else 0

def solve (f : ℝ → ℝ) (c : ℝ) (proposal : ℝ → ℝ) (a b ε : ℝ) :=
  orbit f c proposal a b (stopIndex f c proposal a b ε)

theorem stopIndex_spec (f : ℝ → ℝ) (c r a b ε : ℝ) (proposal : ℝ → ℝ)
    (hm : StrictMonoOn f (Icc a b)) (hr : f r=c) (hb : r ∈ Icc a b) (hε : 0 < ε) :
    stopped f c proposal a b ε (stopIndex f c proposal a b ε) := by
  classical
  obtain ⟨N,hN⟩ := finite_width f c r a b ε proposal hm hr hb hε
  have hex : ∃ n, stopped f c proposal a b ε n := ⟨N,hN N le_rfl⟩
  unfold stopIndex
  rw [dif_pos hex]
  exact Nat.find_spec hex

/-- The returned interval is certified and its midpoint has the requested absolute error. -/
theorem solve_certificate (f : ℝ → ℝ) (c r a b ε : ℝ) (proposal : ℝ → ℝ)
    (hm : StrictMonoOn f (Icc a b)) (hr : f r=c) (hb : r ∈ Icc a b) (hε : 0 < ε) :
    let ab := solve f c proposal a b ε
    a ≤ ab.1 ∧ ab.1 ≤ r ∧ r ≤ ab.2 ∧ ab.2 ≤ b ∧ ab.2-ab.1 < 2*ε ∧ |middle ab-r| < ε := by
  have h := orbit_certificate f c r a b proposal hm hr hb (stopIndex f c proposal a b ε)
  have hw := stopIndex_spec f c r a b ε proposal hm hr hb hε
  change (solve f c proposal a b ε).2-(solve f c proposal a b ε).1 < 2*ε at hw
  change a ≤ (solve f c proposal a b ε).1 ∧ (solve f c proposal a b ε).1 ≤ r ∧
    r ≤ (solve f c proposal a b ε).2 ∧ (solve f c proposal a b ε).2 ≤ b ∧
    (solve f c proposal a b ε).2-(solve f c proposal a b ε).1 ≤ _ at h
  refine ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,hw,?_⟩
  apply abs_lt.mpr
  unfold middle
  constructor <;> linarith [h.2.1,h.2.2.1]

/-- Endpoint sign tests and continuity suffice; no root value is supplied to the algorithm. -/
theorem solve_from_signs (f : ℝ → ℝ) (c a b ε : ℝ) (proposal : ℝ → ℝ)
    (hab : a ≤ b) (hc : ContinuousOn f (Icc a b)) (hm : StrictMonoOn f (Icc a b))
    (ha : f a ≤ c) (hb : c ≤ f b) (hε : 0 < ε) :
    ∃ r : ℝ, f r=c ∧ r ∈ Icc (solve f c proposal a b ε).1 (solve f c proposal a b ε).2 ∧
      |middle (solve f c proposal a b ε)-r| < ε := by
  obtain ⟨r,hr,hval⟩ := intermediate_value_Icc hab hc ⟨ha,hb⟩
  have h := solve_certificate f c r a b ε proposal hm hval hr hε
  exact ⟨r,hval,⟨h.2.1,h.2.2.1⟩,h.2.2.2.2.2⟩

theorem accepts_central (proposal : ℝ → ℝ) (ab : ℝ × ℝ)
    (h : central ab (proposal (middle ab))) : trial proposal ab=proposal (middle ab) := by
  simp [trial,h]

theorem rejects_outside (proposal : ℝ → ℝ) (ab : ℝ × ℝ)
    (h : ¬ central ab (proposal (middle ab))) : trial proposal ab=middle ab := by
  simp [trial,h]

theorem orbit_nested (f : ℝ → ℝ) (c r a b : ℝ) (proposal : ℝ → ℝ)
    (hm : StrictMonoOn f (Icc a b)) (hr : f r=c) (hb : r ∈ Icc a b) (n : ℕ) :
    Icc (orbit f c proposal a b (n+1)).1 (orbit f c proposal a b (n+1)).2 ⊆
      Icc (orbit f c proposal a b n).1 (orbit f c proposal a b n).2 := by
  have hc := orbit_certificate f c r a b proposal hm hr hb n
  have h := contained f c proposal (orbit f c proposal a b n) (hc.2.1.trans hc.2.2.1)
  have he : orbit f c proposal a b (n+1)=step f c proposal (orbit f c proposal a b n) :=
    iterate_succ_apply' _ _ _
  rw [he]
  intro x hx
  exact ⟨h.1.trans hx.1,hx.2.trans h.2⟩

/-- Any a priori geometric width budget bounds the first stopping index. -/
theorem iteration_bound (f : ℝ → ℝ) (c r a b ε : ℝ) (proposal : ℝ → ℝ)
    (hm : StrictMonoOn f (Icc a b)) (hr : f r=c) (hb : r ∈ Icc a b)
    (N : ℕ) (hN : (3/4:ℝ)^N*(b-a) < 2*ε) :
    stopIndex f c proposal a b ε ≤ N := by
  classical
  have hs : stopped f c proposal a b ε N :=
    (orbit_certificate f c r a b proposal hm hr hb N).2.2.2.2.trans_lt hN
  have hex : ∃ n, stopped f c proposal a b ε n := ⟨N,hs⟩
  unfold stopIndex
  rw [dif_pos hex]
  exact Nat.find_min' hex hs

end LeanMath.Papers.GuardedBracket
