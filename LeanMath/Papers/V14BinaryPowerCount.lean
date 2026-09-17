import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic

/-! A binary powering evaluator with an explicit multiplication counter. -/
namespace LeanMath.Papers.V14BinaryPowerCount

/-- Number of set bits in the canonical binary representation. -/
def population (n : ℕ) : ℕ := n.bits.count true

/-- Process the most significant prefix first, then square and optionally multiply by x.
Assignments, bit tests and division of the exponent do not count as multiplications. -/
def run (x : ℝ) (n : ℕ) : ℝ × ℕ :=
  if h0 : n=0 then (1,0) else
  if h1 : n=1 then (x,0) else
  let t := run x (n/2)
  if n%2=0 then (t.1*t.1,t.2+1) else (t.1*t.1*x,t.2+2)
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

theorem population_step (n : ℕ) : population n=population (n/2)+n%2 := by
  have hm := Nat.mod_lt n (by decide : 0<2)
  have he := Nat.mod_add_div n 2
  by_cases h0 : n=0
  · subst n; simp [population]
  by_cases hr : n%2=0
  · have hn : n=2*(n/2) := by omega
    have hq : n/2≠0 := by omega
    conv_lhs => rw [hn]
    simp [population,Nat.bit0_bits _ hq,hr]
  · have hr1 : n%2=1 := by omega
    have hn : n=2*(n/2)+1 := by omega
    conv_lhs => rw [hn]
    unfold population
    rw [Nat.bit1_bits]
    simp [hr1]

theorem population_pos (n : ℕ) (hn : 0<n) : 0<population n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [population_step n]
    by_cases hz : n/2=0
    · have hm := Nat.mod_add_div n 2
      omega
    · have hh := ih (n/2) (Nat.div_lt_self hn (by decide)) (by omega)
      omega

/-- The first projection really computes x^n, not just an abstract recurrence of costs. -/
theorem run_value (x : ℝ) (n : ℕ) : (run x n).1=x^n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [run]
    split
    · next h0 => simp [h0]
    · next h0 =>
      split
      · next h1 => simp [h1]
      · next h1 =>
        have hq : n/2<n := Nat.div_lt_self (by omega) (by decide)
        have hv := ih (n/2) hq
        have hm := Nat.mod_lt n (by decide : 0<2)
        have he := Nat.mod_add_div n 2
        split
        · next hr =>
          simp only [hv]
          rw [←pow_add]
          congr 1
          omega
        · next hr =>
          simp only [hv]
          rw [←pow_add,←pow_succ]
          congr 1
          omega

/-- For every positive exponent: floor(log₂ n) + popcount(n) - 1 multiplications. -/
theorem multiplication_count (x : ℝ) (n : ℕ) (hn : 0<n) :
    (run x n).2=Nat.log 2 n+population n-1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h1 : n=1
    · subst n
      rw [run]
      norm_num [population]
    have h2 : 2≤n := by omega
    have hq0 : 0<n/2 := Nat.div_pos h2 (by decide)
    have hq : n/2<n := Nat.div_lt_self hn (by decide)
    have hc := ih (n/2) hq hq0
    have hl := Nat.log_div_base 2 n
    have hl0 : 0<Nat.log 2 n := Nat.log_pos_iff.mpr ⟨h2,by decide⟩
    have hb := population_step n
    have hb0 := population_pos (n/2) hq0
    rw [run]
    simp only [Nat.ne_of_gt hn,h1, dite_false,if_false]
    split
    · next hr => simp only [hc]; omega
    · next hr =>
      have hm := Nat.mod_lt n (by decide : 0<2)
      simp only [hc]
      omega

/-- Examples in the paper: powering p-1 and multiplying once can cost more. -/
theorem examples (x : ℝ) :
    (run x 7).2+1=5 ∧ (run x 8).2=3 ∧
    (run x 255).2+1=15 ∧ (run x 256).2=8 := by
  simp only [multiplication_count x 7 (by decide),multiplication_count x 8 (by decide),
    multiplication_count x 255 (by decide),multiplication_count x 256 (by decide)]
  decide +kernel

end LeanMath.Papers.V14BinaryPowerCount
