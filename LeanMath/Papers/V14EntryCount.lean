import LeanMath.Papers.V14Entry

/-! Exact entry count for a fixed positive Cayley gate (equation 13.9). -/
noncomputable section
namespace LeanMath.Papers.V14EntryCount
open Real Filter Set
open LeanMath.Papers.Cayley LeanMath.Papers.V14Entry

/-- Natural ceiling includes the maximum with zero in the printed formula. -/
def count (p X rho : ℝ) : ℕ :=
  ⌈log (|log X|/(2*artanh rho))/log (p+1)⌉₊

theorem gate_iff (p X rho : ℝ) (hp : 0 < p) (hX : 0 < X) (hX1 : X ≠ 1)
    (hr0 : 0 < rho) (hr1 : rho < 1) (n : ℕ) :
    |chi (residual p X n)| ≤ rho ↔
      log (|log X|/(2*artanh rho))/log (p+1) ≤ (n:ℝ) := by
  have hlX : log X ≠ 0 := by
    intro hz
    apply hX1
    exact log_injOn_pos hX (by norm_num) (by simpa using hz)
  have hnum : 0 < |log X| := abs_pos.mpr hlX
  have hart : 0 < artanh rho := artanh_pos ⟨hr0,hr1⟩
  have hd : 0 < 2*(p+1)^n := by positivity
  have hlogd : 0 < log (p+1) := log_pos (by linarith)
  rw [residual_coordinate p X hX n,V14Entry.abs_tanh,abs_div,abs_of_pos hd]
  rw [← artanh_le_artanh_iff
    ⟨neg_one_lt_tanh _,tanh_lt_one _⟩ ⟨by linarith,hr1⟩,artanh_tanh]
  have h1 : |log X|/(2*(p+1)^n) ≤ artanh rho ↔
      |log X|/(2*artanh rho) ≤ (p+1)^n := by
    rw [div_le_iff₀ hd,div_le_iff₀ (by positivity : 0 < 2*artanh rho)]
    ring_nf
  rw [h1]
  rw [← log_le_log_iff (div_pos hnum (by positivity)) (by positivity : 0 < (p+1)^n)]
  rw [log_pow,div_le_iff₀ hlogd]

theorem exact_count (p X rho : ℝ) (hp : 0 < p) (hX : 0 < X) (hX1 : X ≠ 1)
    (hr0 : 0 < rho) (hr1 : rho < 1) (n : ℕ) :
    |chi (residual p X n)| ≤ rho ↔ count p X rho ≤ n := by
  rw [gate_iff p X rho hp hX hX1 hr0 hr1 n]
  exact Nat.ceil_le.symm

theorem first_accepted_entry (p X rho : ℝ) (hp : 0 < p) (hX : 0 < X) (hX1 : X ≠ 1)
    (hr0 : 0 < rho) (hr1 : rho < 1) :
    |chi (residual p X (count p X rho))| ≤ rho ∧
      ∀ n < count p X rho, rho < |chi (residual p X n)| := by
  constructor
  · exact (exact_count p X rho hp hX hX1 hr0 hr1 _).mpr le_rfl
  · intro n hn
    exact lt_of_not_ge (fun h => (not_le_of_gt hn)
      ((exact_count p X rho hp hX hX1 hr0 hr1 n).mp h))

theorem unit_input (p : ℝ) (n : ℕ) : chi (residual p 1 n)=0 := by
  simp [V14Entry.residual,chi]

end LeanMath.Papers.V14EntryCount
