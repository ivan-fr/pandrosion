import LeanMath.Papers.V14CompressedAnalytic
import Mathlib.RingTheory.PowerSeries.Derivative

/-! Differential identities for the existing analytic root-coordinate series. -/
noncomputable section
namespace LeanMath.Papers.V14SeriesRecurrence
open PowerSeries Polynomial
open LeanMath.Papers.V14RootSeries

theorem choose_step (a : ℝ) (n : ℕ) :
    ((n:ℝ)+1)*Ring.choose a (n+1)=(a-n)*Ring.choose a n := by
  have hh := Ring.descPochhammer_eq_factorial_smul_choose a (n+1)
  rw [descPochhammer_succ_right,Polynomial.smeval_mul,Polynomial.smeval_sub,
    Polynomial.smeval_X,Polynomial.smeval_natCast,Ring.descPochhammer_eq_factorial_smul_choose] at hh
  simp only [nsmul_eq_mul,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,
    pow_one,pow_zero,mul_one] at hh
  have hn : (n.factorial:ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero n
  apply mul_left_cancel₀ hn
  nlinarith [hh]

theorem scaled_binomial_ode (a b : ℝ) :
    (1+PowerSeries.C b*PowerSeries.X)*PowerSeries.derivative ℝ (rescale b (binomialSeries ℝ a))=
      PowerSeries.C (a*b)*rescale b (binomialSeries ℝ a) := by
  ext n
  cases n with
  | zero =>
    simp only [add_mul,one_mul,mul_assoc,map_add,PowerSeries.coeff_C_mul,coeff_zero_X_mul,
      PowerSeries.coeff_derivative,coeff_rescale,binomialSeries_coeff]
    simp [mul_comm]
  | succ n =>
    simp only [add_mul,one_mul,mul_assoc,map_add,PowerSeries.coeff_C_mul,
      coeff_succ_X_mul,PowerSeries.coeff_derivative,coeff_rescale,binomialSeries_coeff,
      smul_eq_mul,mul_one,Nat.cast_add,Nat.cast_one]
    have hh := choose_step a (n+1)
    simp only [Nat.cast_add,Nat.cast_one] at hh
    rw [pow_succ,pow_succ]
    nlinarith [congrArg (fun t : ℝ => b^n*b*b*t) hh]

theorem root_ode (a : ℝ) :
    (1-(PowerSeries.X:PS)^2)*PowerSeries.derivative ℝ (rootSeries a)=PowerSeries.C (2*a)*rootSeries a := by
  have hb := scaled_binomial_ode a 1
  have hz := scaled_binomial_ode (-a) (-1)
  simp only [rescale_one,map_one,one_mul,mul_one] at hb
  norm_num only [neg_mul_neg,mul_one,map_neg,map_one,neg_one_mul,←sub_eq_add_neg] at hz
  unfold rootSeries
  rw [Derivation.leibniz]
  simp only [map_mul,map_ofNat]
  linear_combination
    (1-(PowerSeries.X:PS))*rescale (-1) (binomialSeries ℝ (-a))*hb +
    (1+(PowerSeries.X:PS))*binomialSeries ℝ a*hz

/-- Riccati identity for the exact formal series of tanh(a*artanh y). -/
theorem coordinate_ode (a : ℝ) :
    (1-(PowerSeries.X:PS)^2)*PowerSeries.derivative ℝ (coordinate a)=
      PowerSeries.C a*(1-(coordinate a)^2) := by
  have he := coordinate_equation a
  have hd := congrArg (PowerSeries.derivative ℝ) he
  simp only [Derivation.leibniz,map_add,map_sub,PowerSeries.derivative_one,add_zero,sub_zero] at hd
  have hr := root_ode a
  have hn : rootSeries a+1≠0 := by
    intro hz
    have hh := congrArg PowerSeries.constantCoeff hz
    simp [root_constant] at hh
  apply mul_right_cancel₀ hn
  simp only [map_mul,map_ofNat] at hr
  linear_combination
    (1-(PowerSeries.X:PS)^2)*hd + (1-coordinate a)*hr +
    PowerSeries.C a*(coordinate a-1)*he

theorem coordinate_square_coeff (a : ℝ) (n : ℕ) :
    PowerSeries.coeff (2*n+2) ((coordinate a)^2)=
      ∑ k ∈ Finset.range (n+1),
        PowerSeries.coeff (2*k+1) (coordinate a)*PowerSeries.coeff (2*(n-k)+1) (coordinate a) := by
  have he : (coordinate a)^2=(PowerSeries.X:PS)^2*expand 2 (by decide) ((compressed a)^2) := by
    rw [compressed_identity,mul_pow,map_pow]
  rw [he,PowerSeries.coeff_X_pow_mul,PowerSeries.coeff_expand_mul,pow_two,PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j =>
      PowerSeries.coeff i (compressed a)*PowerSeries.coeff j (compressed a)) n]
  simp [compressed]

/-- General odd-coefficient recurrence, indexed from n=0 to avoid truncated subtraction. -/
theorem odd_recurrence (a : ℝ) (n : ℕ) :
    (2*(n:ℝ)+3)*PowerSeries.coeff (2*n+3) (coordinate a)=
      (2*(n:ℝ)+1)*PowerSeries.coeff (2*n+1) (coordinate a)-
      a*∑ k ∈ Finset.range (n+1),
        PowerSeries.coeff (2*k+1) (coordinate a)*PowerSeries.coeff (2*(n-k)+1) (coordinate a) := by
  have hh := congrArg (PowerSeries.coeff (2*n+2)) (coordinate_ode a)
  simp only [sub_mul,one_mul,map_sub,PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul,PowerSeries.coeff_derivative,PowerSeries.coeff_one] at hh
  rw [coordinate_square_coeff] at hh
  norm_num only [show 2*n+2≠0 by omega,ite_false,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at hh
  have hi : 2*n+2+1=2*n+3 := by omega
  rw [hi] at hh
  linarith

/-- The initial odd coefficient is the reciprocal degree parameter. -/
theorem first_coefficient (a : ℝ) : PowerSeries.coeff 1 (coordinate a)=a := by
  have hh := congrArg (PowerSeries.coeff 0) (coordinate_ode a)
  have hz := even_coordinate_coeff a 0
  norm_num only [Nat.mul_zero] at hz
  simp only [sub_mul,one_mul,map_sub,PowerSeries.coeff_C_mul] at hh
  have hx : PowerSeries.coeff 0 ((PowerSeries.X:PS)^2*PowerSeries.derivative ℝ (coordinate a))=0 := by simp
  rw [hx,sub_zero,PowerSeries.coeff_derivative] at hh
  have hsq : PowerSeries.coeff 0 ((coordinate a)^2)=0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply] at hz ⊢
    rw [map_pow,hz]
    norm_num
  simpa [hsq] using hh

open Real Filter
open scoped Topology

/-- The coefficient sequence in the paper, a_(2n+1), at real degree p. -/
def oddCoefficient (p : ℝ) (n : ℕ) := PowerSeries.coeff (2*n+1) (coordinate (1/p))

/-- The full series is identified with the actual analytic function near zero. -/
theorem paper_represents (p : ℝ) :
    V14ScalarSeries.Represents (coordinate (1/p)) (fun y => tanh (artanh y/p)) := by
  rw [V14ScalarSeries.represents_iff]
  have hh := (V14ScalarSeries.represents_iff _ _).mp (V14ScalarSeries.coordinate_represents (1/p))
  filter_upwards [hh,Ioo_mem_nhds (by norm_num : (-1:ℝ)<0) (by norm_num : (0:ℝ)<1)] with y hy hcell
  have he := V14CompressedAnalytic.root_coordinate_formula (1/p) y hcell
  unfold V14CompressedAnalytic.rootCoordinate at he
  rw [he] at hy
  simpa only [one_div_mul_eq_div] using hy

/-- The odd series alone converges to F_p near zero. -/
theorem paper_hasSum (p : ℝ) :
    ∀ᶠ y : ℝ in 𝓝 0, HasSum (fun n => oddCoefficient p n*y^(2*n+1)) (tanh (artanh y/p)) := by
  have hh := (V14ScalarSeries.represents_iff _ _).mp (paper_represents p)
  filter_upwards [hh] with y hy
  have ho := hy.summable.comp_injective (i := fun n : ℕ => 2*n+1) (by intro i j h; dsimp at h; omega)
  have he : HasSum (fun n => PowerSeries.coeff (2*n) (coordinate (1/p))*y^(2*n)) 0 := by
    simpa only [even_coordinate_coeff,zero_mul] using (hasSum_zero : HasSum (fun _ : ℕ => (0:ℝ)) 0)
  have hv := hy.unique (HasSum.even_add_odd (f := fun n => PowerSeries.coeff n (coordinate (1/p))*y^n) he ho.hasSum)
  simp only [zero_add] at hv
  rw [hv]
  exact ho.hasSum

theorem paper_initial (p : ℝ) : oddCoefficient p 0=1/p := by
  exact first_coefficient (1/p)

/-- The printed recurrence with j=n+1 (hence j≥1), for arbitrary real p. -/
theorem paper_recurrence (p : ℝ) (n : ℕ) :
    (2*(n:ℝ)+3)*oddCoefficient p (n+1)=
      (2*(n:ℝ)+1)*oddCoefficient p n-
        (1/p)*∑ k ∈ Finset.range (n+1), oddCoefficient p k*oddCoefficient p (n-k) := by
  simpa only [oddCoefficient,show 2*(n+1)+1=2*n+3 by omega] using odd_recurrence (1/p) n

/-- The recurrence in exactly the manuscript's indexing, for n ≥ 1. -/
theorem paper_recurrence_indexed (p : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    (2*(n:ℝ)+1)*oddCoefficient p n =
      (2*(n:ℝ)-1)*oddCoefficient p (n-1) -
        (1/p)*∑ k ∈ Finset.range n, oddCoefficient p k*oddCoefficient p (n-1-k) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one,
    show ∀ x : ℝ, 2*(x+1)+1=2*x+3 by intro x; ring,
    show ∀ x : ℝ, 2*(x+1)-1=2*x+1 by intro x; ring] using paper_recurrence p j

/-- The first two nontrivial coefficients printed after the recurrence. -/
theorem paper_low_coefficients (p : ℝ) (hp : p ≠ 0) :
    oddCoefficient p 1=(p^2-1)/(3*p^3) ∧
    oddCoefficient p 2=(p^2-1)*(3*p^2-2)/(15*p^5) := by
  have h₁ := paper_recurrence p 0
  have h₂ := paper_recurrence p 1
  norm_num [Finset.sum_range_succ, paper_initial] at h₁ h₂
  have hc : oddCoefficient p 1=(p^2-1)/(3*p^3) := by
    field_simp [hp] at h₁ ⊢
    nlinarith
  constructor
  · exact hc
  · rw [hc] at h₂
    field_simp [hp] at h₂ ⊢
    nlinarith

end LeanMath.Papers.V14SeriesRecurrence
