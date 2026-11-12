import LeanMath.Papers.NestedRadicalReal

/-! Extension to every nonzero real degree by dyadic degree doubling and,
for negative degrees, inversion of the readout. The raw radical formula
is used only at degrees greater than two. -/
noncomputable section
namespace LeanMath.Papers.NestedRadicalAllDegrees
open Real Filter Function
open scoped Topology
open LeanMath.Papers.NestedRadicalReal
set_option maxHeartbeats 1000000

def degree (p : ℝ) (k : ℕ) : ℝ := |p| * ((2^k:ℕ):ℝ)

theorem exists_doubling (p : ℝ) (hp : p≠0) : ∃ k : ℕ, 2<degree p k := by
  have ha : 0 < |p| := abs_pos.mpr hp
  obtain ⟨n,hn⟩ := exists_nat_gt (2/|p|)
  have hpow : (n:ℝ)<((2^n:ℕ):ℝ) := by exact_mod_cast (Nat.lt_two_pow_self (n:=n))
  have hbase : 2 < |p| * (n:ℝ) := by
    have h := (div_lt_iff₀ ha).mp hn
    nlinarith
  exact ⟨n,hbase.trans (mul_lt_mul_of_pos_left hpow ha)⟩

def doublings (p : ℝ) (hp : p≠0) : ℕ := Nat.find (exists_doubling p hp)

theorem degree_doublings (p : ℝ) (hp : p≠0) : 2<degree p (doublings p hp) :=
  Nat.find_spec (exists_doubling p hp)

def output (p : ℝ) (k : ℕ) (v : ℝ) : ℝ :=
  if 0<p then v^(2^k) else (v^(2^k))⁻¹
def orbit (p : ℝ) (k : ℕ) (X v : ℝ) (n : ℕ) : ℝ :=
  output p k ((step (degree p k) X)^[n] v)

theorem limit_power (p X : ℝ) (k : ℕ) (hp : p≠0) (hX : 0<X) :
    (X^(1/degree p k))^(2^k)=X^(1/|p|) := by
  have ha : |p|≠0 := (abs_pos.mpr hp).ne'
  have hn : (((2^k:ℕ):ℝ))≠0 := by positivity
  rw [←Real.rpow_natCast,←Real.rpow_mul hX.le]
  congr 1
  unfold degree
  field_simp

/-- Every positive internal starting value converges for every nonzero degree. -/
theorem global_orbit (p X v : ℝ) (k : ℕ) (hp : p≠0)
    (hdegree : 2<degree p k) (hX : 0<X) (hv : 0<v) :
    Tendsto (orbit p k X v) atTop (𝓝 (X^(1/p))) := by
  have hb := (NestedRadicalReal.global_convergence (degree p k) X v hdegree hX hv).pow (2^k)
  rw [limit_power p X k hp hX] at hb
  rcases hp.lt_or_gt with hpneg | hppos
  · have hnot : ¬0<p := by linarith
    have hi := hb.inv₀ (Real.rpow_pos_of_pos hX (1/|p|)).ne'
    have he : (X^(1/|p|))⁻¹=X^(1/p) := by
      rw [abs_of_neg hpneg,←Real.rpow_neg hX.le]
      congr 1
      field_simp
    rw [he] at hi
    convert hi using 1
    funext n
    simp [orbit, output, hnot]
  · rw [abs_of_pos hppos] at hb
    convert hb using 1
    funext n
    simp [orbit, output, hppos]

/-- Initial internal value obtained using k successive square roots. -/
def start (p : ℝ) (k : ℕ) (u : ℝ) : ℝ :=
  (if 0<p then u else u⁻¹)^(1/(((2^k:ℕ):ℝ)))
def method (p : ℝ) (k : ℕ) (X u : ℝ) (n : ℕ) : ℝ :=
  orbit p k X (start p k u) n

theorem start_positive (p u : ℝ) (k : ℕ) (hu : 0<u) : 0<start p k u := by
  unfold start
  apply Real.rpow_pos_of_pos
  split_ifs <;> positivity

theorem method_zero (p X u : ℝ) (k : ℕ) (hu : 0<u) : method p k X u 0=u := by
  have hn : (2^k:ℕ)≠0 := by positivity
  have hpwr (y : ℝ) (hy : 0<y) : (y^(1/(((2^k:ℕ):ℝ))))^(2^k)=y := by
    rw [one_div]
    exact Real.rpow_inv_natCast_pow hy.le hn
  unfold method orbit output start
  simp only [iterate_zero, id_eq]
  split_ifs with h
  · exact hpwr u hu
  · rw [hpwr u⁻¹ (by positivity)]
    simp

/-- The extended algorithm starts at the prescribed u0 and converges globally. -/
theorem global_method (p X u : ℝ) (k : ℕ) (hp : p≠0)
    (hdegree : 2<degree p k) (hX : 0<X) (hu : 0<u) :
    Tendsto (method p k X u) atTop (𝓝 (X^(1/p))) := by
  exact global_orbit p X (start p k u) k hp hdegree hX (start_positive p u k hu)

/-- Universal statement: every real p!=0, every X>0 and every prescribed u0>0. -/
theorem global_all_nonzero (p X u : ℝ) (hp : p≠0) (hX : 0<X) (hu : 0<u) :
    Tendsto (method p (doublings p hp) X u) atTop (𝓝 (X^(1/p))) := by
  exact global_method p X u (doublings p hp) hp (degree_doublings p hp) hX hu

end LeanMath.Papers.NestedRadicalAllDegrees
