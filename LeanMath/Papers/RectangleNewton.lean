import LeanMath.Papers.RectangleDynamics
import LeanMath.Papers.IntervalIteration
import LeanMath.Papers.Bracket

noncomputable section
namespace LeanMath.Papers.RectangleNewton
open LeanMath.Papers.RectangleReports LeanMath.Papers.RectangleRaw
open LeanMath.Papers Filter Set Function
open scoped Topology

theorem ak_pos (p : ℕ) (X s : ℝ) (hp : 2≤p) (hX : 0<X) (hs : 0<s) : 0<ak p X s := by
  have hp' : (0:ℝ)<p := by exact_mod_cast (show 0<p by omega)
  exact div_pos (mul_pos hp' hs) (denominators_pos p X s hp hX hs).1

theorem ak_one (p : ℕ) (hp : 2≤p) : ak p 1 1=1 := by
  have hp' : (p:ℝ)≠0 := by exact_mod_cast (show p≠0 by omega)
  simp [ak,hp']

theorem ak_unit_bound (p : ℕ) (s : ℝ) (hp : 2≤p) (hs : 0<s) : ak p 1 s≤1 := by
  apply (div_le_one (denominators_pos p 1 s hp (by norm_num) hs).1).mpr
  have ht := Bracket.power_tangent p s hs
  simp only [one_mul]
  linarith

theorem ak_unit_increases (p : ℕ) (s : ℝ) (hp : 2≤p) (hs : 0<s) (hs1 : s<1) : s<ak p 1 s := by
  have hpow : s^p<1 := pow_lt_one₀ hs.le hs1 (by omega)
  apply (lt_div_iff₀ (denominators_pos p 1 s hp (by norm_num) hs).1).mpr
  nlinarith [mul_pos hs (sub_pos.mpr hpow)]

theorem ak_unit_global (p : ℕ) (s : ℝ) (hp : 2≤p) (hs : 0<s) :
    Tendsto (fun n : ℕ => (ak p 1)^[n] s) atTop (𝓝 1) := by
  let b := ak p 1 s
  have hb : 0<b := ak_pos p 1 s hp (by norm_num) hs
  have hb1 : b≤1 := ak_unit_bound p s hp hs
  have ht : Tendsto (fun n : ℕ => (ak p 1)^[n] b) atTop (𝓝 1) := by
    apply IntervalIteration.converge (ak p 1) b 1 1 b ⟨hb1,le_rfl⟩ ⟨le_rfl,hb1⟩
    · intro t hmem
      have hd := (denominators_pos p 1 t hp (by norm_num) (hb.trans_le hmem.1)).1.ne'
      unfold ak; fun_prop
    · exact ak_one p hp
    · intro t hmem ht
      exact ⟨ak_unit_increases p t hp (hb.trans_le hmem.1) ht,
        ak_unit_bound p t hp (hb.trans_le hmem.1)⟩
    · intro t hmem ht; exact False.elim (not_lt_of_ge hmem.2 ht)
  have he : (fun n : ℕ => (ak p 1)^[n+1] s)=(fun n : ℕ => (ak p 1)^[n] b) := by
    funext n; rw [iterate_succ_apply]
  exact (tendsto_add_atTop_iff_nat 1).mp (by rwa [he])

theorem ak_scale (p : ℕ) (X a t : ℝ) (ha : X*a^p=1) : ak p X (a*t)=a*ak p 1 t := by
  unfold ak; rw [mul_pow]
  have h : X*(a^p*t^p)=t^p := by rw [← mul_assoc,ha,one_mul]
  rw [h]; ring

theorem ak_global_with_root (p : ℕ) (X a s : ℝ) (hp : 2≤p)
    (ha : 0<a) (hs : 0<s) (hroot : X*a^p=1) :
    Tendsto (fun n : ℕ => (ak p X)^[n] s) atTop (𝓝 a) := by
  have he : ∀ n : ℕ, (ak p X)^[n] s=a*(ak p 1)^[n] (s/a) := by
    intro n; induction n with
    | zero => change s=a*(s/a); field_simp
    | succ n ih => rw [iterate_succ_apply',iterate_succ_apply',ih,ak_scale p X a _ hroot]
  have ht := (ak_unit_global p (s/a) hp (div_pos hs ha)).const_mul a
  simpa only [← he,mul_one] using ht

theorem ak_global_convergence (p : ℕ) (X s : ℝ) (hp : 2≤p) (hX : 0<X) (hs : 0<s) :
    Tendsto (fun n : ℕ => (ak p X)^[n] s) atTop (𝓝 (X⁻¹ ^ (1/(p:ℝ)))) := by
  have hp0 : (p:ℝ)≠0 := by exact_mod_cast (show p≠0 by omega)
  apply ak_global_with_root p X _ s hp (Real.rpow_pos_of_pos (inv_pos.mpr hX) _) hs
  rw [← Real.rpow_natCast,one_div,Real.rpow_inv_rpow (inv_nonneg.mpr hX.le) hp0,
    mul_inv_cancel₀ hX.ne']

theorem hasDerivAt_ak (p : ℕ) (X s : ℝ) (hp : 2≤p)
    (hd : (p:ℝ)-1+X*s^p≠0) :
    HasDerivAt (ak p X) ((p:ℝ)*((p:ℝ)-1)*(1-X*s^p)/((p:ℝ)-1+X*s^p)^2) s := by
  have hpow : s*s^(p-1)=s^p := by rw [← pow_succ']; congr 1; omega
  have h := ((hasDerivAt_id s).const_mul (p:ℝ)).div
    ((((hasDerivAt_id s).pow p).const_mul X).const_add ((p:ℝ)-1)) hd
  convert! h using 1
  simp only [id_eq,mul_one,Pi.pow_apply,Pi.mul_apply]
  field_simp [hd]
  rw [← hpow]; ring

def akFactor (p : ℕ) (e : ℝ) :=
  -(p:ℝ)*((p:ℝ)-1)*sumPowers p (1+e)/((p:ℝ)-1+(1+e)^p)^2

theorem ak_order_two (p : ℕ) (hp : 2≤p) :
    Tendsto (fun e : ℝ => (ak p 1 (1+e)-1)/e^2) (𝓝[≠] 0) (𝓝 (-((p:ℝ)-1)/2)) := by
  have hp' : (2:ℝ)≤p := by exact_mod_cast hp
  have hp0 : (p:ℝ)≠0 := by linarith
  have hd0 : (p:ℝ)-1+(1+(0:ℝ))^p≠0 := by
    simp only [add_zero,one_pow,sub_add_cancel]
    exact hp0
  have hf0 : ak p 1 (1+0)-1=0 := by simp [ak_one p hp]
  have hc : ContinuousAt (fun e : ℝ => ak p 1 (1+e)-1) 0 := by
    unfold ak
    apply ContinuousAt.sub _ continuousAt_const
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · simpa using hd0
  have hg : ContinuousAt (akFactor p) 0 := by
    unfold akFactor sumPowers
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · exact pow_ne_zero _ hd0
  have hh : ∀ᶠ e : ℝ in 𝓝[≠] 0,
      HasDerivAt (fun e : ℝ => ak p 1 (1+e)-1) (e^1*akFactor p e) e := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (show (-1:ℝ)<0 by norm_num))] with e he
    have hpos : 0<1+e := by have : -1<e := he; linarith
    have hd := (denominators_pos p 1 (1+e) hp (by norm_num) hpos).1.ne'
    have hd' := ((hasDerivAt_ak p 1 (1+e) hp hd).comp e ((hasDerivAt_id e).const_add 1)).sub_const 1
    convert! hd' using 1
    simp only [one_mul,mul_one,pow_one]
    have hi := sum_identity p (1+e)
    have hi' : 1-(1+e)^p= -e*sumPowers p (1+e) := by nlinarith [hi]
    rw [hi']; unfold akFactor; ring
  have ht := LocalOrder.from_derivative 1 (fun e : ℝ => ak p 1 (1+e)-1) (akFactor p) hf0 hc hg hh
  have hv : akFactor p 0/((1:ℝ)+1)= -((p:ℝ)-1)/2 := by
    simp [akFactor,sumPowers]; field_simp [hp0] <;> ring
  simpa only [Nat.reduceAdd,Nat.cast_one,Nat.cast_ofNat,hv] using ht
theorem ak_relative_order_two (p : ℕ) (X a : ℝ) (hp : 2≤p)
    (ha : 0<a) (hroot : X*a^p=1) :
    Tendsto (fun e : ℝ => (ak p X (a*(1+e))/a-1)/e^2) (𝓝[≠] 0)
      (𝓝 (-((p:ℝ)-1)/2)) := by
  simpa only [ak_scale p X a _ hroot,mul_div_cancel_left₀ _ ha.ne'] using ak_order_two p hp

end LeanMath.Papers.RectangleNewton
