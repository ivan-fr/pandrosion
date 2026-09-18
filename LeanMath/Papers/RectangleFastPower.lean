import LeanMath.Papers.RectangleNewton
import LeanMath.Papers.RectangleProjective
import LeanMath.Papers.RectangleDecenteredArc
import Mathlib.Data.Nat.BinaryRec

/-! Post-V20 experiment. Affine certificates for the homogeneous gallery engine.
The binary recursion is evaluated from the most significant bit, with no root oracle.
No floating-point conditioning or adaptive-optimality theorem is asserted. -/
noncomputable section
namespace LeanMath.Papers.RectangleFastPower
open RectangleGeometry

def R (W H q : ℝ) : Point := (W, H*(1-q))
def Xtop (W H q : ℝ) : Point := (W+H*q,H)
def unit (W H : ℝ) : Point := (W+H,H)
def transfer (W H : ℝ) := join (unit W H) (W,0)
def multiplier (W H a b : ℝ) := parallel (join (unit W H) (R W H b)) (Xtop W H a)

theorem copy_incidence (W H q : ℝ) :
    On (parallel (transfer W H) (R W H q)) (Xtop W H q) ∧
    On (horizontal H) (Xtop W H q) := by
  constructor <;> dsimp [On,parallel,transfer,join,unit,R,Xtop,horizontal] <;> ring

theorem copy_unique (W H q : ℝ) (hH : H ≠ 0) :
    meet (parallel (transfer W H) (R W H q)) (horizontal H) = Xtop W H q := by
  apply intersection_unique _ _ _ _ _ (meet_on _ _ _) (copy_incidence W H q)
  all_goals simpa [parallel,transfer,join,unit,horizontal] using hH

theorem fastPower_mul_incidence (W H a b : ℝ) :
    On (multiplier W H a b) (R W H (a*b)) ∧ On (vertical W) (R W H (a*b)) := by
  constructor <;> dsimp [On,multiplier,parallel,join,unit,R,Xtop,vertical] <;> ring

theorem multiplier_transverse (W H a b : ℝ) (hH : H ≠ 0) :
    (multiplier W H a b).a*(vertical W).b - (vertical W).a*(multiplier W H a b).b ≠ 0 := by
  simpa [multiplier,parallel,join,unit,R,vertical] using hH

theorem rectangle_mul_readout (W H a b : ℝ) (hH : H ≠ 0) :
    meet (multiplier W H a b) (vertical W) = R W H (a*b) := by
  exact intersection_unique _ _ (multiplier_transverse W H a b hH) _ _
    (meet_on _ _ (multiplier_transverse W H a b hH)) (fastPower_mul_incidence W H a b)

theorem join_distinct (W H b : ℝ) (hH : H ≠ 0) : unit W H ≠ R W H b := by
  intro h
  have := congrArg Prod.fst h
  dsimp [unit,R] at this
  exact hH (by linarith)

-- Descending to n/2 and unwinding is left-to-right binary exponentiation.
def binaryPower (s : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 1 else if n = 1 then s else
    (binaryPower s (n/2))^2 * s^(n%2)
termination_by n

theorem binaryPower_eq (s : ℝ) (n : ℕ) : binaryPower s n = s^n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [binaryPower]
    split_ifs with h0 h1
    · simp [h0]
    · simp [h1]
    · rw [ih (n/2) (Nat.div_lt_self (by omega) (by omega)), ← pow_mul, ← pow_add]
      congr 1
      omega

theorem final_E (W H s : ℝ) (p : ℕ) : R W H (binaryPower s p) = R W H (s^p) := by
  rw [binaryPower_eq]

theorem binary_stage (W H s : ℝ) (n : ℕ) (hH : H ≠ 0) :
    meet (multiplier W H (binaryPower s n) (binaryPower s n)) (vertical W) = R W H (s^(2*n)) := by
  rw [rectangle_mul_readout W H _ _ hH, binaryPower_eq]
  congr 1
  rw [pow_mul, pow_two]
  ring

-- The geometric recursion performs rail intersections, not a scalar power call.
def readout (H : ℝ) (P : Point) := 1-P.2/H
def geometricMul (W H : ℝ) (P Q : Point) : Point :=
  let T := meet (parallel (transfer W H) P) (horizontal H)
  meet (parallel (join (unit W H) Q) T) (vertical W)

theorem readout_R (W H a : ℝ) (hH : H ≠ 0) : readout H (R W H a) = a := by
  dsimp [readout,R]; field_simp; ring

theorem geometricMul_R (W H a b : ℝ) (hH : H ≠ 0) :
    geometricMul W H (R W H a) (R W H b) = R W H (a*b) := by
  dsimp [geometricMul]
  rw [copy_unique W H a hH]
  exact rectangle_mul_readout W H a b hH

def geometricPower (W H s : ℝ) (n : ℕ) : Point :=
  if n = 0 then R W H 1 else if n = 1 then R W H s else
    let Q := geometricPower W H s (n/2)
    let Q₂ := geometricMul W H Q Q
    if n%2 = 0 then Q₂ else geometricMul W H (R W H s) Q₂
termination_by n

theorem geometricPower_eq (W H s : ℝ) (n : ℕ) (hH : H ≠ 0) :
    geometricPower W H s n = R W H (s^n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [geometricPower]
    by_cases h0 : n = 0
    · simp [h0]
    rw [if_neg h0]
    by_cases h1 : n = 1
    · simp [h1]
    rw [if_neg h1, ih (n/2) (Nat.div_lt_self (by omega) (by omega))]
    dsimp only
    rw [geometricMul_R W H _ _ hH]
    split_ifs with he
    · congr 1
      rw [← pow_add]
      congr 1
      omega
    · rw [geometricMul_R W H _ _ hH, ← pow_add, ← pow_succ']
      have hn : n/2+n/2+1=n := by omega
      rw [hn]

theorem geometric_readout (W H s : ℝ) (n : ℕ) (hH : H ≠ 0) :
    readout H (geometricPower W H s n) = s^n := by
  rw [geometricPower_eq W H s n hH, readout_R W H _ hH]

def mulCount (n : ℕ) : ℕ := if n ≤ 1 then 0 else mulCount (n/2)+1+n%2
termination_by n

theorem count_log_bound (n : ℕ) : mulCount n ≤ 2*n.log2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [mulCount]
    split_ifs with h
    · omega
    · have hn : n/2 < n := Nat.div_lt_self (by omega) (by omega)
      have hi := ih (n/2) hn
      have hl : n.log2 = (n/2).log2+1 := by
        have hh := Nat.log2_eq_succ_log2_shiftRight (n := n) (by simpa [Nat.shiftRight_eq_div_pow] using (show n/2 ≠ 0 by omega))
        simpa [Nat.shiftRight_eq_div_pow] using hh
      have hm := Nat.mod_lt n (by omega : 0<2)
      omega

theorem count_power_two (k : ℕ) : mulCount (2^k) = k := by
  induction k with
  | zero => rw [show 2^0 = 1 by rfl, mulCount]; norm_num
  | succ k ih =>
    have hp : 0 < 2^k := by positivity
    have hd : 2^(k+1)/2 = 2^k := by rw [pow_succ]; omega
    have hm : 2^(k+1)%2 = 0 := by rw [pow_succ]; omega
    rw [mulCount, if_neg (by rw [pow_succ]; omega), hd, hm, ih]

-- Support substitution: all corrections consume exactly the same E coordinate.
def fastAK (p : ℕ) (X s : ℝ) := (p:ℝ)*s/((p:ℝ)-1+X*binaryPower s p)
def fastAD (p : ℕ) (X s : ℝ) := s*((p:ℝ)+1+((p:ℝ)-1)*X*binaryPower s p)/((p:ℝ)-1+((p:ℝ)+1)*X*binaryPower s p)
def fastProjective (p : ℕ) (X s : ℝ) := s*RectangleProjective.num p (X*binaryPower s p)/RectangleProjective.den p (X*binaryPower s p)
def arcSupport (p : ℕ) (s t : ℝ) := let g := ((p:ℝ)-1)*Real.sqrt (RectangleDecenteredArc.rad p t); s*(1+g)/(t+g)
def fastArc (p : ℕ) (X s : ℝ) := arcSupport p s (X*binaryPower s p)

theorem fastAK_eq (p : ℕ) (X s : ℝ) : fastAK p X s = RectangleReports.ak p X s := by simp [fastAK,binaryPower_eq,RectangleReports.ak]
theorem fastAD_eq (p : ℕ) (X s : ℝ) : fastAD p X s = RectangleReports.ad p X s := by simp [fastAD,binaryPower_eq,RectangleReports.ad]
theorem fastProjective_eq (p : ℕ) (X s : ℝ) : fastProjective p X s = RectangleProjective.step p X s := by simp [fastProjective,binaryPower_eq,RectangleProjective.step]
theorem fastArc_eq (p : ℕ) (X s : ℝ) : fastArc p X s = arcSupport p s (X*s^p) := by simp [fastArc,binaryPower_eq]

open Filter Function
open scoped Topology

theorem fastAK_converges (p : ℕ) (X s : ℝ) (hp : 2≤p) (hX : 0<X) (hs : 0<s) :
    Tendsto (fun n : ℕ => (fastAK p X)^[n] s) atTop (𝓝 (X⁻¹ ^ (1/(p:ℝ)))) := by
  have h : fastAK p X = RectangleReports.ak p X := funext (fastAK_eq p X)
  rw [h]; exact RectangleNewton.ak_global_convergence p X s hp hX hs

theorem fastAD_converges (p : ℕ) (X s : ℝ) (hp : 2≤p) (hX : 0<X) (hs : 0<s) :
    Tendsto (fun n : ℕ => (fastAD p X)^[n] s) atTop (𝓝 (X⁻¹ ^ (1/(p:ℝ)))) := by
  have h : fastAD p X = RectangleReports.ad p X := funext (fastAD_eq p X)
  rw [h]; exact RectangleDynamics.ad_global_convergence p X s hp hX hs

theorem fastProjective_converges (p : ℕ) (X s : ℝ) (hp : 2≤p) (hX : 0<X) (hs : 0<s) :
    Tendsto (fun n : ℕ => (fastProjective p X)^[n] s) atTop (𝓝 (X⁻¹ ^ (1/(p:ℝ)))) := by
  have h : fastProjective p X = RectangleProjective.step p X := funext (fastProjective_eq p X)
  rw [h]; exact RectangleProjective.global_convergence p X s hp hX hs
end LeanMath.Papers.RectangleFastPower
