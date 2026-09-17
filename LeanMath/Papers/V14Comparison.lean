import LeanMath.Papers.V14Coefficients
import LeanMath.Papers.V14Defect
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Uniform differential comparison for the ninth-degree defect polynomial. -/
noncomputable section
namespace LeanMath.Papers.V14Comparison
open Real Set
open LeanMath.Papers.V14Coefficients LeanMath.Papers.Cayley

def tail (t : ℝ) := (1012/175)*t+(2416/945)*t^2+(4756/2205)*t^3+
  (32/21)*t^4+(64/81)*t^5

theorem tail_bound (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 1/16) : tail t < 3/8 := by
  have h : tail t ≤ tail (1/16) := by unfold tail; gcongr
  have hb : tail (1/16) < 3/8 := by norm_num [tail]
  exact h.trans_lt hb

theorem differential_defect_negative (a y : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (hy0 : 0 < y) (hy : y ≤ 1/4) :
    (1-y^2)*(1-a^2*y^2)*Q9prime a y-c a*y^2*(1-(Q9 a y)^2) < 0 := by
  obtain ⟨hc0,_,_⟩ := c_bounds a ha0 ha1
  obtain ⟨h3,h3b,h5,h5b,h7,h7b⟩ := first_coefficients a ha0 ha1
  obtain ⟨h9,h9b,h9c⟩ := q9_bounds a ha0 ha1
  have h11 := (q11_lower a ha0 ha1).1
  have ha2 : a^2 ≤ 1 := (powers_bounds a ha0 ha1).1.le
  have ha9 : 9*a^2*q9 a ≤ 4*c a := by
    have hh : a^2*q9 a ≤ 1*q9 a := mul_le_mul_of_nonneg_right ha2 h9.le
    nlinarith
  have hA : 9*a^2*q9 a+c a*(2*q3 a*q7 a+(q5 a)^2) ≤ c a*(1012/175) := by
    have hh : 2*q3 a*q7 a+(q5 a)^2 ≤ 2*(2/3)*(6/7)+(4/5)^2 := by gcongr
    nlinarith
  have hB : 2*q3 a*q9 a+2*q5 a*q7 a ≤ (2416/945:ℝ) := by
    calc
      _ ≤ (2:ℝ)*(2/3)*(8/9)+2*(4/5)*(6/7) := by gcongr
      _ = _ := by norm_num
  have hC : 2*q5 a*q9 a+(q7 a)^2 ≤ (4756/2205:ℝ) := by
    calc
      _ ≤ (2:ℝ)*(4/5)*(8/9)+(6/7)^2 := by gcongr
      _ = _ := by norm_num
  have hD : 2*q7 a*q9 a ≤ (32/21:ℝ) := by
    calc
      _ ≤ (2:ℝ)*(6/7)*(8/9) := by gcongr
      _ = _ := by norm_num
  have hE : (q9 a)^2 ≤ (64/81:ℝ) := by
    calc
      _ ≤ (8/9:ℝ)^2 := by gcongr
      _ = _ := by norm_num
  rw [differential_defect_identity]
  have hmain :
      -11*q11 a*y^10+(9*a^2*q9 a+c a*(2*q3 a*q7 a+(q5 a)^2))*y^12+
      c a*(2*q3 a*q9 a+2*q5 a*q7 a)*y^14+
      c a*(2*q5 a*q9 a+(q7 a)^2)*y^16+2*c a*q7 a*q9 a*y^18+
      c a*(q9 a)^2*y^20 ≤
      -c a*y^10+c a*(1012/175)*y^12+c a*(2416/945)*y^14+
      c a*(4756/2205)*y^16+c a*(32/21)*y^18+c a*(64/81)*y^20 := by
    have h0 : -11*q11 a*y^10 ≤ -c a*y^10 := by
      have := mul_le_mul_of_nonneg_right h11 (pow_nonneg hy0.le 10)
      nlinarith
    have h1 := mul_le_mul_of_nonneg_right hA (pow_nonneg hy0.le 12)
    have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB hc0.le) (pow_nonneg hy0.le 14)
    have h3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC hc0.le) (pow_nonneg hy0.le 16)
    have h4 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD hc0.le) (pow_nonneg hy0.le 18)
    have h5 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE hc0.le) (pow_nonneg hy0.le 20)
    nlinarith
  have hid : -c a*y^10+c a*(1012/175)*y^12+c a*(2416/945)*y^14+
      c a*(4756/2205)*y^16+c a*(32/21)*y^18+c a*(64/81)*y^20 =
      c a*y^10*(-1+tail (y^2)) := by unfold tail; ring
  rw [hid] at hmain
  have ht := tail_bound (y^2) (sq_nonneg y) (by nlinarith)
  exact hmain.trans_lt (mul_neg_of_pos_of_neg (by positivity) (by linarith))

/-- A bound keeping the polynomial away from the Cayley pole. -/
theorem Q9_mem (a y : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (hy : |y| ≤ 1/4) : Q9 a y ∈ Ioo (-1) 1 := by
  obtain ⟨h3,h3b,h5,h5b,h7,h7b⟩ := first_coefficients a ha0 ha1
  obtain ⟨h9,h9b,_⟩ := q9_bounds a ha0 ha1
  have hpos : ∀ t : ℝ, 0 ≤ t → t ≤ 1/4 → 0 ≤ Q9 a t ∧ Q9 a t < 1 := by
    intro t ht0 ht1
    have ht : t ≤ 1 := by linarith
    have h5t : t^5 ≤ t := pow_le_of_le_one ht0 ht (by decide : 5 ≠ 0)
    have h7t : t^7 ≤ t := pow_le_of_le_one ht0 ht (by decide : 7 ≠ 0)
    have h9t : t^9 ≤ t := pow_le_of_le_one ht0 ht (by decide : 9 ≠ 0)
    have h3t : t^3 ≤ t := pow_le_of_le_one ht0 ht (by decide : 3 ≠ 0)
    have hQ : Q9 a t ≤ (2/3+4/5+6/7+8/9)*t := by
      unfold Q9 Q7 Q5 Q3
      have hh : q3 a*t^3+q5 a*t^5+q7 a*t^7+q9 a*t^9 ≤
          (2/3)*t+(4/5)*t+(6/7)*t+(8/9)*t := by gcongr
      nlinarith
    constructor
    · unfold Q9 Q7 Q5 Q3; positivity
    · nlinarith
  have h := hpos |y| (abs_nonneg y) hy
  by_cases hy0 : 0 ≤ y
  · rw [abs_of_nonneg hy0] at h
    exact ⟨by linarith [h.1],h.2⟩
  · rw [abs_of_nonpos (le_of_not_ge hy0),Q9_odd] at h
    exact ⟨by linarith [h.2],by linarith [h.1]⟩


def delta (a y : ℝ) := (1+a)/(2*(1-a))*(a*logCoord y-logCoord (a*y))
def logGap (a y : ℝ) := logCoord (Q9 a y)-delta a y

theorem scaled_mem (a y : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (hy : y ∈ Ioo (-1) 1) : a*y ∈ Ioo (-1) 1 := by
  apply abs_lt.mp
  rw [abs_mul,abs_of_pos ha0]
  have h := mul_le_mul_of_nonneg_left (abs_lt.mpr hy).le ha0.le
  nlinarith

/-- Links the a-parameterized analysis to the geometric defect of §9. -/
theorem delta_eq_defect (p y : ℝ) (hp : 2 < p) (hy : y ∈ Ioo (-1) 1) :
    delta (V14Defect.a p) y = V14Defect.defect p y := by
  rw [V14Defect.exact_defect_identity p y hp hy]
  unfold delta
  rw [logCoord_eq y hy,V14Defect.log_unchi y hy,
    logCoord_eq _ (V14Defect.scaled_mem p y hp hy),
    V14Defect.log_unchi _ (V14Defect.scaled_mem p y hp hy)]
  have hp0 : p ≠ 0 := by linarith
  have ha1 : 1-V14Defect.a p ≠ 0 := by linarith [(V14Defect.a_mem p hp).2]
  unfold V14Defect.a at *
  field_simp
  <;> ring

theorem hasDerivAt_delta (a y : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (hy : y ∈ Ioo (-1) 1) :
    HasDerivAt (delta a) (2*c a*y^2/((1-y^2)*(1-a^2*y^2))) y := by
  have hay := scaled_mem a y ha0 ha1 hy
  have hd : 1-y^2 ≠ 0 := by nlinarith [hy.1,hy.2]
  have hd' : 1-(a*y)^2 ≠ 0 := by nlinarith [hay.1,hay.2]
  have haa : 1-a ≠ 0 := by linarith
  convert! (((hasDerivAt_logCoord y hy).const_mul a).sub
    ((hasDerivAt_logCoord (a*y) hay).comp y ((hasDerivAt_id y).const_mul a))).const_mul
    ((1+a)/(2*(1-a))) using 1
  unfold c
  have he : 1-a^2*y^2 = 1-(a*y)^2 := by ring
  rw [he]
  have hd2 : 1-a^2*y^2 ≠ 0 := by nlinarith [hay.1,hay.2]
  have hd3 : 1-y^2*a^2 ≠ 0 := by nlinarith [hay.1,hay.2]
  field_simp [hd2,hd3]
  <;> ring

theorem hasDerivAt_Q9 (a y : ℝ) : HasDerivAt (Q9 a) (Q9prime a y) y := by
  convert! (((((hasDerivAt_id y).pow 3).const_mul (q3 a)).add
    (((hasDerivAt_id y).pow 5).const_mul (q5 a))).add
    (((hasDerivAt_id y).pow 7).const_mul (q7 a))).add
    (((hasDerivAt_id y).pow 9).const_mul (q9 a)) using 1
  simp only [Q9prime,id_eq,Nat.reduceSub,Nat.cast_ofNat,mul_one]
  ring

theorem hasDerivAt_logGap (a y : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (hy : |y| ≤ 1/4) :
    HasDerivAt (logGap a)
      (2/ (1-(Q9 a y)^2)*Q9prime a y-2*c a*y^2/((1-y^2)*(1-a^2*y^2))) y := by
  have hm : y ∈ Ioo (-1) 1 := by
    obtain ⟨hl,hu⟩ := abs_le.mp hy
    exact ⟨by linarith,by linarith⟩
  exact ((hasDerivAt_logCoord _ (Q9_mem a y ha0 ha1 hy)).comp y (hasDerivAt_Q9 a y)).sub
    (hasDerivAt_delta a y ha0 ha1 hm)

theorem logGap_deriv_neg (a y : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (hy0 : 0 < y) (hy : y ≤ 1/4) : deriv (logGap a) y < 0 := by
  have hab : |y| ≤ 1/4 := by rwa [abs_of_pos hy0]
  have hm := Q9_mem a y ha0 ha1 hab
  have hQ : 0 < 1-(Q9 a y)^2 := by nlinarith [hm.1,hm.2]
  have hd : 0 < 1-y^2 := by nlinarith
  have hay := scaled_mem a y ha0 ha1 ⟨by linarith,by linarith⟩
  have hd' : 0 < 1-a^2*y^2 := by nlinarith [hay.1,hay.2]
  rw [(hasDerivAt_logGap a y ha0 ha1 hab).deriv]
  have he : 2/(1-(Q9 a y)^2)*Q9prime a y-2*c a*y^2/((1-y^2)*(1-a^2*y^2)) =
      2*((1-y^2)*(1-a^2*y^2)*Q9prime a y-c a*y^2*(1-(Q9 a y)^2))/
        ((1-(Q9 a y)^2)*(1-y^2)*(1-a^2*y^2)) := by
        have hd2 : 1-y^2*a^2 ≠ 0 := by nlinarith [hay.1,hay.2]
        field_simp [hQ.ne',hd.ne',hd'.ne',hd2]
        <;> ring
  rw [he]
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num)
    (differential_defect_negative a y ha0 ha1 hy0 hy)) (by positivity)

/-- The all-points comparison, not an assumption on the uncomputed tail. -/
theorem logarithmic_comparison (a y : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (hy0 : 0 < y) (hy : y ≤ 1/4) : logCoord (Q9 a y) < delta a y := by
  have ha : StrictAntiOn (logGap a) (Icc 0 (1/4)) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 (1/4))
    · intro t ht
      exact (hasDerivAt_logGap a t ha0 ha1
        (by rw [abs_of_nonneg ht.1]; exact ht.2)).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact logGap_deriv_neg a t ha0 ha1 ht.1 ht.2.le
  have hz : logGap a 0 = 0 := by simp [logGap,delta,Q9,Q7,Q5,Q3,logCoord]
  have hh := ha (show (0:ℝ) ∈ Icc 0 (1/4) by norm_num) ⟨hy0.le,hy⟩ hy0
  rw [hz] at hh
  exact sub_neg.mp hh

/-- Lemma 9.4, its difficult final strict inequality. -/
theorem Q9_below_exact_defect (p y : ℝ) (hp : 2 < p)
    (hy0 : 0 < y) (hy : y ≤ 1/4) :
    Q9 (V14Defect.a p) y < V14Defect.defectCoordinate p y := by
  have ha := V14Defect.a_mem p hp
  have hmem : y ∈ Ioo (-1) 1 := ⟨by linarith,by linarith⟩
  have hab : |y| ≤ 1/4 := by rwa [abs_of_pos hy0]
  have hq := Q9_mem _ y ha.1 ha.2 hab
  have h := logarithmic_comparison _ y ha.1 ha.2 hy0 hy
  rw [delta_eq_defect p y hp hmem,logCoord_eq _ hq,V14Defect.log_unchi _ hq] at h
  unfold V14Defect.defectCoordinate
  apply (artanh_lt_artanh_iff hq ⟨neg_one_lt_tanh _,tanh_lt_one _⟩).mp
  rw [artanh_tanh]
  linarith

end LeanMath.Papers.V14Comparison
