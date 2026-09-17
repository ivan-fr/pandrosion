import Mathlib.Tactic

/-! The coefficients and exact polynomial comparison calculation of §9.
The parameter is a=(p-2)/p in (0,1). -/
noncomputable section
namespace LeanMath.Papers.V14Coefficients

def c (a : ℝ) := a*(1+a)^2/2

def d3 (a : ℝ) := c a/3
def d5 (a : ℝ) := c a*(1+a^2)/5
def d7 (a : ℝ) := c a*(1+a^2+a^4)/7
def d9 (a : ℝ) := c a*(1+a^2+a^4+a^6)/9
def d11 (a : ℝ) := c a*(1+a^2+a^4+a^6+a^8)/11

def q3 := d3
def q5 := d5
def q7 := d7
def q9 (a : ℝ) := d9 a - (d3 a)^3/3
def q11 (a : ℝ) := d11 a - (d3 a)^2*d5 a

def Q3 (a y : ℝ) := q3 a*y^3
def Q5 (a y : ℝ) := Q3 a y+q5 a*y^5
def Q7 (a y : ℝ) := Q5 a y+q7 a*y^7
def Q9 (a y : ℝ) := Q7 a y+q9 a*y^9

def Q9prime (a y : ℝ) := 3*q3 a*y^2+5*q5 a*y^4+7*q7 a*y^6+9*q9 a*y^8

theorem c_bounds (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    0 < c a ∧ c a < 2 ∧ c a ≤ 2*a := by
  have hs : (1+a)^2 < 4 := by nlinarith
  have hca : c a ≤ 2*a := by unfold c; nlinarith
  exact ⟨by unfold c; positivity, by linarith, hca⟩

theorem powers_bounds (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    a^2 < 1 ∧ a^4 < 1 ∧ a^6 < 1 ∧ a^8 < 1 := by
  exact ⟨pow_lt_one₀ ha0.le ha1 (by decide), pow_lt_one₀ ha0.le ha1 (by decide),
    pow_lt_one₀ ha0.le ha1 (by decide), pow_lt_one₀ ha0.le ha1 (by decide)⟩

theorem first_coefficients (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    0 < q3 a ∧ q3 a < 2/3 ∧ 0 < q5 a ∧ q5 a < 4/5 ∧
    0 < q7 a ∧ q7 a < 6/7 := by
  obtain ⟨hc0,hc2,_⟩ := c_bounds a ha0 ha1
  obtain ⟨ha2,ha4,_,_⟩ := powers_bounds a ha0 ha1
  have h5 : c a*(1+a^2) < 4 := by nlinarith
  have h7 : c a*(1+a^2+a^4) < 6 := by nlinarith
  unfold q3 q5 q7 d3 d5 d7
  exact ⟨by positivity, by linarith, by positivity, by linarith,
    by positivity, by linarith⟩

theorem q9_bounds (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    0 < q9 a ∧ q9 a < 8/9 ∧ q9 a ≤ 4*c a/9 := by
  obtain ⟨hc0,hc2,_⟩ := c_bounds a ha0 ha1
  obtain ⟨ha2,ha4,ha6,_⟩ := powers_bounds a ha0 ha1
  have hs : (c a)^2 < 4 := by nlinarith
  have hlow : 0 < c a*(9-(c a)^2)/81 := by
    have : 0 < 9-(c a)^2 := by linarith
    positivity
  have hid : q9 a = c a*(9-(c a)^2)/81+c a*(a^2+a^4+a^6)/9 := by
    unfold q9 d9 d3; ring
  have hpos : 0 < q9 a := by rw [hid]; positivity
  have hd : d9 a ≤ 4*c a/9 := by unfold d9; nlinarith
  have hq : q9 a < d9 a := by
    have : 0 < (d3 a)^3/3 := by unfold d3; positivity
    unfold q9; linarith
  exact ⟨hpos, by linarith, hq.le.trans hd⟩

theorem q11_lower_identity (a : ℝ) :
    q11 a = c a * (1/11+(a^2+a^4)/495+(a^6+a^8)/11+
      (4*a^2-(c a)^2)*(1+a^2)/45) := by
  unfold q11 d11 d3 d5
  ring

theorem q11_lower (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    c a/11 ≤ q11 a ∧ 0 < q11 a := by
  obtain ⟨hc0,_,hca⟩ := c_bounds a ha0 ha1
  have hs : 0 ≤ 4*a^2-(c a)^2 := by nlinarith
  have hnon : 0 ≤ (a^2+a^4)/495+(a^6+a^8)/11+
      (4*a^2-(c a)^2)*(1+a^2)/45 := by positivity
  have hh : c a/11 ≤ q11 a := by
    rw [q11_lower_identity]
    nlinarith
  exact ⟨hh, (by positivity : 0 < c a/11).trans_le hh⟩

/-- Lemma 9.2, all five leading coefficients are strictly positive. -/
theorem coefficients_positive (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    0 < q3 a ∧ 0 < q5 a ∧ 0 < q7 a ∧ 0 < q9 a ∧ 0 < q11 a := by
  obtain ⟨h3,_,h5,_,h7,_⟩ := first_coefficients a ha0 ha1
  exact ⟨h3,h5,h7,(q9_bounds a ha0 ha1).1,(q11_lower a ha0 ha1).2⟩

theorem polynomial_ordering (a y : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hy : 0 < y) :
    0 < Q3 a y ∧ Q3 a y < Q5 a y ∧ Q5 a y < Q7 a y ∧ Q7 a y < Q9 a y := by
  obtain ⟨h3,h5,h7,h9,_⟩ := coefficients_positive a ha0 ha1
  unfold Q3 Q5 Q7 Q9
  exact ⟨by positivity, lt_add_of_pos_right _ (by positivity),
    lt_add_of_pos_right _ (by positivity), lt_add_of_pos_right _ (by positivity)⟩

theorem Q9_odd (a y : ℝ) : Q9 a (-y) = -Q9 a y := by
  unfold Q9 Q7 Q5 Q3; ring

/-- Equation 9.19, exact identity in the independent variables a and y. -/
theorem differential_defect_identity (a y : ℝ) :
    (1-y^2)*(1-a^2*y^2)*Q9prime a y-c a*y^2*(1-(Q9 a y)^2) =
      -11*q11 a*y^10+(9*a^2*q9 a+c a*(2*q3 a*q7 a+(q5 a)^2))*y^12+
      c a*(2*q3 a*q9 a+2*q5 a*q7 a)*y^14+
      c a*(2*q5 a*q9 a+(q7 a)^2)*y^16+
      2*c a*q7 a*q9 a*y^18+c a*(q9 a)^2*y^20 := by
  unfold Q9prime Q9 Q7 Q5 Q3 q3 q5 q7 q9 q11 d3 d5 d7 d9 d11 c
  ring

/-- Equation 9.21. This arithmetic is reduced by the Lean kernel. -/
theorem comparison_tail_bound :
    (1012/175:ℚ)*(1/16)+(2416/945)*(1/16)^2+(4756/2205)*(1/16)^3+
      (32/21)*(1/16)^4+(64/81)*(1/16)^5 = 604705921/1625702400 ∧
      (604705921/1625702400:ℚ) < 3/8 := by norm_num

end LeanMath.Papers.V14Coefficients
