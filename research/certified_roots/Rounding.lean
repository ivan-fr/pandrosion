import Mathlib

/- Exact midpoint theorem. No claim of refinement of the Python code or of
   the complete IEEE decoder is made by this module. -/
namespace CertifiedRoots

theorem power_le_root (a r : ℝ) (p : ℕ) (hp : 0 < p)
    (_ha : 0 ≤ a) (hr : 0 ≤ r) (h : a^p ≤ r^p) : a ≤ r := by
  by_contra hn
  have hh := pow_lt_pow_left₀ (lt_of_not_ge hn) hr (Nat.ne_of_gt hp)
  linarith

/-- An exact rational bracket and a midpoint power comparison select a
    nearest endpoint to the real root. Equality is allowed on either side. -/
theorem midpoint_sound (x l u : ℚ) (p : ℕ) (r : ℝ)
    (hp : 0 < p) (hl : 0 ≤ l) (hlu : l ≤ u)
    (hr : 0 ≤ r) (hroot : r^p = (x : ℝ))
    (hlo : l^p ≤ x) (hhi : x ≤ u^p) :
    (x ≤ ((l+u)/2)^p → |r-(l:ℝ)| ≤ |r-(u:ℝ)|) ∧
    (((l+u)/2)^p ≤ x → |r-(u:ℝ)| ≤ |r-(l:ℝ)|) := by
  have hl' : (0:ℝ) ≤ l := by exact_mod_cast hl
  have hlu' : (l:ℝ) ≤ u := by exact_mod_cast hlu
  have hu' : (0:ℝ) ≤ u := le_trans hl' hlu'
  have hlow : (l:ℝ)^p ≤ r^p := by rw [hroot]; exact_mod_cast hlo
  have hhigh : r^p ≤ (u:ℝ)^p := by rw [hroot]; exact_mod_cast hhi
  have hrl := power_le_root _ _ p hp hl' hr hlow
  have hru := power_le_root _ _ p hp hr hu' hhigh
  have hm : (0:ℝ) ≤ ((l:ℝ)+u)/2 := by positivity
  rw [abs_of_nonneg (sub_nonneg.mpr hrl), abs_of_nonpos (sub_nonpos.mpr hru)]
  constructor
  · intro h
    have h' : r^p ≤ (((l:ℝ)+u)/2)^p := by rw [hroot]; exact_mod_cast h
    have := power_le_root _ _ p hp hr hm h'
    linarith
  · intro h
    have h' : (((l:ℝ)+u)/2)^p ≤ r^p := by rw [hroot]; exact_mod_cast h
    have := power_le_root _ _ p hp hm hr h'
    linarith

def chooseLower (x l u : ℚ) (p : ℕ) (lowerEven : Bool) : Bool :=
  if x < ((l+u)/2)^p then true
  else if ((l+u)/2)^p < x then false
  else lowerEven

def accepts (x l u : ℚ) (p : ℕ) : Bool :=
  decide (0 < p ∧ 0 ≤ l ∧ l ≤ u ∧ l^p ≤ x ∧ x ≤ u^p)

/-- The executable choice is correct for every accepted rational bracket. -/
theorem choice_sound (x l u : ℚ) (p : ℕ) (even : Bool) (r : ℝ)
    (h : accepts x l u p = true) (hr : 0 ≤ r) (hroot : r^p = (x:ℝ)) :
    if chooseLower x l u p even then |r-(l:ℝ)| ≤ |r-(u:ℝ)|
    else |r-(u:ℝ)| ≤ |r-(l:ℝ)| := by
  simp only [accepts, decide_eq_true_eq] at h
  have hs := midpoint_sound x l u p r h.1 h.2.1 h.2.2.1 hr hroot h.2.2.2.1 h.2.2.2.2
  by_cases h₁ : x < ((l+u)/2)^p
  · simpa [chooseLower, h₁] using hs.1 (le_of_lt h₁)
  · by_cases h₂ : ((l+u)/2)^p < x
    · simpa [chooseLower, h₁, h₂] using hs.2 (le_of_lt h₂)
    · cases even with
      | false => simpa [chooseLower, h₁, h₂] using hs.2 (le_of_not_gt h₁)
      | true => simpa [chooseLower, h₁, h₂] using hs.1 (le_of_not_gt h₂)

/-- On an exact midpoint tie the executable decision follows the parity flag. -/
theorem tie_even (x l u : ℚ) (p : ℕ) (even : Bool)
    (h : x = ((l+u)/2)^p) : chooseLower x l u p even = even := by
  simp [chooseLower, h]

abbrev Certified (x l u : ℚ) (p : ℕ) (even : Bool) :=
  { b : Bool // accepts x l u p = true ∧ b = chooseLower x l u p even }

def certify (x l u : ℚ) (p : ℕ) (even : Bool) : Option (Certified x l u p even) :=
  if h : accepts x l u p = true then
    some ⟨chooseLower x l u p even, h, rfl⟩
  else none

theorem certified_sound (x l u : ℚ) (p : ℕ) (even : Bool)
    (v : Certified x l u p even) (r : ℝ) (hr : 0 ≤ r)
    (hroot : r^p = (x:ℝ)) :
    if v.val then |r-(l:ℝ)| ≤ |r-(u:ℝ)|
    else |r-(u:ℝ)| ≤ |r-(l:ℝ)| := by
  rw [v.property.2]
  exact choice_sound x l u p even r v.property.1 hr hroot

/-- Adjacent endpoints suffice for nearest rounding on the entire grid.
    The absence of grid values between l and u is an explicit hypothesis. -/
theorem nearest_grid (r l u v : ℝ) (hrl : l ≤ r) (hru : r ≤ u)
    (_hv : v = l ∨ v = u)
    (hl : |r-v| ≤ |r-l|) (hu : |r-v| ≤ |r-u|)
    (grid : Set ℝ) (hgap : ∀ z ∈ grid, z ≤ l ∨ u ≤ z) :
    ∀ z ∈ grid, |r-v| ≤ |r-z| := by
  intro z hz
  rcases hgap z hz with hz | hz
  · have hzr : z ≤ r := le_trans hz hrl
    rw [abs_of_nonneg (sub_nonneg.mpr hzr)]
    rw [abs_of_nonneg (sub_nonneg.mpr hrl)] at hl
    linarith
  · have hrz : r ≤ z := le_trans hru hz
    rw [abs_of_nonpos (sub_nonpos.mpr hrz)]
    rw [abs_of_nonpos (sub_nonpos.mpr hru)] at hu
    linarith

example : chooseLower (25/4) 2 3 2 true = true := by norm_num [chooseLower]
example : chooseLower (25/4) 2 3 2 false = false := by norm_num [chooseLower]

#print axioms midpoint_sound
#print axioms choice_sound
#print axioms tie_even
#print axioms nearest_grid
#print axioms certified_sound
end CertifiedRoots

def main (args : List String) : IO UInt32 := do
  let path := args.headD "research/certified_roots/lean_cases.csv"
  let content ← IO.FS.readFile path
  let start ← IO.monoMsNow
  let mut count := 0
  let mut rejected := 0
  let mut failures := 0
  for line in content.splitOn "\n" do
    if line.isEmpty then continue
    match (line.splitOn ",").map String.toNat! with
    | [xn,xd,ln,ld,un,ud,p,even,expected] =>
      if xd == 0 || ld == 0 || ud == 0 then throw (IO.userError "zero denominator")
      let result := CertifiedRoots.certify ((xn:ℚ)/xd) ((ln:ℚ)/ld) ((un:ℚ)/ud) p (even == 1)
      let actual := match result with
        | none => 2
        | some v => if v.val then 1 else 0
      count := count+1
      if actual == 2 then rejected := rejected+1
      if actual != expected then failures := failures+1
    | _ => throw (IO.userError "malformed case")
  IO.println s!"cases={count} rejected={rejected} mismatches={failures} wall_ms={(← IO.monoMsNow)-start}"
  return if failures == 0 then 0 else 1
