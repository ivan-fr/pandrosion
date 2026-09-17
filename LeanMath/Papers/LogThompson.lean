import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Normed.Group.Constructions

/-! Logarithmic transport on the positive orthant, with optional fixed positive weights.
The distance is defined explicitly; no new global metric instance is installed. -/
noncomputable section
namespace LeanMath.Papers.LogThompson

abbrev Positive (n : ℕ) := {u : Fin n → ℝ // ∀ i, 0 < u i}

def encode {n : ℕ} (w : Fin n → ℝ) (u : Positive n) : Fin n → ℝ :=
  fun i => Real.log (u.val i) / w i

def decode {n : ℕ} (w x : Fin n → ℝ) : Positive n :=
  ⟨fun i => Real.exp (w i * x i), fun _ => Real.exp_pos _⟩

def distance {n : ℕ} (w : Fin n → ℝ) (u v : Positive n) : ℝ :=
  ‖encode w u - encode w v‖

def lift {n : ℕ} (w : Fin n → ℝ) (f : (Fin n → ℝ) → (Fin n → ℝ))
    (u : Positive n) := decode w (f (encode w u))

theorem encode_decode {n : ℕ} (w x : Fin n → ℝ) (hw : ∀ i, 0 < w i) :
    encode w (decode w x) = x := by
  funext i
  simp [encode, decode, ne_of_gt (hw i)]

theorem decode_encode {n : ℕ} (w : Fin n → ℝ) (u : Positive n) (hw : ∀ i, 0 < w i) :
    decode w (encode w u) = u := by
  apply Subtype.ext
  funext i
  change Real.exp (w i * (Real.log (u.val i) / w i)) = u.val i
  have he : w i * (Real.log (u.val i) / w i) = Real.log (u.val i) := by
    field_simp [ne_of_gt (hw i)]
  rw [he, Real.exp_log (u.property i)]

theorem distance_zero_iff {n : ℕ} (w : Fin n → ℝ) (u v : Positive n)
    (hw : ∀ i, 0 < w i) : distance w u v = 0 ↔ u = v := by
  simp only [distance, norm_eq_zero, sub_eq_zero]
  constructor
  · intro h
    have he := congrArg (decode w) h
    simpa only [decode_encode w u hw, decode_encode w v hw] using he
  · exact fun h => congrArg (encode w) h

theorem distance_formula {n : ℕ} (w : Fin n → ℝ) (u v : Positive n) :
    distance w u v = ‖fun i => (Real.log (u.val i) - Real.log (v.val i)) / w i‖ := by
  unfold distance
  congr 1
  funext i
  simp [encode, sub_div]

/-- A contraction towards a log-root transports to weighted Thompson distance. -/
theorem lift_contracts {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (f : (Fin n → ℝ) → (Fin n → ℝ)) (z : Fin n → ℝ) (q : ℝ)
    (hf : ∀ x, ‖f x-z‖ ≤ q * ‖x-z‖) (u : Positive n) :
    distance w (lift w f u) (decode w z) ≤ q * distance w u (decode w z) := by
  simpa only [distance, lift, encode_decode w _ hw] using hf (encode w u)

end LeanMath.Papers.LogThompson
