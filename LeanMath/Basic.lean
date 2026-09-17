import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Premières preuves : chaque théorème est vérifié par Lean. -/

namespace LeanMath

-- Une identité algébrique sur les nombres réels.
theorem carre_somme (a b : ℝ) :
    (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring

-- Déduire une inégalité d'une hypothèse.
theorem ajouter_un (x : ℝ) (h : x > 2) : x + 1 > 3 := by
  linarith

-- Une preuve directe à partir d'un théorème de la bibliothèque.
theorem carre_positif (x : ℝ) : 0 ≤ x ^ 2 := by
  exact sq_nonneg x

end LeanMath
