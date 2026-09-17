import Std

/- The algebra used after taking real logarithms. This file deliberately does
   not assert an analytic sqrt/rpow theorem or a zeta bridge. -/
namespace BilateralAudit

 theorem log_balance {R : Type} [Lean.Grind.CommRing R]
    (a z m g : R) (h : a * g = a * z - (1 - a) * m) :
    g + (1 - a) * (m - g) = a * z := by
  grind

 theorem recursive_log_identity {R : Type} [Lean.Grind.Field R]
    (a z m : R) (ha : a ≠ 0) :
    (z - ((1-a)/a)*m) + (1-a)*(m-(z-((1-a)/a)*m)) = a*z := by
  grind

 theorem cayley_inverse {R : Type} [Lean.Grind.Field R] [Lean.Grind.IsCharP R 0]
    (l : R) (hl : l + 2 ≠ 0) (htwo : (2 : R) ≠ 0) :
    2 * (1 + (l-2)/(l+2)) / (1 - (l-2)/(l+2)) = l := by
  have hcancel := Lean.Grind.Field.mul_inv_cancel hl
  have htwo_cancel := Lean.Grind.Field.mul_inv_cancel htwo
  have hn : 1 - (l-2)/(l+2) ≠ 0 := by grind
  grind

#print axioms log_balance
#print axioms recursive_log_identity
#print axioms cayley_inverse
end BilateralAudit
