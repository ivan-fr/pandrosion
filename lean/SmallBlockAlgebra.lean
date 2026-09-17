import Std
namespace SmallBlockAudit
/-- Expansion of det(rI - A) for symmetric zero-diagonal 3x3 A. -/
theorem triangle_characteristic {R : Type} [Lean.Grind.CommRing R]
    (a b c r : R) :
    r * (r*r-c*c) - a*(a*r+b*c) - b*(a*c+r*b) =
      r*r*r - (a*a+b*b+c*c)*r - 2*a*b*c := by
  grind

/-- E + tr(A^3) for a zero-diagonal symmetric three-point block. -/
theorem triangle_moment {R : Type} [Lean.Grind.CommRing R]
    (a b c : R) :
    (a*a+b*b) + (a*a+c*c) + (b*b+c*c) +
      (a*c*b+b*c*a+a*b*c+c*b*a+b*a*c+c*a*b) =
      2*(a*a+b*b+c*c)+6*a*b*c := by
  grind
#print axioms triangle_characteristic
#print axioms triangle_moment
end SmallBlockAudit
