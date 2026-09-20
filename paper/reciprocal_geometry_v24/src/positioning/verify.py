"""Exact checks for V24's bounded equivalence discussion.

This checks algebra and finite regression cases, not Böttcher's analytic
existence theorem, the universal square-free proof, or historical priority.
"""
from pathlib import Path
import json
import sympy as sp

p, t, u, v, q, x = sp.symbols("p t u v q x")
S = (p - 2) * (t**2 + 1) + (10*p + 4)*t
P = (p - 1)**2 * S * (v - 1)**2 - 12*p*(t*v - 1)**2
checks = {}


def equal(name, actual, expected=0):
    difference = sp.factor(actual - expected)
    if difference != 0:
        raise AssertionError(f"{name}: {difference}")
    checks[name] = True


equal("radicand_discriminant", sp.discriminant(S, t), 96*p*(p + 1))
equal("radicand_nonzero_constant", S.subs(t, 0), p - 2)
equal("quadratic_discriminant", sp.discriminant(P, v),
      48*p*(p - 1)**2*(t - 1)**2*S)
equal("primitive_coefficients_sum", P.subs(v, 1), -12*p*(t - 1)**2)
equal("no_common_factor_at_one", P.subs(t, 1),
      12*p**2*(p - 2)*(v - 1)**2)

# Recover the radical from the *unsquared* branch formula. This also checks
# that elimination has not changed the sign in the displayed recovery.
phi = (1 + (p - 1)*q)/(t + (p - 1)*q)
equal("recover_radical", (1 - t*phi)/((p - 1)*(phi - 1)), q)
equal("elimination_before_square_root", P.subs(v, phi),
      (p - 1)**2*(t - 1)**2*(S - 12*p*q**2)/(t + (p - 1)*q)**2)

# Form the target independently from the generalized binomial recurrence.
# Truncating at degree six suffices for every coefficient tested below.
coeff = [sp.S.One]
for k in range(1, 7):
    coeff.append(sp.factor(coeff[-1] * (-1/p - (k - 1))/k))
target = sum(c*u**k for k, c in enumerate(coeff))
residual = sp.Poly(sp.expand(P.subs({t: 1 + u, v: target})), u)
for k in range(6):
    equal(f"target_contact_coefficient_{k}", residual.nth(k))
lead = (p - 2)*(p - 1)**2*(p + 1)*(3*p + 1)/(60*p**4)
equal("target_contact_coefficient_6", residual.nth(6), lead)
derivative = sp.Poly(sp.expand(sp.diff(P, v).subs({t: 1 + u, v: target})), u)
equal("branch_derivative_coefficient_1", derivative.nth(1), -24*p*(p - 1))

# Exact jet consistency: residual contact six divided by a first-order
# derivative gives fifth-order branch error, then e=log(x), t=x**p.
c_arc = (p - 2)*(p**2 - 1)*(3*p + 1)/1440
c_rat = (p**2 - 1)*(4*p**2 - 1)/720
equal("contact_implies_arc_coefficient", lead/(24*p*(p - 1))*p**5, c_arc)
equal("positive_scaling_fourth_power", c_arc/c_rat,
      (p - 2)*(3*p + 1)/(2*(4*p**2 - 1)))
lam, mu, a, b, c, d = sp.symbols("lambda mu a b c d")
F, G, h = a*x**5 + b*x**6, c*x**5 + d*x**6, lam*x + mu*x**2
defect = sp.Poly(sp.expand(h.subs(x, F) - G.subs(x, h)), x)
equal("conjugacy_leading_coefficient", defect.nth(5), lam*a - c*lam**5)

# Supplementary finite tests; the manuscript proves the general integer
# statement from S's distinct nonzero roots and the derivative of x**p.
squarefree_cases = []
for degree in range(3, 13):
    composed = sp.Poly(S.subs({p: degree, t: x**degree}), x)
    if sp.gcd(composed, composed.diff()).degree() != 0:
        raise AssertionError(f"Repeated radicand root at degree {degree}")
    squarefree_cases.append(degree)

report = {
    "revision": "V24",
    "symbolic_checks": len(checks),
    "checks": checks,
    "residual_order": 6,
    "residual_leading_coefficient": str(lead),
    "diagonal_222_required_residual_order": 8,
    "integer_squarefree_regression_cases": squarefree_cases,
    "scope": "Exact identities and finite regression cases only. The universal "
             "nonrationality proof and application of Böttcher's classical "
             "analytic theorem are written in POSITIONING.md, not Lean-checked.",
}
Path(__file__).with_name("checks.json").write_text(json.dumps(report, indent=2) + "\n")
print(f"PASS: {len(checks)} exact positioning checks; "
      f"{len(squarefree_cases)} integer square-free regression cases")
