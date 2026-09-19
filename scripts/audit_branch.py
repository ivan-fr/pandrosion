"""Axiom audit for the whole-branch contraction module (V20 conjecture (29), proved in V22).

Checks the 33 declarations of LeanMath.Papers.RectangleFixedCircleBranch and rejects
any axiom outside Lean's standard three, and any sorryAx.
"""
from pathlib import Path
import re
import subprocess

allowed = {'propext', 'Classical.choice', 'Quot.sound'}
expected = 33
audit = Path('validation/rectangle_fixed_circle_branch/Audit.lean')
p = subprocess.run(['lake', 'env', 'lean', str(audit)],
                   text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
print(p.stdout)
p.check_returncode()
if 'sorryAx' in p.stdout:
    raise SystemExit('Unproved declaration in the branch audit')
matches = re.findall(r"depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms", p.stdout)
if len(matches) != expected:
    raise SystemExit(f'expected {expected} audit records, found {len(matches)}')
for axioms in matches:
    extra = {x.strip() for x in axioms.split(',') if x.strip()} - allowed
    if extra:
        raise SystemExit(f'Unexpected axioms: {extra}')
print(f'Branch audit: {expected} declarations passed the axiom audit.')
