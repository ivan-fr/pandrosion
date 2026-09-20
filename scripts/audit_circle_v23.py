"""Audit every declaration introduced for V23 Theorem 4.3.

The manifest must cover the three complete source modules. Lean checks the
transitive axiom dependencies; only the standard logical axioms are accepted.
Run after `lake build LeanMath.Papers.RectangleFixedCircleTheorem43`.
"""
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
MODULES = (
    'RectangleFixedCircleUniform',
    'RectangleFixedCircleDynamics',
    'RectangleFixedCircleTheorem43',
)
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
expected = []
for module in MODULES:
    source = ROOT / 'LeanMath' / 'Papers' / f'{module}.lean'
    expected.extend(f'LeanMath.Papers.{module}.{name}' for name in
                    re.findall(r'^(?:theorem|lemma|def)\s+(\w+)', source.read_text(), re.M))
audit = ROOT / 'validation' / 'rectangle_fixed_circle_v23' / 'Audit.lean'
manifest = re.findall(r'^#print axioms (\S+)', audit.read_text(), re.M)
if manifest != expected:
    raise SystemExit('V23 audit manifest does not cover every source declaration in order')
result = subprocess.run(['lake', 'env', 'lean', str(audit)], cwd=ROOT,
                        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
print(result.stdout)
result.check_returncode()
if 'sorryAx' in result.stdout:
    raise SystemExit('Unproved declaration in the V23 audit')
records = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
                     result.stdout)
if [name for name, _ in records] != expected:
    raise SystemExit(f'Expected {len(expected)} named V23 axiom records; found {len(records)}')
for name, axioms in records:
    extra = {x.strip() for x in axioms.split(',') if x.strip()} - ALLOWED
    if extra:
        raise SystemExit(f'Unexpected axioms for {name}: {extra}')
print(f'V23 circle audit: {len(expected)} declarations passed; only standard logical axioms.')
