"""Compile the construction and reject nonstandard axioms in its core theorems."""
import json,re,subprocess
from pathlib import Path
subprocess.run(['lake','build','LeanMath.Papers.GeometricSubdivision'],check=True)
p=subprocess.run(['lake','env','lean','validation/geometric_subdivision/Audit.lean'],capture_output=True,text=True)
print(p.stdout);p.check_returncode()
assert 'sorryAx' not in p.stdout
matches=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',p.stdout)
assert len(matches)==7
for m in matches:assert set(x.strip() for x in m.split(',')) <= {'propext','Classical.choice','Quot.sound'}
Path('validation/geometric_subdivision/verification.json').write_text(json.dumps(dict(status='PASS',audited_theorems=len(matches),allowed_axioms=['propext','Classical.choice','Quot.sound'],new_axioms=False,sorry=False),indent=2)+'\n')
print('Seven construction theorems passed the axiom audit.')
