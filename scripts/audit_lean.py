"""Recheck the V19 audit and reject any axiom outside Lean's standard three."""
from pathlib import Path
import re
import subprocess

allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for name, expected in [('Audit', 149), ('BackgroundAudit', 11)]:
    p = subprocess.run(['lake', 'env', 'lean', f'validation/rectangle_v19/{name}.lean'],
                       text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    print(p.stdout)
    p.check_returncode()
    if 'sorryAx' in p.stdout:
        raise SystemExit('Unproved declaration in audit')
    matches = re.findall(r"depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms", p.stdout)
    if len(matches) != expected:
        raise SystemExit(f'{name}: expected {expected} audit records, found {len(matches)}')
    for axioms in matches:
        extra = {x.strip() for x in axioms.split(',') if x.strip()} - allowed
        if extra:
            raise SystemExit(f'Unexpected axioms: {extra}')
    print(f'{name}: {expected} declarations passed the axiom audit.')
