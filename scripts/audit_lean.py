"""Build retained sources and audit the explicitly documented theorem subset."""
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
subprocess.run(['lake', 'build'], cwd=ROOT, check=True)
for name, expected in [('decentered', 10), ('geometric_subdivision', 7)]:
    result = subprocess.run(
        ['lake', 'env', 'lean', f'validation/{name}/Audit.lean'],
        cwd=ROOT, check=True, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    print(result.stdout)
    records = re.findall(
        r"depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms",
        result.stdout,
    )
    if len(records) != expected or 'sorryAx' in result.stdout:
        raise SystemExit(f'{name}: incomplete audit or admitted proof')
    for record in records:
        extra = {a.strip() for a in record.split(',') if a.strip()} - ALLOWED
        if extra:
            raise SystemExit(f'{name}: unexpected axioms {extra}')
    print(f'{name}: {expected} declarations passed the axiom audit.')
