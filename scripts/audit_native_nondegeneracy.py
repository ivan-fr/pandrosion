"""Independent post-V20 axiom audit, without changing the frozen V20 audit."""
import re
import subprocess
from pathlib import Path
source = Path('validation/rectangle_native_nondegeneracy/Audit.lean')
p = subprocess.run(['lake', 'env', 'lean', str(source)], text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
print(p.stdout)
p.check_returncode()
records = re.findall(r"depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms", p.stdout)
assert len(records) == source.read_text().count('#print axioms'), 'Missing audit output'
for axioms in records:
    assert set(filter(None, map(str.strip, axioms.split(',')))) <= {'propext', 'Classical.choice', 'Quot.sound'}, axioms
print(f'Post-V20 native incidence: {len(records)} declarations passed the axiom audit.')
