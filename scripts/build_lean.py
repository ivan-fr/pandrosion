"""Build every bundled source in dependency order, limiting peak memory."""
from pathlib import Path
import re
import subprocess

sources = {'.'.join(p.with_suffix('').parts): p
           for folder in ('LeanMath', 'research', 'lean')
           for p in Path(folder).rglob('*.lean')}
seen = set()
active = set()
order = []
def visit(module):
    if module in seen:
        return
    if module in active:
        raise RuntimeError(f'Cyclic import: {module}')
    active.add(module)
    for dep in re.findall(r'^import\s+([\w.]+)', sources[module].read_text(), re.M):
        if dep in sources:
            visit(dep)
    active.remove(module)
    seen.add(module)
    order.append(module)
for module in sorted(sources):
    visit(module)
for i, module in enumerate(order, 1):
    print(f'[{i}/{len(order)}] {module}', flush=True)
    subprocess.run(['lake', 'build', module], check=True)
subprocess.run(['lake', 'build'], check=True)
print(f'All {len(order)} source modules and library targets built successfully.')
