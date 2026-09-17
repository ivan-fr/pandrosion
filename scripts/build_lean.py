"""Build all Lean sources, or reproducible CI phases for large certificates.

base: modules independent of V14Segments certificates;
segments: a disjoint shard of those certificates;
final: their downstream users, then every default library target.
All phases combined check exactly the same sources as the default 'all'.
"""
from pathlib import Path
import argparse
import re
import subprocess

parser = argparse.ArgumentParser()
parser.add_argument('--phase', choices=['all','base','segments','final'], default='all')
parser.add_argument('--shard', type=int, default=0)
parser.add_argument('--shards', type=int, default=4)
parser.add_argument('--list', action='store_true')
args = parser.parse_args()
if not 0 <= args.shard < args.shards:
    parser.error('shard must lie in [0, shards)')
sources = {'.'.join(p.with_suffix('').parts): p
           for folder in ('LeanMath', 'research', 'lean')
           for p in Path(folder).rglob('*.lean')}
deps = {m: [dep for line in re.findall(r'^import\s+([^\n]+)', p.read_text(), re.M)
            for dep in line.split('--')[0].split() if dep in sources]
        for m,p in sources.items()}
seen,active,order = set(),set(),[]
def visit(module):
    if module in seen:return
    if module in active:raise RuntimeError(f'Cyclic import: {module}')
    active.add(module)
    for dep in deps[module]:visit(dep)
    active.remove(module);seen.add(module);order.append(module)
for module in sorted(sources):visit(module)
segments = {m for m in sources if m.startswith('LeanMath.Papers.V14Segments')}
blocked = set(segments)
for m in order:
    if any(d in blocked for d in deps[m]):blocked.add(m)
base = set(sources)-blocked
final = blocked-segments
# Segment files must be independent of one another for artifact-based splitting.
assert all(not (set(deps[m]) & blocked) for m in segments)
assert base | segments | final == set(sources)
assert not (base & segments or base & final or segments & final)
shard = set(sorted(segments)[args.shard::args.shards])
selected = {'all':set(sources),'base':base,'segments':shard,'final':final}[args.phase]
chosen = [m for m in order if m in selected]
print(f'Partition: {len(base)} base + {len(segments)} segments + {len(final)} downstream = {len(sources)} modules',flush=True)
for i,module in enumerate(chosen,1):
    print(f'[{i}/{len(chosen)}] {module}',flush=True)
    if not args.list:subprocess.run(['lake','build',module],check=True)
if not args.list and args.phase in ['all','final']:
    subprocess.run(['lake','build'],check=True)
print(f'{args.phase}: {len(chosen)} modules {"listed" if args.list else "built successfully"}.')
