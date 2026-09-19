"""Reproduce V21 from the repository root; no electrical-model rerun required.

The geometric campaigns stay in their archived V20 locations to preserve their
provenance. They regenerate deterministic JSON records there. The V30 checker
reads retained circuit evidence rather than claiming a new SPICE campaign.
"""
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SCRIPTS = [
    'paper/reciprocal_geometry_v20/src/revision/verify.py',
    'paper/reciprocal_geometry_v20/src/review/check_math.py',
    'paper/reciprocal_geometry_v20/src/fixed_circle/verify.py',
    'paper/reciprocal_geometry_v20/src/decentered/verify.py',
    'research/fixed_circle_safeguard/verify.py',
    'research/fixed_circle_safeguard/draw.py',
    'research/analog_fast_ad/verify.py',
    'paper/pandrosion_analog_v30/check_results.py',
    'paper/reciprocal_geometry_v21/draw_figures.py',
    'paper/reciprocal_geometry_v21/draw_pandrosion.py',
]
for script in SCRIPTS:
    print(f'\n=== {script} ===', flush=True)
    subprocess.run([sys.executable, str(ROOT / script)], cwd=ROOT, check=True)

# The electrical and binary diagrams are explicitly reused from the companion.
for name in ['fast_geometry', 'analog_circuit']:
    assert (HERE / f'figures/{name}.pdf').read_bytes() == (
        ROOT / f'paper/pandrosion_analog_v30/figures/{name}.pdf'
    ).read_bytes(), f'Companion figure differs: {name}'
print('PASS: V21 geometry, centered algebra, retained analog results and figure provenance')
