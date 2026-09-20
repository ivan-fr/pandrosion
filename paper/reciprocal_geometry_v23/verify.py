"""Reproduce V23 mathematics and figures; Lean audits run separately; retained SPICE data are checked without new simulation."""
from pathlib import Path
import subprocess,sys
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
scripts=[
 'paper/reciprocal_geometry_v23/src/uniform/verify.py',
 'paper/reciprocal_geometry_v20/src/revision/verify.py',
 'paper/reciprocal_geometry_v20/src/review/check_math.py',
 'paper/reciprocal_geometry_v20/src/fixed_circle/verify.py',
 'paper/reciprocal_geometry_v20/src/decentered/verify.py',
 'research/fixed_circle_safeguard/verify.py',
 'paper/reciprocal_geometry_v23/src/branch/verify.py',
 'paper/reciprocal_geometry_v23/src/branch/protocol.py',
 'paper/reciprocal_geometry_v23/src/branch/figure.py',
 'paper/reciprocal_geometry_v23/src/branch/fold.py',
 'paper/reciprocal_geometry_v23/draw_figures.py',
 'paper/reciprocal_geometry_v23/draw_pandrosion.py',
 'paper/reciprocal_geometry_v23/draw_safeguard.py',
 'research/analog_fast_ad/verify.py',
 'paper/pandrosion_analog_v30/check_results.py']
for script in scripts:
 print(script,flush=True)
 subprocess.run([sys.executable,str(ROOT/script)],cwd=ROOT,check=True)
for name in ['fast_geometry','analog_circuit']:
 assert (HERE/f'figures/{name}.pdf').read_bytes()==(ROOT/f'paper/pandrosion_analog_v30/figures/{name}.pdf').read_bytes()
print('PASS: V23 mathematics, two controllers, five Pandrosion figures and companion provenance')
