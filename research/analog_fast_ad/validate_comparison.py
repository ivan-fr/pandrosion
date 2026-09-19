"""Score host benchmark outputs; reference roots never enter timed methods."""
from pathlib import Path
import json
import mpmath as mp
mp.mp.dps=90
path=Path(__file__).with_name('benchmark_results.json')
r=json.loads(path.read_text())
for row in r['rows']:
 ref=mp.exp(mp.log(mp.mpf(row['X']))/row['p'])
 for key in ['centered_root','standard_root']:
  error=float(abs(mp.mpf(row[key])/ref-1))
  assert error<2e-13
  row[key+'_relative_error']=error
path.write_text(json.dumps(r,indent=2)+'\n')
print('PASS: 24 digital outputs; all relative errors below 2e-13; no speed threshold asserted')
