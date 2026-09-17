"""Check recorded runs and repeat integrated decks with five times smaller max step."""
import json
from pathlib import Path
import numpy as np
from simulate_p3 import execute,P,V0
r=json.loads((P/'results.json').read_text())
assert r['spice_runs']==56
assert len(r['cells'])==28
for x in r['cells'][:-1]:
 assert abs(x['final_den_error'])<1e-5
 assert x['rise_settle_0p1pct_us'] is not None and x['rise_settle_0p1pct_us']<3
 assert x['fall_settle_0p1pct_us'] is not None and x['fall_settle_0p1pct_us']<3
assert abs(r['cells'][-1]['final_den_error'])>.1
checks=[]
for z in r['chains']:
 for x in z['nominal']+z['frozen_calibration_corners']:
  assert x['port_peak']<.95
  assert abs(x['corrected_error'])<3e-5
  assert x['servo_error_at_sample_volts']<30e-6
 net=(P/(z['mode'].lower()+'_p3.cir')).read_text()
 assert 'tran 100n' in net
 net=net.replace('tran 100n','tran 20n').replace('0 100n uic','0 20n uic')
 a=execute(net)
 out=float(np.interp(645e-6,a[:,0],a[:,11]))
 nominal=next(x['output_volts'] for x in z['nominal'] if x['m']==2)
 ppm=(out-nominal)/(V0*2**(1/3))*1e6
 assert abs(ppm)<1,ppm
 checks.append(dict(mode=z['mode'],max_step_ns=20,output_difference_ppm=ppm))
(P/'VALIDATION.json').write_text(json.dumps(dict(main_runs=56,refined_step_runs=2,total_spice_runs=58,cell_settling_below_3us=True,chain_error_below_30ppm_at_tested_samples=True,step_checks=checks),indent=2)+'\n')
print(checks)
