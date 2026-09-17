import json
import numpy as np
import p3_base as base
from simulate_p4 import P
r=json.loads((P/'results.json').read_text());checks=[]
for resistance in [10000,12500,15000]:
 net=f'''Independent RC discharge check
Rload state 0 {resistance}
Cstate state 0 10n IC=4.096
.control
set wr_singlescale
set wr_vecnames
set numdgt=14
tran 20n 23u 0 20n uic
wrdata waveform.txt v(state)
quit
.endc
.end
'''
 a=base.execute(net);expected=4.096*np.exp(-23e-6/(resistance*10e-9))
 actual=float(a[-1,1]);assert abs(actual/expected-1)<2e-5
 checks.append(dict(resistance=resistance,expected_volts=expected,simulated_volts=actual))
step=[]
for z in r['results']:
 for x in z['buffered']:
  assert abs(x['error'])<3e-5 and x['port_peak']<.95
  assert abs(x['hold_change_ppm'])<10
 for x in z['frozen_calibration_corners']:
  assert abs(x['error'])<5e-5 and x['port_peak']<.95
 net=(P/(z['mode'].lower()+'_buffered.cir')).read_text().replace('tran 100n','tran 20n').replace('0 100n uic','0 20n uic')
 a=base.execute(net);out=float(np.interp(645e-6,a[:,0],a[:,11]))
 old=next(x['output_volts']for x in z['buffered']if x['m']==2)
 diff=(out-old)/(base.V0*2**(1/3))*1e6
 assert abs(diff)<1
 step.append(dict(mode=z['mode'],difference_ppm=diff))
(P/'VALIDATION.json').write_text(json.dumps(dict(main_runs=40,RC_checks=checks,refined_step_checks=step,retained_validation_runs=45),indent=2)+'\n')
print('RC checks and refined time-step checks passed')
