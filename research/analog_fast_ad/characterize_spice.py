"""One-at-a-time timed sensitivity and sample-phase tests using real ngspice."""
import json
from pathlib import Path
from model import prepare
from spice import run

SCENARIOS = {
 'baseline': {},
 'offset_25uV': dict(offset=25e-6),
 'product_gain_1000ppm': dict(gain=.001),
 'load_50k': dict(rin=50000),
 'leak_5nA': dict(leak=5e-9),
 'charge_0p5pC': dict(charge=.5e-12),
 'target_gain_1000ppm_offset_25uV': dict(target_gain=.001,target_offset=25e-6),
 'stage_tau_30us': dict(stage_cap=3e-6),
 'stage_tau_30us_slower_clock': dict(stage_cap=3e-6,timing_scale=30.),
}
def main():
 rows=[]
 for r in prepare([[3,500000],[1000000,500000]]):
  for scenario,cfg in SCENARIOS.items():
   row=dict(scenario=scenario,**run(r,config=cfg))
   rows.append(row)
   print(r['p'],scenario,row['decoded_relative_error'],flush=True)
  baseline=rows[-len(SCENARIOS)]
  # Finite off-resistance still leaks over the longer cycle, especially at p=3.
  target = 1e-9 if r['p']==1000000 else 1e-6
  assert rows[-1]['decoded_relative_error']<target, 'Slower clock failed the stated accuracy target'
  charged=next(x for x in rows if x['p']==r['p'] and x['scenario']=='charge_0p5pC')
  # At cubic convergence, transfer injection remains visible at the readout.
  assert abs((charged['q_final']-baseline['q_final'])-.5e-12/10e-9)<2e-6
  leakage=next(x for x in rows if x['p']==r['p'] and x['scenario']=='leak_5nA')
  assert abs(leakage['final_hold_drift']+37.5e-6)<.2e-6
 # Check the new fast charge pulse independently with a finer transient step.
 r=prepare([[1000000,500000]])[0]
 fine=run(r,config=SCENARIOS['charge_0p5pC'],step='0.05u')
 coarse=next(x for x in rows if x['p']==1000000 and x['scenario']=='charge_0p5pC')
 assert abs(fine['q_final']-coarse['q_final'])<1e-6
 rows.append(dict(scenario='charge_0p5pC_fine_step',**fine))
 Path(__file__).with_name('characterization_spice.json').write_text(json.dumps(rows,indent=2)+'\n')
 print('PASS',len(rows),'transients; charge area, leakage drift and timestep checks')
if __name__=='__main__':main()
