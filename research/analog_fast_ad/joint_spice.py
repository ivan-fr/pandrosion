"""Combined timed behavioral errors, finite coefficients/ADC and colored disturbance.
No yield claim: deterministic signed corners and two reproducible noise seeds.
"""
from pathlib import Path
import json,math
from model import prepare
from spice import run

def config(profile,temp,sign,seed,slow=False):
 tight=profile=='trim_target'
 dt=abs(temp-25)
 return dict(offset=sign*((1e-6 if tight else 25e-6)+dt*(.02e-6 if tight else .5e-6)),
  gain=sign*((20e-6 if tight else .001)+dt*(.2e-6 if tight else 10e-6)),
  target_offset=sign*((1e-6 if tight else 25e-6)+dt*(.02e-6 if tight else .5e-6)),
  target_gain=sign*((20e-6 if tight else .001)+dt*(.2e-6 if tight else 10e-6)),
  rin=1e7 if tight else 50000,
  leak=sign*(50e-12 if tight else 5e-9)*2**((temp-25)/10),
  charge=sign*(.02e-12 if tight else .5e-12),
  coeff_bits=24 if tight else 16,adc_bits=22 if tight else 18,
  adc_offset=sign*(1e-6 if tight else 25e-6),adc_gain=sign*(2e-6 if tight else 100e-6),
  adc_inl_lsb=sign*(.5 if tight else 1.),noise_rms=.5e-6 if tight else 5e-6,
  noise_seed=seed,sample_noise_rms=math.sqrt(2*1.380649e-23*(temp+273.15)/10e-9),stage_cap=3e-6 if slow else 100e-9,timing_scale=30. if slow else 1.,
  switch_ron=120.) # ADG1211 headline on-resistance scale, not a full device model

def main():
 rows=[]
 cases=prepare([[3,500000],[32,500000],[983039,500000],[1000000,500000]])
 for r in cases:
  for profile in ['untrimmed','trim_target']:
   for temp,sign in [(25,1),(85,-1)]:
    cfg=config(profile,temp,sign,20260920+int(sign))
    row=dict(profile=profile,temperature_C=temp,**run(r,config=cfg))
    rows.append(row);print(r['p'],profile,temp,row['configured_adc_relative_error'],flush=True)
 # Long clock now tested WITH hot leakage, conversion and all other errors together.
 for profile in ['untrimmed','trim_target']:
  cfg=config(profile,85,1,20260921,slow=True)
  row=dict(profile=profile,temperature_C=85,**run(cases[-1],config=cfg))
  rows.append(row);print('slow joint',profile,row['configured_adc_relative_error'],flush=True)
 # Independent temporal convergence on the million-degree hot joint scenario.
 cfg=config('trim_target',85,-1,20260919)
 fine=run(cases[-1],step='0.05u',config=cfg)
 coarse=next(x for x in rows if x['p']==1000000 and x['profile']=='trim_target' and x['temperature_C']==85 and x['config']['timing_scale']==1)
 assert abs(fine['q_final']-coarse['q_final'])<2e-6
 rows.append(dict(profile='trim_target',temperature_C=85,**fine))
 for row in rows:
  row['accuracy_target']=1e-6 if row['p']<=32 else 1e-9
  row['meets_accuracy_target']=row['configured_adc_relative_error']<=row['accuracy_target']
 Path(__file__).with_name('joint_spice_results.json').write_text(json.dumps(dict(
  scope='Combined behavioral transients, not measured hardware or a certified corner envelope',runs=rows),indent=2)+'\n')
 print('PASS',len(rows),'joint timed cases; guards and timestep comparison')
if __name__=='__main__':main()
