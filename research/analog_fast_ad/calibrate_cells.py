"""Electrical-input cell calibration in ngspice; never evaluates a root to fit trims.
Finite measurement noise and 24-bit programmable compensation. No PDK model.
"""
from pathlib import Path
import json, subprocess, tempfile
import numpy as np
from model import schedule,prepare
from spice import run
from joint_spice import config
OUT=Path(__file__).parent

def calibrate(p,cfg,seed=42):
 ops=schedule(p)
 rnd=lambda v:np.rint(np.asarray(v)*2**24)/2**24
 cf=lambda v:round(v*2**cfg['coeff_bits'])/2**cfg['coeff_bits']
 lines=['Centered cell electrical calibration','.options reltol=1e-10','Vd d 0 0','Vq q 0 0']
 specs=[]
 # Each cell is independently stimulated with known electrical voltages.
 specs.append(('read',f'v(d)+{cfg["offset"]}',[0,1],np.array([0.,1.])))
 for i,op in enumerate(ops):
  w=cf(op['product_weight'])
  if op['kind']=='square':
   expr=f'v(d)+{w}*((1+{cfg["gain"]})*v(d)*v(d)+{cfg["offset"]})+{cfg["offset"]}'
   specs.append((f'cell{i}',expr,[0,1,3],np.array([0.,1.,op['product_weight']])))
  else:
   v=cf(op['copy_weight'])
   expr=f'v(d)+{v}*(v(q)-v(d))+{w}*((1+{cfg["gain"]})*v(d)*v(q)+{cfg["offset"]})+{cfg["offset"]}'
   specs.append((f'cell{i}',expr,[0,1,2,4],np.array([0.,1-op['copy_weight'],op['copy_weight'],op['product_weight']])))
 specs.append(('target',f'(1+{cfg["target_gain"]})*v(d)+{cfg["target_offset"]}',[0,1],np.array([0.,1.])))
 for name,expr,_,_ in specs:
  lines += [f'B{name} {name}_drive 0 V={expr}',f'R{name} {name}_drive {name} 10',f'Rload{name} {name} 0 {1e12 if name=="target" else cfg["rin"]}']
 names=' '.join(f'v({name})' for name,_,_,_ in specs)
 lines += ['.control','set numdgt=16','set wr_singlescale','set wr_vecnames','dc Vd -0.7 0.1 0.1 Vq -0.7 0.1 0.1',f'wrdata measured.txt v(d) v(q) {names}','quit','.endc','.end']
 with tempfile.TemporaryDirectory() as tmp:
  path=Path(tmp);(path/'cal.cir').write_text('\n'.join(lines)+'\n')
  proc=subprocess.run(['ngspice','-b','cal.cir'],cwd=path,capture_output=True,text=True,timeout=90)
  if proc.returncode:raise RuntimeError(proc.stdout+proc.stderr)
  raw=np.loadtxt(path/'measured.txt',skiprows=1)
 rng=np.random.default_rng(seed)
 measured=rnd(raw[:,3:]+rng.normal(0,.1e-6,raw[:,3:].shape))
 d,q=raw[:,1:3].T;basis=np.array([np.ones(len(d)),d,q,d*d,d*q]).T
 compensation=[];report=[];read=None;target=None
 for j,(name,_,indices,ideal) in enumerate(specs):
  A=basis[:,indices];coeff=np.linalg.lstsq(A,measured[:,j],rcond=None)[0]
  # d coefficient supplies the output attenuation, with known copy weight removed.
  attenuation=coeff[1]/ideal[1]
  assert .95<attenuation<1.05
  correction=rnd((ideal-coeff)/attenuation)
  if name=='read':read=correction.tolist()
  elif name=='target':target=rnd(coeff).tolist()
  else:
   full=np.zeros(5);full[indices]=correction;compensation.append(full.tolist())
  report.append(dict(cell=name,fit_rms_V=float(np.sqrt(np.mean((A@coeff-measured[:,j])**2))),
   measured_coefficients=coeff.tolist(),source_compensation=correction.tolist()))
 return dict(read_compensation=read,stage_compensation=compensation,target_calibration=target),report

def main():
 rows=[]
 for r in prepare([[3,500000],[1000000,500000]]):
  base=config('untrimmed',25,1,20260921)
  trims,measurements=calibrate(r['p'],base)
  # Do not call the tight-profile assumptions a achieved result; retain original devices.
  # ADC, noise, leakage, switch and charge errors remain active before/after calibration.
  raw=run(r,config=base)
  calibrated=run(r,config={**base,**trims})
  hotcfg=config('untrimmed',85,1,20260921)
  hot=run(r,config={**hotcfg,**trims})
  hottrims,hotmeasurements=calibrate(r['p'],hotcfg,seed=43)
  recalibrated=run(r,config={**hotcfg,**hottrims})
  assert calibrated['configured_adc_relative_error']<raw['configured_adc_relative_error']
  rows.append(dict(p=r['p'],X=r['originalX'],training_points_per_cell=81,
   measurement_noise_rms_V=.1e-6,measurement_fraction_bits=24,measurements=measurements,
   compensation=trims,uncalibrated=raw,calibrated_25C=calibrated,calibrated_85C=hot,recalibrated_85C=recalibrated,hot_compensation=hottrims,hot_measurements=hotmeasurements))
  print(r['p'],'before',raw['configured_adc_relative_error'],'after',calibrated['configured_adc_relative_error'],'hot',hot['configured_adc_relative_error'],'recalibrated hot',recalibrated['configured_adc_relative_error'],flush=True)
 (OUT/'calibration_results.json').write_text(json.dumps(dict(scope='Simulated electrical-reference calibration with additional programmable compensation paths; not measured hardware',runs=rows),indent=2)+'\n')
 print('PASS simulated calibration, retained-error and temperature checks')
if __name__=='__main__':main()
