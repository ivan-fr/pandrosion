"""Paired behavioral AD correction cells on the unchanged V30 power/memory circuit.
The direct comparator and feedback have two equally loaded one-pole cells.
Their behavioral sources are not transistor models or energy/area models.
"""
from pathlib import Path
import json, math, subprocess, sys, tempfile, time
import mpmath as mp
import numpy as np
HERE=Path(__file__).resolve().parent
BASE=HERE.parent/'analog_fast_ad'
sys.path.insert(0,str(BASE))
import spice
from model import decode
from simulation_runtime import spice_timeout
VARIANTS=('legacy','direct','feedback')

def execute(text):
 with tempfile.TemporaryDirectory(prefix='pandrosion-ad-cell-') as tmp:
  path=Path(tmp);(path/'test.cir').write_text(text)
  start=time.monotonic()
  proc=subprocess.run(['ngspice','-b','test.cir'],cwd=path,text=True,capture_output=True,timeout=spice_timeout())
  if proc.returncode:raise RuntimeError((proc.stdout+proc.stderr)[-4000:])
  wave=np.loadtxt(path/'wave.txt',skiprows=1)
 return wave,proc.stdout+proc.stderr,time.monotonic()-start

def calibrate_correction(cfg,seed):
 """Known electrical references only, 81 levels; affine error model explicitly assumed.
 A matched unity reference estimates output loading, like the existing cell bench.
 """
 g=cfg['gain'];o=cfg['offset'];rin=cfg['rin']
 lines=['Correction-cell electrical calibration','.options reltol=1e-10','Vref f 0 0',
  'Bref load_drive 0 V=v(f)','Rref load_drive load 10',f'Rrefload load 0 {rin}']
 for i in range(2):
  lines += [f'Bc{i} c{i}_drive 0 V=(1+({g:.17g}))*v(f)+({o:.17g})',
    f'Rc{i} c{i}_drive c{i} 10',f'Rl{i} c{i} 0 {rin}']
 lines += ['.control','set numdgt=16','set wr_singlescale','set wr_vecnames',
  'dc Vref -1 1.8 .035','wrdata wave.txt v(f) v(load) v(c0) v(c1)','quit','.endc','.end']
 data,_,_=execute('\n'.join(lines)+'\n')
 rng=np.random.default_rng(seed)
 x=data[:,1];basis=np.column_stack([np.ones(len(x)),x])
 vals=np.rint((data[:,2:]+rng.normal(0,.1e-6,data[:,2:].shape))*2**24)/2**24
 load=np.linalg.lstsq(basis,vals[:,0],rcond=None)[0][1]
 trims=[];reports=[]
 for i in range(2):
  fit=np.linalg.lstsq(basis,vals[:,i+1],rcond=None)[0]
  trim=np.rint((np.array([0.,1.])-fit)/load*2**24)/2**24
  trims.append(trim.tolist());reports.append(dict(fit=fit.tolist(),trim=trim.tolist(),rms=float(np.sqrt(np.mean((basis@fit-vals[:,i+1])**2)))))
 return trims,dict(points=len(x),measurement_noise_rms_V=.1e-6,programming_fraction_bits=24,load_gain=load,cells=reports)

def correction_lines(p,cfg,variant,w='(v(residual)-1)',q='v(q)'):
 bits=cfg.get('coeff_bits');invp=round((1/p)*2**bits)/2**bits if bits else 1/p
 aa=(1+invp)/2;bb=f'(1+({invp:.17g})*({q}))'
 g=cfg.get('correction_gain',cfg['gain']);o=cfg.get('correction_offset',cfg['offset'])
 cap=cfg['stage_cap']*cfg.get('correction_tau_scale',1.)
 trims=cfg.get('correction_calibration',[[0.,0.],[0.,0.]])
 lines=[];drives=[]
 def stage(name,expr,i):
  c0,c1=trims[i]
  raw=f'((1+({g:.17g}))*({expr})+({o:.17g})+({c0:.17g})+({c1:.17g})*({expr}))'
  if cfg.get('correction_noise_rms',0):raw+=f'+v(cornoise{i})'
  lines.extend([f'B{name} {name}_drive 0 V=min(2,max(-2,{raw}))',
   f'R{name} {name}_drive {name} 10',f'C{name} {name} 0 {cap:.17g}',
   f'Rport_{name} {name} 0 {cfg["rin"]}',f'Cport_{name} {name} 0 2p'])
  # Monitor the pre-clipped target too; saturation must not be hidden by the clamp.
  mon=f'{name}_raw';lines.append(f'B{mon} {mon} 0 V={raw}');drives.append(f'abs(v({mon}))')
 if variant=='direct':
  stage('corr_first',f'-({w})*{bb}',0)
  stage('delta',f'v(corr_first)/max(.125,1+({aa:.17g})*({w}))',1)
 elif variant=='feedback':
  stage('corr_first',f'{bb}+({aa:.17g})*v(delta)',0)
  stage('delta',f'-({w})*v(corr_first)',1)
 else:raise ValueError(variant)
 lines += [f'Bcorpeak corpeak 0 V=max({drives[0]},{drives[1]})',
  f'Binnerden innerden 0 V=1+({aa:.17g})*({w})']
 return lines

def deck(r,cfg,variant,step='1u'):
 base=spice.deck(r['p'],r['Y'],config=cfg,step=step)
 if variant=='legacy':return base
 lines=base.splitlines();idx=next(i for i,s in enumerate(lines) if s.startswith('Btarget '))
 expression=f'(v(q)+v(delta))*(1+({cfg["target_gain"]:.17g}))+({cfg["target_offset"]:.17g})'
 if cfg['noise_rms']:expression+='+v(targetnoise)'
 if cfg.get('target_calibration'):
  a,b=cfg['target_calibration'];expression=f'(({expression})-({a:.17g}))/({b:.17g})'
 lines[idx]=f'Btarget target 0 V={expression}'
 ctrl=lines.index('.control');extra=correction_lines(r['p'],cfg,variant)
 if cfg.get('correction_noise_rms',0):
  duration=cfg['cycles']*cfg['period_us']*1e-6
  count=round(duration/10e-6)+1;knots=np.linspace(0,duration,count)
  rng=np.random.default_rng(cfg['noise_seed']+900)
  for i in range(2):
   pairs=' '.join(f'{t:.17g} {v:.17g}' for t,v in zip(knots,rng.normal(0,cfg['correction_noise_rms'],count)))
   extra.append(f'Vcornoise{i} cornoise{i} 0 PWL({pairs})')
 lines[ctrl:ctrl]=extra
 for i,line in enumerate(lines):
  if line.startswith('wrdata wave.txt '):lines[i]+=' v(delta) v(corr_first) v(corpeak) v(innerden)'
 return '\n'.join(lines)+'\n'

def score(r,cfg,data):
 period=cfg['period_us'];cycles=cfg['cycles']
 read=cfg['update_start_us']+cfg['update_width_us']+cfg.get('read_delay_us',15.)
 times=np.array([read+period*i for i in range(cycles)])*1e-6
 raw=np.interp(times,data[:,0],data[:,1]);lsb=4/2**cfg['adc_bits']
 observed=raw*(1+cfg['adc_gain'])+cfg['adc_offset']
 inl=cfg['adc_inl_lsb']*lsb
 if cfg.get('adc_inl_period_V',0):inl*=np.sin(2*np.pi*raw/cfg['adc_inl_period_V'])
 observed+=inl
 converted=np.rint(observed/lsb)*lsb
 if cfg.get('adc_calibration'):
  a,b=cfg['adc_calibration'];converted=(converted-a)/b
 mp.mp.dps=90;ref=mp.exp(mp.log(mp.mpf(r['originalX']))/r['p'])
 def error(q):return float(abs(mp.mpf(decode(r['c'],q,r['p']))/ref-1))
 points=[]
 for n in [2,3,4,6,8,12,20]:
  if n>cycles:continue
  for avg in [1,2,4,8,16]:
   if avg>n or (avg>1 and n-avg<2):continue
   q=float(np.mean(converted[n-avg:n]));points.append(dict(iterations=n,average=avg,time_ms=float(times[n-1]*1000),error=error(q)))
 guards=[]
 if data[:,5].min()<=.25:guards.append('denominator floor')
 if abs(data[:,6]).max()>=2:guards.append('candidate clamp')
 if data[:,7].max()>=1.99:guards.append('power clamp/margin')
 if abs(observed).max()>=2:guards.append('ADC range')
 if data.shape[1]>8:
  if data[:,10].max()>=1.99:guards.append('correction clamp/margin')
  if data[:,11].min()<=.125:guards.append('inner denominator floor')
 return dict(status='rejected' if guards else 'ok',guards=guards,
  points=points,q_samples=raw.tolist(),configured_adc_samples=converted.tolist(),
  denominator_min=float(data[:,5].min()),power_peak=float(data[:,7].max()),
  target_peak=float(abs(data[:,6]).max()),correction_peak=float(data[:,10].max()) if data.shape[1]>8 else None,
  initial_error=error(0.))

def run(r,cfg,variant,step='1u',keep=None):
 text=deck(r,cfg,variant,step)
 data,log,elapsed=execute(text)
 result=score(r,cfg,data)
 if keep:
  path=Path(keep);path.parent.mkdir(parents=True,exist_ok=True)
  path.with_suffix('.cir').write_text(text);path.with_suffix('.log').write_text(log)
  np.savetxt(path.with_suffix('.csv'),data[::max(1,len(data)//2400)],delimiter=',',
   header='time,state,q,residual,candidate,denominator,target,stagepeak'+(',delta,first,corpeak,innerden' if variant!='legacy' else ''),comments='')
 return dict(variant=variant,step=step,wall_seconds=elapsed,**result)

if __name__=='__main__':
 from model import prepare
 from revised_circuit import prepare_revision
 r=prepare([[3,2]])[0];cfg,cal=prepare_revision(3,25,1,20269190)
 trims,internal=calibrate_correction(cfg,20269191);cfg['correction_calibration']=trims
 cfg.update(cycles=6,output_average_count=2)
 for variant in VARIANTS:
  row=run(r,cfg,variant,keep=HERE/'examples'/f'pilot_{variant}')
  print(variant,row['status'],row['points'][-1],round(row['wall_seconds'],2),flush=True)
  if variant=='legacy':
   reference=spice.run(r,config=cfg,step='1u')
   assert np.max(np.abs(np.array(row['q_samples'])-reference['q_samples']))<1e-12
   point=next(x for x in row['points'] if x['iterations']==cfg['cycles'] and x['average']==cfg['output_average_count'])
   assert abs(point['error']-reference['configured_adc_relative_error'])<1e-14
 print('PASS: baseline deck/scoring agrees with archived V30 runner')
