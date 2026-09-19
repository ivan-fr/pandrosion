"""Finite-current, two-edge charge memory model; geometry/power arithmetic unchanged."""
from pathlib import Path
import sys, math, json,subprocess,tempfile,time
import numpy as np
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent))
import circuit
from revised_circuit import revision,calibrate_adc
from calibrate_cells import calibrate
from model import prepare

PROFILES=[dict(name='control100',memory_cap=100e-9,switch_ron=230.,edge_charge=.5e-12,parasitic=2e-12),
 dict(name='small33',memory_cap=33e-9,switch_ron=230.,edge_charge=.5e-12,parasitic=2e-12),
 dict(name='small10',memory_cap=10e-9,switch_ron=230.,edge_charge=.5e-12,parasitic=2e-12),
 dict(name='small1',memory_cap=1e-9,switch_ron=230.,edge_charge=.5e-12,parasitic=2e-12),
 dict(name='lowR100',memory_cap=100e-9,switch_ron=23.,edge_charge=5e-12,parasitic=20e-12),
 dict(name='lowR10',memory_cap=10e-9,switch_ron=23.,edge_charge=5e-12,parasitic=20e-12)]
SCHEDULES=[dict(name='precision',start=350.,width=400.,gap=20.,period=1200.),
 dict(name='acquire120',start=150.,width=120.,gap=10.,period=420.),
 dict(name='acquire50',start=150.,width=50.,gap=10.,period=280.),
 dict(name='acquire20',start=150.,width=20.,gap=10.,period=220.)]

def execute(text):
 with tempfile.TemporaryDirectory(prefix='pandrosion-memory-') as tmp:
  path=Path(tmp);(path/'test.cir').write_text(text);start=time.monotonic()
  proc=subprocess.run(['ngspice','-b','test.cir'],cwd=path,text=True,capture_output=True,timeout=circuit.spice_timeout())
  log=proc.stdout+proc.stderr
  if proc.returncode or not (path/'wave.txt').exists():raise RuntimeError(log[-4000:])
  wave=np.loadtxt(path/'wave.txt',skiprows=1)
 return wave,log,time.monotonic()-start

def driver_expression(src,dst,cfg):
 i=cfg['driver_limit_A'];r=cfg['driver_rout']
 return f'{i:.17g}*tanh((v({src})-v({dst}))/({i*r:.17g}))'

def driver(name,src,dst,cfg):
 return f'B{name} {src} {dst} I='+driver_expression(src,dst,cfg)

def clocks(cfg):
 ss=cfg['sample_start_us'];sw=cfg['sample_width_us'];us=cfg['update_start_us'];uw=cfg['update_width_us'];per=cfg['period_us']
 return [f'.model SW SW(Ron={cfg["switch_ron"]} Roff=1e12 Vt=0.5 Vh=0.1)',
  f'Vsample sample 0 PULSE(0 1 {ss}u 10n 10n {sw}u {per}u)',
  f'Vupdate update 0 PULSE(0 1 {us}u 10n 10n {uw}u {per}u)',
  'Vreset reset 0 PULSE(1 0 10u 10n 10n 1 2)']

def memory(cfg,tag='',thermal=True,trim=True):
 def node(s):return tag+s
 stored=node('stored');state=node('state');read=node('stored_read');drive=node('stored_drive')
 C=cfg['memory_cap']+cfg['parasitic'];per=cfg['period_us'];duration=per*cfg['cycles']
 expr=f'v({stored})'
 if trim and cfg.get('memory_calibration'):
  a,b=cfg['memory_calibration'];expr=f'({expr}-({a:.17g}))/({b:.17g})'
 lines=[f'S{tag}reset {state} 0 reset 0 SW',f'C{tag}state {state} 0 {C:.17g} IC=0',
  f'R{tag}leak {state} 0 1e12',f'I{tag}leak {state} 0 {cfg["leak"]-cfg.get("leak_compensation_A",0):.17g}',
  f'C{tag}next {stored} 0 {C:.17g} IC=0',f'R{tag}next {stored} 0 1e12',
  f'S{tag}sample {node("candidate")} {stored} sample 0 SW',f'S{tag}update {read} {state} update 0 SW',
  f'B{tag}stored {drive} 0 V={expr}',driver(tag+'drive_stored',drive,read,cfg),f'C{tag}buffer {read} 0 100n']
 releases=[cfg['sample_start_us']+cfg['sample_width_us'],cfg['update_start_us']+cfg['update_width_us']]
 for name,dst,release in zip(['sample','update'],[stored,state],releases):
  edge=node('edge_'+name);amp=cfg['charge']/10e-9;curv=cfg['charge_curvature']
  lines += [f'V{edge} {edge} 0 PULSE(0 1 {release+.02:.17g}u 1n 1n 9n {per}u)',
   f'B{tag}charge_{name} 0 {dst} I=v({edge})*({amp:.17g})*(1+({curv:.17g})*(v({dst})/.7)^2)']
 if thermal:
  for i,dv in enumerate(np.random.default_rng(cfg['noise_seed']+1).normal(0,cfg['sample_noise_rms'],cfg['cycles'])):
   release=releases[1]+.02+per*i
   lines.append(f'I{tag}thermal{i} 0 {state} PULSE(0 {dv*C/10e-9:.17g} {release:.17g}u 1n 1n 9n {2*duration}u)')
 return lines

def calibrate_memory(cfg,seed):
 refs=np.array([-.7,-.43,-.16,.11]);read=cfg['update_start_us']+cfg['update_width_us']+15
 lines=['Finite-current memory electrical calibration','.options reltol=1e-8 abstol=1e-13 vntol=1e-10',*clocks(cfg)]
 for j,v in enumerate(refs):
  tag=f'b{j}_';src=tag+'candidate_drive';dst=tag+'candidate'
  lines += [f'Vref{j} {src} 0 {v}',driver(tag+'drive_candidate',src,dst,cfg),f'Cc{j} {dst} 0 100n']
  lines += memory(cfg,tag,thermal=False,trim=False)
 lines += ['.control','set numdgt=16','set wr_singlescale','set wr_vecnames',f'tran .25u {read+102}u uic',
  'wrdata wave.txt '+' '.join(f'v(b{j}_state)' for j in range(len(refs))),'quit','.endc','.end']
 data,_,_=execute('\n'.join(lines)+'\n')
 rng=np.random.default_rng(seed)
 measure=lambda t:np.array([np.interp(t*1e-6,data[:,0],data[:,j+1])for j in range(len(refs))])+rng.normal(0,.1e-6,len(refs))
 measured=measure(read);later=measure(read+100)
 estimate=-(cfg['memory_cap']+cfg['parasitic'])*float(np.mean(later-measured))/100e-6
 basis=np.column_stack([np.ones(len(refs)),refs]);fit=np.linalg.lstsq(basis,measured,rcond=None)[0]
 if not .5<fit[1]<1.5:raise ValueError('Unusable memory calibration gain')
 return fit.tolist(),dict(references=refs.tolist(),measurements=measured.tolist(),fit=fit.tolist(),
  fit_rms_V=float(np.sqrt(np.mean((basis@fit-measured)**2))),measurement_noise_rms_V=.1e-6,
  estimated_residual_leak_A=estimate,later_measurements=later.tolist())

def configure(p,temp,sign,seed,profile,timing,overrides=None):
 cfg=revision(temp,sign,seed);cfg.update(profile)
 cfg.update(charge=sign*profile['edge_charge'],charge_curvature=.1,driver_limit_A=.002,driver_rout=10.,cycles=12,
  sample_start_us=timing['start'],sample_width_us=timing['width'],update_start_us=timing['start']+timing['width']+timing['gap'],
  update_width_us=timing['width'],period_us=timing['period'])
 cfg.update(overrides or {})
 cfg['sample_noise_rms']=math.sqrt(2*1.380649e-23*(temp+273.15)/(cfg['memory_cap']+cfg['parasitic']))
 trims,cells=calibrate(p,cfg,seed+1);cfg.update(trims)
 _,probe=calibrate_memory(cfg,seed+2)
 estimate=probe['estimated_residual_leak_A']
 if abs(estimate)>=1e-6:raise ValueError('Leak compensation out of range')
 cfg['leak_compensation_A']=round(estimate/2e-12)*2e-12
 cfg['memory_calibration'],mem=calibrate_memory(cfg,seed+4)
 cfg['adc_calibration'],adc=calibrate_adc(cfg,seed+3)
 cfg['correction_calibration'],inner=circuit.calibrate_correction(cfg,seed+901)
 cfg['correction_noise_rms']=cfg['noise_rms']
 return cfg,dict(cells=cells,leak_probe=probe,memory=mem,adc=adc,correction=inner)

def deck(case,cfg,variant,step='1u'):
 original=circuit.deck(case,cfg,variant,step)
 remove=('Sreset ','Cstate ','Rleak ','Ileak ','Cnext ','Rnext ','Ssample ','Supdate ','Bstored ','Icharge ','Ithermal','Rcandidate ')
 lines=[s for s in original.splitlines() if not s.startswith(remove)]
 idx=lines.index('.control')
 lines[idx:idx]=memory(cfg)+[driver('drive_candidate','candidate_drive','candidate',cfg),
  'Bmonitor_c monitor_c 0 V='+driver_expression('candidate_drive','candidate',cfg),
  'Bmonitor_s monitor_s 0 V='+driver_expression('stored_drive','stored_read',cfg)]
 for i,s in enumerate(lines):
  if s.startswith('wrdata wave.txt '):lines[i]+=' v(stored) v(stored_read) v(monitor_c) v(monitor_s)'
 return '\n'.join(lines)+'\n'

def run(case,cfg,variant='legacy',step='1u',keep=None):
 text=deck(case,cfg,variant,step);data,log,elapsed=execute(text)
 cols=8 if variant=='legacy' else 12
 result=circuit.score(case,cfg,data[:,:cols]);cur=data[:,cols+2:cols+4]
 duty=[]
 for j in range(2):
  mask=(np.abs(cur[:,j])>.95*cfg['driver_limit_A']).astype(float)
  duty.append(float(np.trapezoid(mask,data[:,0])/data[-1,0]))
 if keep:
  path=Path(keep);path.parent.mkdir(parents=True,exist_ok=True)
  path.with_suffix('.cir').write_text(text);path.with_suffix('.log').write_text(log)
  header='time,state,q,residual,candidate,denominator,target,stagepeak'+(',delta,first,corpeak,innerden' if variant=='feedback'else '')+',stored,stored_read,candidate_current_A,transfer_current_A'
  np.savetxt(path.with_suffix('.csv'),data[::max(1,len(data)//1800)],delimiter=',',header=header,comments='')
 return dict(variant=variant,step=step,wall_seconds=elapsed,**result,
  driver_peak_A=np.max(abs(cur),axis=0).tolist(),current_limit_duty=duty,
  memory_cap_F=cfg['memory_cap'],sample_noise_rms_V=cfg['sample_noise_rms'])

if __name__=='__main__':
 case=prepare([[3,2]])[0]
 for prof in [PROFILES[0],PROFILES[2]]:
  for timing in [SCHEDULES[0],SCHEDULES[2]]:
   cfg,cal=configure(3,85,1,20269930,prof,timing)
   result=run(case,cfg,keep=HERE/'examples'/f'pilot_{prof["name"]}_{timing["name"]}')
   assert result['status']=='ok'
   error=result['points'][-1]['error']
   if prof['name']=='control100' and timing['name']=='acquire50':assert error>.01
   else:assert error<2e-6
   print(prof['name'],timing['name'],result['status'],result['points'][-1],cal['memory']['fit_rms_V'],flush=True)
