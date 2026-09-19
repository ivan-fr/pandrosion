"""Behavioral, clocked sample/hold SPICE prototype. No root/power oracle in deck.
Unrolled programmable stages, NOT a validated time-multiplexed transistor core.
"""
from pathlib import Path
import json,subprocess,tempfile,re
import numpy as np
import mpmath as mp
from model import prepare,schedule,decode
OUT=Path(__file__).parent

def deck(p,Y,stress=False,step='0.2u',config=None):
 offset=25e-6 if stress else 0.;gain=.001 if stress else 0.;rin=50000 if stress else 1e12;leak=5e-9 if stress else 0.
 cfg = dict(offset=offset,gain=gain,rin=rin,leak=leak,charge=0.,target_offset=0.,target_gain=0.,stage_cap=100e-9,timing_scale=1.,switch_ron=1.,coeff_bits=None,noise_rms=0.,noise_seed=0,
  adc_bits=18,adc_offset=0.,adc_gain=0.,adc_inl_lsb=0.,sample_noise_rms=0.)
 if config: cfg.update(config)
 offset,gain,rin,leak = (cfg[k] for k in ['offset','gain','rin','leak'])
 def coefficient(x):
  return round(x*2**cfg['coeff_bits'])/2**cfg['coeff_bits'] if cfg['coeff_bits'] else x
 Y=coefficient(Y);invp=coefficient(1/p)
 lines=['Fast AD centered state behavioral P5', '.options reltol=1e-7 abstol=1e-12 vntol=1e-9',
 f'.model SW SW(Ron={cfg["switch_ron"]} Roff=1e12 Vt=0.5 Vh=0.1)',
 'Vreset reset 0 PULSE(1 0 10u 10n 10n 10m 20m)',
 'Vsample sample 0 PULSE(0 1 350u 10n 10n 10u 500u)',
 'Vupdate update 0 PULSE(0 1 380u 10n 10n 10u 500u)',
 'Sreset state 0 reset 0 SW','Cstate state 0 10n IC=0','Rleak state 0 1e12',f'Ileak state 0 {leak}',
 'Cnext stored 0 10n IC=0','Rnext stored 0 1e12',
 'Ssample candidate stored sample 0 SW','Supdate stored_read state update 0 SW',
 'Bstored stored_read 0 V=v(stored)']
 if cfg['charge']:
  # Positive charge enters the state at the end of transfer. Area = charge.
  lines.append(f"Icharge 0 state PULSE(0 {cfg['charge']/(10e-9*cfg['timing_scale']):.17g} 390.02u 1n 1n 9n 500u)")
 if cfg['sample_noise_rms']:
  rng=np.random.default_rng(cfg['noise_seed']+1)
  for i,dv in enumerate(rng.normal(0,cfg['sample_noise_rms'],6)):
   current=dv*10e-9/(10e-9*cfg['timing_scale'])
   lines.append(f'Ithermal{i} 0 state PULSE(0 {current:.17g} {390.02+500*i:.17g}u 1n 1n 9n 10m)')
 # Reproducible colored disturbance: independent 10 us PWL knots at read and target.
 # RMS specifies knot values, not white-noise spectral density. Clock scaling scales bandwidth.
 if cfg['noise_rms']:
  rng=np.random.default_rng(cfg['noise_seed'])
  for node in ['readnoise','targetnoise']:
   knots=' '.join(f'{t*cfg["timing_scale"]:.17g} {v:.17g}' for t,v in
    zip(np.linspace(0,.003,301),rng.normal(0,cfg['noise_rms'],301)))
   lines.append(f'V{node} {node} 0 PWL({knots})')
 def stage(name,expr):
  lines.extend([f'B{name} {name}_drive 0 V=min(2,max(-2,({expr})))',f'R{name} {name}_drive {name} 10',f'C{name} {name} 0 {cfg["stage_cap"]:.17g}',f'Rport_{name} {name} 0 {rin}',f'Cport_{name} {name} 0 2p'])
 readexpr=f'v(state)+{offset}'
 if cfg['noise_rms']:readexpr+='+v(readnoise)'
 if cfg.get('read_compensation'):
  a,b=cfg['read_compensation'];readexpr+=f'+({a:.17g})+({b:.17g})*v(state)'
 stage('q',readexpr)
 prev='q'
 for i,op in enumerate(schedule(p)):
  name=f'd{i}';w=coefficient(op['product_weight'])
  if op['kind']=='square':expr=f'v({prev})+{w:.17g}*((1+{gain})*v({prev})*v({prev})+{offset})+{offset}'
  else:expr=f'v({prev})+{coefficient(op["copy_weight"]):.17g}*(v(q)-v({prev}))+{w:.17g}*((1+{gain})*v({prev})*v(q)+{offset})+{offset}'
  if cfg.get('stage_compensation'):
   a,b,c,d,e=cfg['stage_compensation'][i]
   expr+=f'+({a:.17g})+({b:.17g})*v({prev})+({c:.17g})*v(q)+({d:.17g})*v({prev})*v({prev})+({e:.17g})*v({prev})*v(q)'
  stage(name,expr);prev=name
 peak='abs(v(q_drive))'
 for i in range(len(schedule(p))):peak=f'max({peak},abs(v(d{i}_drive)))'
 lines.append(f'Bpeak stagepeak 0 V={peak}')
 lines.extend([f'Bres residual 0 V={Y:.17g}*(1+v({prev}))',f'Bden denominator 0 V=1+v(residual)+(v(residual)-1)*{invp:.17g}',
 f'Btarget target 0 V=(v(q)+2*(1+v(q)*{invp:.17g})*(1-v(residual))/max(0.25,v(denominator)))*(1+{cfg["target_gain"]})+{cfg["target_offset"]}'+('+v(targetnoise)' if cfg['noise_rms'] else ''),
 'Bcandidate candidate_drive 0 V=min(2,max(-2,v(target)))','Rcandidate candidate_drive candidate 10','Ccandidate candidate 0 100n',
 '.control','set numdgt=16','set wr_singlescale','set wr_vecnames',f'tran {step} 3m uic','wrdata wave.txt v(state) v(q) v(residual) v(candidate) v(denominator) v(target) v(stagepeak)', 'quit','.endc','.end'])
 if cfg.get('target_calibration'):
  a,b=cfg['target_calibration']
  lines=[f'Btarget target 0 V=(({line.split("V=",1)[1]})-({a:.17g}))/({b:.17g})'
         if line.startswith('Btarget ') else line for line in lines]
 if cfg['timing_scale'] != 1:
  # Scale only timing statements, never component values or current amplitudes.
  def scale_time(match):
   return f"{float(match[1])*cfg['timing_scale']:.17g}{match[2]}"
  lines = [re.sub(r'(?<![\w.])(\d+(?:\.\d+)?)([num])(?!\w)',scale_time,line)
           if 'PULSE(' in line or line.startswith('tran ') else line for line in lines]
 return '\n'.join(lines)+'\n'

def run(r,stress=False,step='0.2u',keep=None,config=None):
 text=deck(r['p'],r['Y'],stress,step,config)
 with tempfile.TemporaryDirectory(prefix='pandrosion-fast-ad-') as tmp:
  path=Path(tmp);(path/'test.cir').write_text(text)
  proc=subprocess.run(['ngspice','-b','test.cir'],cwd=path,text=True,capture_output=True,timeout=90)
  if proc.returncode:raise RuntimeError(proc.stdout+proc.stderr)
  a=np.loadtxt(path/'wave.txt',skiprows=1)
  if keep:
   (OUT/(keep+'.cir')).write_text(text)
   (OUT/(keep+'.log')).write_text(proc.stdout+proc.stderr)
   # Thin exported plot samples only; measurements below use full simulator output.
   np.savetxt(OUT/(keep+'.csv'),a[::20],delimiter=',',header='time,state,q,residual,candidate,denominator,target,stagepeak',comments='')
 mp.mp.dps=80
 timing_scale=(config or {}).get('timing_scale',1.)
 samples=[float(np.interp((405+500*i)*1e-6*timing_scale,a[:,0],a[:,1]))for i in range(6)]
 q=samples[-1];lsb=4/(2**18);adc=round(q/lsb)*lsb
 adc_cfg=config or {};adc_lsb=4/2**adc_cfg.get('adc_bits',18)
 observed=q*(1+adc_cfg.get('adc_gain',0))+adc_cfg.get('adc_offset',0)+adc_cfg.get('adc_inl_lsb',0)*adc_lsb
 assert abs(observed)<2, 'Configured ADC input outside the modeled range'
 converted=round(observed/adc_lsb)*adc_lsb
 ref=mp.exp(mp.log(mp.mpf(r['originalX']))/r['p'])
 result=dict(config=config or {},p=r['p'],X=r['originalX'],stress=stress,max_step=step,q_samples=samples,q_final=q,adc18_q=adc,
  decoded_relative_error=float(abs(mp.mpf(decode(r['c'],q,r['p']))/ref-1)),
  adc18_decoded_relative_error=float(abs(mp.mpf(decode(r['c'],adc,r['p']))/ref-1)),
  configured_adc_q=converted,
  configured_adc_relative_error=float(abs(mp.mpf(decode(r['c'],converted,r['p']))/ref-1)),
  stage_peak=float(a[:,7].max()),denominator_min=float(a[:,5].min()),target_peak=float(abs(a[:,6]).max()),
  final_hold_drift=float(np.interp(2980e-6*timing_scale,a[:,0],a[:,1])-np.interp(2905e-6*timing_scale,a[:,0],a[:,1])))
 assert result['denominator_min']>.25 and result['target_peak']<2 and result['stage_peak']<1.99,'Guard/clamp activated: cannot claim normal operation'
 return result

def main():
 cases=prepare([[3,2],[32,500000],[1000000,500000]])
 results=[]
 for r in cases:
  for stress in [False,True]:
   row=run(r,stress,keep=f'p{r["p"]}_{"stress" if stress else "ideal"}');results.append(row);print(row,flush=True)
 # Independent time-step check of the required million-degree example.
 check=run(cases[-1],True,'0.05u');results.append(check)
 coarse=results[-2]
 assert abs(check['q_final']-coarse['q_final'])<2e-5
 (OUT/'spice_results.json').write_text(json.dumps(dict(scope='Behavioral macros, ideal clock/control and programmed coefficients; not measured silicon or PDK',runs=results),indent=2)+'\n')
if __name__=='__main__':main()
