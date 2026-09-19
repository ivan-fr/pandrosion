"""Precision revision: measured trims, larger memory, matched acquisition and averaging.
Same imposed analog errors; actual extra components/noise of compensation are unmodeled.
"""
from simulation_runtime import spice_timeout
from pathlib import Path
import json,tempfile,subprocess,math
import numpy as np
from model import prepare
from spice import run
from joint_spice import config
from calibrate_cells import calibrate
OUT=Path(__file__).parent

def revision(temp,sign,seed):
 cfg=config('untrimmed',temp,sign,seed)
 cfg.update(memory_cap=100e-9,sample_width_us=400.,update_start_us=770.,update_width_us=400.,
  period_us=1200.,cycles=20,output_average_count=16,switch_ron=230.,coeff_bits=24,adc_bits=24,
  adc_inl_period_V=.2,sample_noise_rms=math.sqrt(2*1.380649e-23*(temp+273.15)/100e-9))
 return cfg

def calibrate_memory(cfg,seed):
 """Four independent sample/hold cells with known electrical references, measured in ngspice."""
 refs=np.array([-.7,-.43,-.16,.11]);C=cfg['memory_cap'];period=cfg['period_us']
 ss=cfg.get('sample_start_us',350);sw=cfg['sample_width_us'];us=cfg['update_start_us'];uw=cfg['update_width_us']
 release=us+uw;read=release+15
 lines=['Memory calibration electrical bench','.options reltol=1e-9 abstol=1e-13 vntol=1e-10',
  f'.model SW SW(Ron={cfg["switch_ron"]} Roff=1e12 Vt=0.5 Vh=0.1)',
  f'Vs sample 0 PULSE(0 1 {ss}u 10n 10n {sw}u {period}u)',
  f'Vu update 0 PULSE(0 1 {us}u 10n 10n {uw}u {period}u)',
  'Vr reset 0 PULSE(1 0 10u 10n 10n 10m 20m)']
 for i,v in enumerate(refs):
  lines += [f'V{i} drive{i} 0 {v}',f'R{i} drive{i} candidate{i} 10',f'Cc{i} candidate{i} 0 100n',
   f'Ss{i} candidate{i} stored{i} sample 0 SW',f'Cs{i} stored{i} 0 {C}',f'Rs{i} stored{i} 0 1e12',
   f'B{i} read{i} 0 V=v(stored{i})',f'Su{i} read{i} state{i} update 0 SW',f'Cq{i} state{i} 0 {C}',
   f'Rq{i} state{i} 0 1e12',f'Sr{i} state{i} 0 reset 0 SW',f'Il{i} state{i} 0 {cfg["leak"]-cfg.get("leak_compensation_A",0)}',
   f'Ic{i} 0 state{i} PULSE(0 {cfg["charge"]/10e-9} {release+.02}u 1n 1n 9n {period}u)']
 lines+=['.control','set numdgt=16','set wr_singlescale','set wr_vecnames',f'tran .25u {read+102}u uic',
  'wrdata mem.txt '+' '.join(f'v(state{i})' for i in range(len(refs))),'quit','.endc','.end']
 with tempfile.TemporaryDirectory() as tmp:
  path=Path(tmp);(path/'mem.cir').write_text('\n'.join(lines)+'\n')
  p=subprocess.run(['ngspice','-b','mem.cir'],cwd=path,capture_output=True,text=True,timeout=spice_timeout())
  if p.returncode:raise RuntimeError(p.stdout+p.stderr)
  a=np.loadtxt(path/'mem.txt',skiprows=1)
 measured=np.array([np.interp(read*1e-6,a[:,0],a[:,i+1]) for i in range(len(refs))])
 rng=np.random.default_rng(seed)
 measured+=rng.normal(0,.1e-6,len(refs))
 later=np.array([np.interp((read+100)*1e-6,a[:,0],a[:,i+1]) for i in range(len(refs))])+rng.normal(0,.1e-6,len(refs))
 leak_estimate=-C*float(np.mean(later-measured))/100e-6
 coeff=np.linalg.lstsq(np.column_stack([np.ones(len(refs)),refs]),measured,rcond=None)[0]
 return coeff.tolist(),dict(references=refs.tolist(),measurements=measured.tolist(),fit=coeff.tolist(),measurement_noise_rms_V=.1e-6,estimated_residual_leak_A=leak_estimate,later_measurements=later.tolist())

def calibrate_adc(cfg,seed):
 refs=np.linspace(-.73,.13,17);lsb=4/2**cfg['adc_bits']
 observed=refs*(1+cfg['adc_gain'])+cfg['adc_offset']+cfg['adc_inl_lsb']*lsb*np.sin(2*np.pi*refs/cfg['adc_inl_period_V'])
 observed+=np.random.default_rng(seed).normal(0,.1e-6,len(refs))
 observed=np.rint(observed/lsb)*lsb
 coeff=np.linalg.lstsq(np.column_stack([np.ones(len(refs)),refs]),observed,rcond=None)[0]
 return coeff.tolist(),dict(references=refs.tolist(),codes=observed.tolist(),fit=coeff.tolist())

def prepare_revision(p,temp,sign,seed):
 cfg=revision(temp,sign,seed)
 trims,cell_report=calibrate(p,cfg,seed=seed+1)
 _,leak_probe=calibrate_memory(cfg,seed+2)
 # Assumed additional programmable compensation source, 2 pA step and ±1 µA range.
 estimate=leak_probe['estimated_residual_leak_A']
 assert abs(estimate)<1e-6
 cfg['leak_compensation_A']=round(estimate/2e-12)*2e-12
 memory,memory_report=calibrate_memory(cfg,seed+4)
 adc,adc_report=calibrate_adc(cfg,seed+3)
 return {**cfg,**trims,'memory_calibration':memory,'adc_calibration':adc},dict(cells=cell_report,leak_probe=leak_probe,memory=memory_report,adc=adc_report)

def main():
 # Development inputs only. Independent validation is a separate executable.
 cases=prepare([[3,2],[3,500000],[1000000,500000]])
 rows=[]
 for r in cases:
  for temp in [25,85]:
   cfg,measurements=prepare_revision(r['p'],temp,1,20261001)
   result=run(r,step='1u',config=cfg)
   rows.append(dict(temperature_C=temp,calibration=measurements,**result))
   print(r['p'],r['originalX'],temp,result['configured_adc_relative_error'],flush=True)
 (OUT/'revised_development.json').write_text(json.dumps(dict(scope='Development set; not the independent validation campaign',runs=rows),indent=2)+'\n')
if __name__=='__main__':main()
