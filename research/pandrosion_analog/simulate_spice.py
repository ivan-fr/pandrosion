"""Behavioral sampled-analog AD prototype. Requires ngspice, numpy.
B sources are abstract arithmetic cells, NOT a transistor design or a PDK model.
"""
from pathlib import Path
import subprocess,shutil,json,tempfile
import numpy as np
OUT=Path(__file__).parent
NG=shutil.which('ngspice') or '/opt/homebrew/bin/ngspice'

def netlist(p=3,m=2.,calc_us=8.,gain=0.,offset=0.,cycles=8,mode="AD"):
 assert p>=2 and 1<=m<=2 and calc_us>0
 alpha=(p-1)/(p+1);T=(2*calc_us+4)*1e-6;acq=.8e-6
 ta=calc_us*1e-6;tb=ta+2e-6;end=cycles*T
 lines=[f'{mode} sampled analog behavioral prototype p={p}, m={m}',
 '* 1 V represents one dimensionless unit. Arithmetic is behavioral.',
 '* Two nonoverlapping track/hold phases; no continuous-loop Halley claim.',
 '.options reltol=1e-7 abstol=1e-12 vntol=1e-9 method=gear',
 f'Vm m 0 {m:.17g}',
 f'Va clk_a 0 PULSE(0 3 {ta:.12g} 5n 5n {acq:.12g} {T:.12g})',
 f'Vb clk_b 0 PULSE(0 3 {tb:.12g} 5n 5n {acq:.12g} {T:.12g})',
 '.model holdsw SW(Ron=100 Roff=1e12 Vt=1.5 Vh=0.1)',
 'Bsample_buffer sample_drive 0 V=v(next)','Sa sample_drive candidate clk_a 0 holdsw','Ca candidate 0 100p IC=1','Ra candidate 0 1e12',
 '* Buffer avoids charge sharing between the two 100 pF memories.',
 'Bbuffer candidate_buffer 0 V=v(candidate)',
 'Sb candidate_buffer state clk_b 0 holdsw','Cs state 0 100p IC=1','Rs state 0 1e12']
 # A proportional product chain with 100 ns first-order cell response.
 prev='state'
 for j in range(2,p+1):
  lines += [f'Bmul{j} drive{j} 0 V=min(3,max(0,(1+{gain:.12g})*v({prev})*v(state)))',f'Rmul{j} drive{j} q{j} 1k',f'Cmul{j} q{j} 0 100p IC=1']
  prev=f'q{j}'
 def lp(name,expr,ic):
  lines.extend([f'B{name} d_{name} 0 V={expr}',f'R{name} d_{name} {name} 1k',f'C{name} {name} 0 100p IC={ic:.12g}'])
 if mode=='AD':
  lp('residual',f'v(m)*v(q{p})',m)
  lp('num',f'1+{alpha:.17g}*v(residual)',1+alpha*m)
  lp('den',f'{alpha:.17g}+v(residual)',alpha+m)
  upper=1.2
 else:
  assert mode=='Halley'
  lines.append(f'Bresidual residual 0 V=v(m)/max(v(q{p}),0.1)')
  lp('num',f'{alpha:.17g}*v(q{p})+v(m)',alpha+m)
  lp('den',f'v(q{p})+{alpha:.17g}*v(m)',1+alpha*m)
  upper=2.
 lp('next',f'min({upper},max(0.5,v(state)*v(num)/max(v(den),0.1)+{offset:.12g}))',1)
 # Readouts are ideal observation ports with no assigned cell bandwidth.
 prior='state' if p==2 else f'q{p-1}'
 if mode=='AD':
  lines += ['Binverse y_inverse 0 V=1/max(v(state),0.1)',f'Bgeometry y_geometry 0 V=v(m)*v({prior})']
 else:
  lines += ['Binverse y_inverse 0 V=v(state)','Bgeometry y_geometry 0 V=v(state)']
 lines += [
 '.control','set noaskquit','set wr_singlescale','set wr_vecnames','set numdgt=15',
 f'tran 20n {end:.12g} 0 20n uic',
 'wrdata waveform.txt v(state) v(candidate) v(next) v(y_inverse) v(y_geometry) v(residual) v(clk_a) v(clk_b)',
 'quit','.endc','.end']
 return '\n'.join(lines)+'\n',T,tb

def run_case(p,m,calc_us=8.,gain=0.,offset=0.,keep=False,mode="AD"):
 deck,T,tb=netlist(p,m,calc_us,gain,offset,mode=mode)
 with tempfile.TemporaryDirectory(prefix='ad_spice_') as tmp:
  work=Path(tmp);(work/'core.cir').write_text(deck)
  proc=subprocess.run([NG,'-b','core.cir'],cwd=work,capture_output=True,text=True,timeout=90)
  log=proc.stdout+proc.stderr
  if proc.returncode or not(work/'waveform.txt').exists():raise RuntimeError(log)
  dat=np.loadtxt(work/'waveform.txt',skiprows=1)
  if keep:
   (OUT/'ad_core_p3.cir').write_text(deck);(OUT/'spice_nominal.log').write_text(log)
   # Downsample plot copy; keep clock edges sufficiently resolved.
   np.savetxt(OUT/'spice_waveform.csv',dat[::5],delimiter=',',header='time,state,candidate,next,inverse,geometry,residual,clock_a,clock_b',comments='')
 samples=[];ideal=1.;r=m**(1/p)
 for n in range(1,9):
  if mode=='AD':ideal=ideal*(p+1+(p-1)*m*ideal**p)/(p-1+(p+1)*m*ideal**p)
  else:ideal=ideal*((p-1)*ideal**p+(p+1)*m)/((p+1)*ideal**p+(p-1)*m)
  when=n*T-1e-6;v=np.array([np.interp(when,dat[:,0],dat[:,j])for j in range(1,9)])
  samples.append({'iteration':n,'time_us':when*1e6,'state':float(v[0]),'ideal_state':ideal,'state_error':float(v[0]-ideal),'inverse_error':float(v[3]/r-1),'geometry_error':float(v[4]/r-1),'residual':float(v[5])})
 return {'mode':mode,'p':p,'m':m,'calc_us':calc_us,'period_us':T*1e6,'multiplier_gain_error':gain,'update_offset_volts':offset,'samples':samples,'max_abs_state_deviation':max(abs(s['state_error'])for s in samples),'final_inverse_error':samples[-1]['inverse_error'],'final_geometry_error':samples[-1]['geometry_error']}

def main():
 OUT.mkdir(exist_ok=True)
 results=[]
 for p in [2,3,4,8,16]:
  for m in [1.,1.25,1.5,2.]:
   row=run_case(p,m,keep=(p==3 and m==2))
   assert row['max_abs_state_deviation']<2e-5,(p,m,row)
   assert abs(row['final_inverse_error'])<1e-5,(p,m,row)
   results.append(row)
 print('Nominal:',len(results),'passed; max state deviation',max(x['max_abs_state_deviation']for x in results),flush=True)
 corners=[run_case(p,2.,gain=g,offset=o)for p in [3,16] for g,o in [(1e-3,0),(0,5e-4)]]
 timing=[run_case(16,2.,calc_us=t)for t in [.25,1.,2.,8.]]
 controls=[run_case(p,2.,mode='Halley')for p in [3,16]]
 for row in controls:assert row['max_abs_state_deviation']<2e-5
 (OUT/'halley_control_p3.cir').write_text(netlist(3,2.,mode='Halley')[0])
 report={'controls':controls,'status':'passed','simulator':subprocess.run([NG,'--version'],capture_output=True,text=True).stdout,'scope':'Behavioral cells + RC bandwidth + two switched capacitors and two ideal isolation buffers; no transistor, process, power or silicon timing claim.','nominal':results,'mismatch_corners':corners,'timing_sweep':timing}
 (OUT/'spice_results.json').write_text(json.dumps(report,indent=2)+'\n')
 print('Corners and timing:',len(corners)+len(timing),'runs complete',flush=True)
if __name__=='__main__':main()
