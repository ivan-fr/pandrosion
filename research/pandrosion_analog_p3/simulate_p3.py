"""P3 denominator servo: authored simplified Qu/Ru model, NOT AD734 vendor model."""
import json,re,subprocess,tempfile
from pathlib import Path
import numpy as np
from p2_base import deck as p2_deck,NG,V0
P=Path(__file__).parent
COUNT=0

def servo(ru=28000,cap=20e-12):
 return f'''
* Simplified internal transistor; parameters are assumptions, not AD734 process data.
.model QUAPP NPN(Is=1e-15 Bf=199 Vaf=100 Cje=2p Cjc=1p Tf=0.3n)
.subckt DEN cmd measured supply PARAMS: vos=25u
Xamp cmd measured base OA PARAMS: vo={{vos}}
Qden supply base measured QUAPP
Rden measured 0 {ru:.15g}
Rcomp base measured 2meg
Cpar measured 0 {cap:.15g}
.ends DEN
'''

def execute(net,keep=None):
 global COUNT
 with tempfile.TemporaryDirectory(prefix='pandro_p3_') as t:
  d=Path(t);(d/'test.cir').write_text(net)
  p=subprocess.run([NG,'-b','test.cir'],cwd=d,capture_output=True,text=True,timeout=60)
  assert p.returncode==0 and (d/'waveform.txt').exists(),(p.stdout+p.stderr)[-3000:]
  a=np.loadtxt(d/'waveform.txt',skiprows=1);assert np.isfinite(a).all()
  if keep:
   (P/f'{keep}.cir').write_text(net);(P/f'{keep}.log').write_text(p.stdout+p.stderr)
   np.savetxt(P/f'{keep}.csv',a[::3],delimiter=',',header=(d/'waveform.txt').read_text().splitlines()[0],comments='')
 COUNT+=1
 return a

def cell(ru=28000,cap=20e-12,temp=27,naive=False,keep=None):
 base,_=p2_deck('AD',1)
 oa=base[base.index('.subckt OA'):base.index('.ends OA')+len('.ends OA')]
 drive='Enaive base 0 cmd 0 1\nQnaive supply base actual QUAPP\nRnaive actual 0 '+str(ru)+f'\nCnaive actual 0 {cap}' if naive else 'Xden cmd actual supply DEN'
 net=f'''P3 isolated XY/U cell; simplified internal transistor
.options reltol=1e-6 abstol=1e-12 vntol=1e-8 method=gear
.temp {temp}
Vrail supply 0 15
Vcmd cmd 0 PWL(0 1.024 20u 1.024 20.1u 4.096 50u 4.096 50.1u 3.25)
{drive}
* X=1 V, Y=4 V. Numerator sources ideal; 0.4 V floor startup guard only.
Bquot target 0 V=4/max(v(actual),0.4)
Rdyn target output 100
Cdyn output 0 1n
{oa}
{servo(ru,cap)}
.control
set wr_singlescale
set wr_vecnames
set numdgt=14
tran 10n 80u 0 10n uic
wrdata waveform.txt v(cmd) v(actual) v(output)
quit
.endc
.end
'''
 a=execute(net,keep)
 final_u=float(a[-1,2]); err=final_u/3.25-1
 def settle(start,end,target):
  q=a[(a[:,0]>=start)&(a[:,0]<end)]
  good=np.abs(q[:,2]/target-1)<=.001
  bad=np.flatnonzero(~good)
  i=bad[-1]+1 if len(bad) else 0
  return float((q[i,0]-start)*1e6) if i<len(q) else None
 return dict(ru=ru,cap_pf=cap*1e12,temp_C=temp,naive=naive,final_den_error=err,final_output_error=float(a[-1,3]/(4/3.25)-1),rise_settle_0p1pct_us=settle(20.1e-6,49e-6,4.096),fall_settle_0p1pct_us=settle(50.1e-6,79e-6,3.25),peak_den=float(a[:,2].max()))

def chain(mode,m,gain=1.,trim=0.,ru=28000,cap=20e-12,keep=None):
 net,info=p2_deck(mode,m,gain,trim)
 ports= [('q2','state','state','ref'),('q3','q2','state','ref'),('t','q3','m','ref'),('next','num','state','den'),('inverse','ref_half','ref_double','state'),('geometry','q2','m','ref')] if mode=='AD' else [('q2','att_state','gainstate','ref'),('q3','att_q2','gainstate','ref'),('next','att_num','gainstate','den')]
 lines=net.splitlines();extras=['Vservo_supply servo_supply 0 15'];ratios=[];errors=[]
 for name,x,y,u in ports:
  actual='u_'+name
  for i,line in enumerate(lines):
   if line.startswith('Bint_'+name+' '):lines[i]=line.replace('v('+u+')','v('+actual+')')
  extras.append(f'Xden_{name} {u} {actual} servo_supply DEN')
  ratios += [f'abs(v({x}))/(1.25*max(v({actual}),0.4))',f'abs(v({y}))/10']
  errors.append(f'abs(v({actual})-v({u}))')
 def peak(v):
  z=v[0]
  for x in v[1:]:z=f'max({z},{x})'
  return z
 lines=[('Bclipratio clipratio 0 V='+peak(ratios)) if x.startswith('Bclipratio ') else x for x in lines]
 extras.append('Bservoerr servoerr 0 V='+peak(errors))
 net='\n'.join(lines)+'\n'
 net=net.replace('.control','\n'.join(extras)+servo(ru,cap)+'\n.control')
 net=net.replace('v(corrected) v(neg)','v(corrected) v(neg) v(servoerr)')
 a=execute(net,keep);t=645e-6
 raw=float(np.interp(t,a[:,0],a[:,3]));out=float(np.interp(t,a[:,0],a[:,11]))
 masks=a[:,0]>80e-6
 # Servo errors during rapid transitions retained separately from settled sample.
 return dict(mode=mode,m=m,ru=ru,cap_pf=cap*1e12,raw_error=raw/(V0*m**(1/3))-1,corrected_error=out/(V0*m**(1/3))-1,output_volts=out,port_peak=float(a[masks,10].max()),servo_error_at_sample_volts=float(np.interp(t,a[:,0],a[:,13])),servo_error_peak_after_reset_volts=float(a[masks,13].max()))

def main():
 cells=[]
 for ru in [22400,28000,33600]:
  for cap in [2e-12,20e-12,200e-12]:
   for temp in [0,27,70]:cells.append(cell(ru,cap,temp,keep='cell_nominal' if ru==28000 and cap==20e-12 and temp==27 else None))
 cells.append(cell(naive=True,keep='cell_naive'))
 print('28 cell runs complete',flush=True)
 chains=[]
 for mode in ['AD','Halley']:
  gain,trim=1.,0.
  for i in range(2):
   a=chain(mode,1,gain,trim);b=chain(mode,2,gain,trim)
   slope=V0*(2**(1/3)-1)/(b['output_volts']-a['output_volts'])
   bias=V0-slope*a['output_volts'];gain*=slope;trim+=bias/(gain*.01)
  nominal=[chain(mode,m,gain,trim,keep=mode.lower()+'_p3' if m==2 else None) for m in [1,1.1,1.35,1.6,1.9,2]]
  corners=[chain(mode,m,gain,trim,ru,200e-12) for ru in [22400,33600] for m in [1.1,1.9]]
  chains.append(dict(mode=mode,gain=gain,trim_volts=trim,nominal=nominal,frozen_calibration_corners=corners))
  print(mode,'chain complete',flush=True)
 result=dict(scope='Simplified transistor denominator servo + custom functional arithmetic; not vendor or PDK simulation',spice_runs=COUNT,cells=cells,chains=chains)
 (P/'results.json').write_text(json.dumps(result,indent=2)+'\n')
 print('Runs',COUNT)
 for x in chains:print(x['mode'],max(abs(v['corrected_error']) for v in x['nominal']),max(v['port_peak'] for v in x['nominal']))
if __name__=='__main__':main()
