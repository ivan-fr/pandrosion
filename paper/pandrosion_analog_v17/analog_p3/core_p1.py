"""Cubic analog prototype P1: explicit weighted resistors, dynamic arithmetic
macros, finite buffers, reset, hold leakage and switch charge injection.
All macros are authored here; no manufacturer model or transistor PDK is used.
"""
from pathlib import Path
import numpy as np,json,tempfile,subprocess,shutil
P=Path(__file__).parent
NG=shutil.which('ngspice') or '/opt/homebrew/bin/ngspice'
PROFILES={'ideal_dynamic':dict(g=0.,off=0.,vos=0.,leak=0.,charge=0.,rm=0.),'trimmed_stress':dict(g=1e-4,off=2e-4,vos=2e-4,leak=1e-9,charge=2e-12,rm=1e-4),'untrimmed_stress':dict(g=1e-3,off=5e-3,vos=1e-3,leak=5e-9,charge=5e-12,rm=1e-3)}
# Sign vectors deliberately fixed and documented, not Monte Carlo process corners.
SIGNS=[1,-1,1,-1,1,-1,1,-1]

def deck(mode='AD',m=2.,profile='trimmed_stress',hold=10e-9,acq_us=20.,sign=1,cycles=6):
 assert mode in ['AD','Halley'] and 1<=m<=2
 cfg=PROFILES[profile];g=cfg['g'];off=cfg['off'];vos=cfg['vos'];leak=cfg['leak']*sign;Q=cfg['charge']*sign
 reset=50e-6;calc=30e-6;acq=acq_us*1e-6;gap=5e-6;tail=25e-6
 period=calc+2*acq+gap+tail;ta=reset+calc;tb=ta+acq+gap;edge=10e-9;pulse=50e-9;stop=reset+cycles*period
 L=[f'Pandrosion P1 {mode} m={m} profile={profile} C={hold} acquisition={acq_us}us',
 '* Authored functional macromodels; not AD734/vendor models; no supply power accounting.',
 '.options reltol=2e-6 abstol=1e-11 vntol=1e-7 method=gear',
 'Vref ref 0 4','Ehalf ref_half 0 ref 0 0.5','Edouble ref_double 0 ref 0 2',f'Vm m 0 {4*m:.16g}',
 f'Va ca 0 PULSE(0 3 {ta:.12g} {edge} {edge} {acq:.12g} {period:.12g})',
 f'Vb cb 0 PULSE(0 3 {tb:.12g} {edge} {edge} {acq:.12g} {period:.12g})',
 f'Vr reset 0 PULSE(3 0 {reset:.12g} {edge} {edge} 1 2)',
 '.model sw SW(Ron=100 Roff=1e12 Vt=1.5 Vh=0.1)',
 f'Cc candidate 0 {hold:.12g}',f'Cs state 0 {hold:.12g}',
 'Rc candidate 0 1e12','Rs state 0 1e12',
 f'Ileakc candidate 0 {leak:.12g}',f'Ileaks state 0 {leak:.12g}',
 'Sa sample_drive candidate ca 0 sw','Sb memory_drive state cb 0 sw',
 'Sr1 reset_drive candidate reset 0 sw','Sr2 reset_drive state reset 0 sw']
 # Injection at the falling edge: pulse area Q. 2 ns rise/fall included.
 for node,when in [('candidate',ta),('state',tb)]:
  amp=Q/(pulse+2e-9)
  L.append(f'Iinj_{node} 0 {node} PULSE(0 {amp:.12g} {when+edge+acq+edge/2:.12g} 2n 2n {pulse:.12g} {period:.12g})')
 macro_count=0;buf_count=0;ratios=[]
 def dynamic(name,expr,tau=1e-7,slew=1e7,rout=5.,imax=.005):
  # 1 nF internal integration capacitor; finite rate + finite output current.
  L.extend([f'Bint_{name} 0 z_{name} I=1n*min({slew},max(-{slew},(min(10.5,max(-10.5,({expr})))-v(z_{name}))/{tau}))',f'Cint_{name} z_{name} 0 1n',f'Rint_{name} z_{name} 0 1e12',f'Bout_{name} 0 {name} I=min({imax},max(-{imax},(v(z_{name})-v({name}))/{rout}))',f'Rout_{name} {name} 0 1e12'])
 def buffer(name,node):
  nonlocal buf_count
  o=vos*SIGNS[buf_count%len(SIGNS)]*sign;buf_count+=1
  dynamic(name,f'(1-1e-5)*v({node})+({o:.12g})',tau=8e-8,slew=5e6,rout=.5)
  L.append(f'Ib_{name} {node} 0 100p')
 def product(name,x,y,u):
  nonlocal macro_count
  sg=SIGNS[macro_count%len(SIGNS)]*sign;macro_count+=1
  ratios.extend([f'abs(v({x}))/(1.25*max(v({u}),0.4))',f'abs(v({y}))/10'])
  xx=f'min(1.25*max(v({u}),0.4),max(-1.25*max(v({u}),0.4),v({x})))'
  dynamic(name,f'(1+({g*sg:.12g}))*({xx})*min(10,max(-10,v({y})))/max(v({u}),0.4)+({off*sg:.12g})')
 buffer('reset_drive','ref');buffer('sample_drive','next');buffer('memory_drive','candidate')
 if mode=='AD':
  product('q2','state','state','ref');product('q3','q2','state','ref')
 else:
  # Preserve XY while keeping X <= 1.25 U and Y <= 10 V.
  L.append('Egainstate gs_target 0 state 0 1.6666666666666667')
  buffer('gainstate','gs_target')
  L += ['Rtop_att_state gainstate att_state 32k','Rbot_att_state att_state 0 18k','Ib_gaininput state 0 100p']
  for src,att in [('q2','att_q2'),('num','att_num')]:
   L += [f'Rtop_{att} {src} {att} 20k',f'Rbot_{att} {att} 0 30k']
  product('q2','att_state','gainstate','ref');product('q3','att_q2','gainstate','ref')
 if mode=='AD':
  product('t','q3','m','ref')
  terms=[('num','ref',10000.,'t',20000.),('den','ref',20000.,'t',10000.)]
 else:terms=[('num','q3',20000.,'m',10000.),('den','q3',10000.,'m',20000.)]
 ri=0
 for out,x,rx,y,ry in terms:
  for src,r in [(x,rx),(y,ry),('0',20000.)]:
   # Alternating resistor errors, fixed for all inputs and updates of a case.
   val=r*(1+cfg['rm']*SIGNS[ri%len(SIGNS)]*sign);ri+=1
   L.append(f'Rweight{ri} {out}_sum {src} {val:.12g}')
  buffer(out,f'{out}_sum')
 if mode=='AD':product('next','num','state','den')
 else:product('next','att_num','gainstate','den')
 if mode=='AD':
  product('inverse','ref_half','ref_double','state');product('geometry','q2','m','ref')
  buffer('out','inverse');buffer('outgeo','geometry')
 else:
  buffer('out','state');L.append('Egeo outgeo 0 out 0 1')
 for node in ['out','outgeo']:L.extend([f'Rload_{node} {node} 0 5k',f'Cload_{node} {node} 0 20p'])
 peak=ratios[0]
 for value in ratios[1:]:peak=f'max({peak},{value})'
 L.append(f'Bclipratio clipratio 0 V={peak}')
 L+=['.control','set noaskquit','set wr_singlescale','set wr_vecnames','set numdgt=14',
 f'tran 100n {stop:.12g} 0 100n uic',
 'wrdata waveform.txt v(state) v(candidate) v(out) v(outgeo) v(next) v(num) v(den) v(ca) v(cb) v(clipratio)',
 'quit','.endc','.end']
 return '\n'.join(L)+'\n',dict(period=period,reset=reset,tb=tb,acq=acq,cycles=cycles,macros=macro_count,buffers=buf_count)

def simulate(mode='AD',m=2.,profile='trimmed_stress',hold=10e-9,acq_us=20.,sign=1,keep=None):
 net,info=deck(mode,m,profile,hold,acq_us,sign)
 with tempfile.TemporaryDirectory(prefix='pandrosion_p1_')as temp:
  d=Path(temp);(d/'core.cir').write_text(net)
  proc=subprocess.run([NG,'-b','core.cir'],cwd=d,capture_output=True,text=True,timeout=90)
  log=proc.stdout+proc.stderr
  if proc.returncode or not(d/'waveform.txt').exists():raise RuntimeError(log[-5000:])
  data=np.loadtxt(d/'waveform.txt',skiprows=1)
  if not np.isfinite(data).all():raise AssertionError('nonfinite waveform')
  if keep:
   (P/f'{keep}.cir').write_text(net);(P/f'{keep}.log').write_text(log)
   np.savetxt(P/f'{keep}.csv',data[::5],delimiter=',',header='time,state,candidate,output,geometry,next,num,den,clock_a,clock_b,clip_ratio',comments='')
 samples=[];r=m**(1/3)
 for n in range(1,info['cycles']+1):
  time=info['reset']+n*info['period']-5e-6
  v=[float(np.interp(time,data[:,0],data[:,i]))for i in range(1,10)]
  samples.append(dict(iteration=n,time_us=time*1e6,state=v[0]/4,output=v[2]/4,relative_error=v[2]/(4*r)-1,geometry_error=v[3]/(4*r)-1,denominator_volts=v[6]))
 # Success definition: all remaining sampled outputs satisfy the target.
 def sustained(eps):
  for k in range(len(samples)):
   if all(abs(z['relative_error'])<=eps for z in samples[k:]):return samples[k]['time_us']
  return None
 peak_clip=float(max(data[data[:,0]>info['reset']+30e-6,10]))
 return dict(peak_port_ratio_after_reset=peak_clip,mode=mode,m=m,profile=profile,hold_pf=hold*1e12,acquisition_us=acq_us,sign=sign,period_us=info['period']*1e6,arithmetic_macros=info['macros'],buffers=info['buffers'],samples=samples,final_error=samples[-1]['relative_error'],final_geometry_error=samples[-1]['geometry_error'],time_to_0p1pct_us=sustained(.001),time_to_0p01pct_us=sustained(.0001))

def main():
 rows=[]
 for mode in ['AD','Halley']:
  for profile in PROFILES:
   for m in [1.,1.25,1.5,1.75,2.]:
    rows.append(simulate(mode,m,profile,keep=f'{mode.lower()}_p1'if profile=='trimmed_stress'and m==2 else None))
  print(mode,'input/profile sweep complete',flush=True)
 for row in rows:
  assert row['peak_port_ratio_after_reset']<.95, row
  if row['profile']!='untrimmed_stress':assert abs(row['final_error'])<.001, row
 # Input points distinct from the calibration endpoints, opposite error sign, varied hold cells.
 corners=[]
 for mode in ['AD','Halley']:
  for hold in [100e-12,1e-9,10e-9]:
   for acq in [1.,5.,20.]:corners.append(simulate(mode,1.6,'trimmed_stress',hold,acq))
  corners.append(simulate(mode,1.6,'trimmed_stress',10e-9,20.,-1))
  print(mode,'memory corners complete',flush=True)
 out={'status':'simulations completed','scope':'Custom nonideal functional macromodels, not vendor SPICE, PDK, post-layout, silicon or guaranteed component bounds.','profiles':PROFILES,'sign_vector':SIGNS,'nominal_grid':rows,'memory_corners':corners,'spice_runs':len(rows)+len(corners)}
 (P/'results.json').write_text(json.dumps(out,indent=2)+'\n')
 print('Runs:',out['spice_runs'],flush=True)
if __name__=='__main__':main()
