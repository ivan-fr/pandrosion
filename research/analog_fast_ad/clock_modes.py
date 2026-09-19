"""Clock alternatives: state-dependent update controller and genuine continuous SPICE feedback.
The adaptive controller is a software behavioral model, not implemented comparators.
The continuous circuit changes the dynamics; it does not have discrete cubic order.
"""
from pathlib import Path
import tempfile,subprocess,json,csv
import numpy as np
import mpmath as mp
from model import prepare,schedule
from spice import deck
OUT=Path(__file__).parent

def reference_q(r):
 mp.mp.dps=90
 return float(r['p']*(mp.exp(-mp.log(mp.mpf(r['originalX']))/r['p'])/mp.mpf(r['c'])-1))

def adaptive(r,step=.25e-6,tau=1e-6,tolerance=1e-7,initial_state=None,slots=None):
 p=r['p'];ops=schedule(p);active_stages=len(ops)
 if slots is not None:
  assert slots>=len(ops)
  ops=ops+[dict(kind='square',product_weight=0.) for _ in range(slots-len(ops))]
 w=np.array([o['product_weight'] for o in ops])
 v=np.array([o.get('copy_weight',0) for o in ops]);sq=np.array([o['kind']=='square' for o in ops])
 y=np.zeros(len(ops)+2) if initial_state is None else np.array(initial_state,dtype=float);q=0.;time=0.;events=[];within=0;held=0.
 def drives(state,held_q):
  read=state[0];prev=state[:-2]
  power=prev+v*(read-prev)+w*np.where(sq,prev*prev,prev*read)
  t=r['Y']*(1+state[-2]);den=1+t+(t-1)/p
  target=read+2*(1+read/p)*(1-t)/den
  return np.concatenate(([held_q],power,[target]))
 while len(events)<6 and time<.01:
  def f(z):return (drives(z,q)-z)/tau
  k1=f(y);k2=f(y+step*k1/2);k3=f(y+step*k2/2);k4=f(y+step*k3)
  y += step*(k1+2*k2+2*k3+k4)/6;time+=step;held+=step
  error=float(np.max(abs(drives(y,q)-y)))
  within=within+1 if error<tolerance else 0
  # All-node completion detector plus dwell; never consult the root reference.
  if within*step>=5*tau and held>=5*tau:
   q=float(y[-1]);events.append(dict(time_s=time,q=q,detector_error_V=error));within=0;held=0
  assert np.all(np.isfinite(y)) and np.max(abs(y))<2
 assert len(events)==6,'Adaptive controller timed out'
 qs=reference_q(r);delta=q-qs
 return dict(p=p,X=r['originalX'],stages=active_stages,physical_slots=len(ops),final_stage_state=y.tolist(),events=events,total_time_s=time,
  q=q,state_error_V=abs(delta),relative_error=abs(delta/(p+qs+delta)),step_s=step,
  scope='Ideal memory/switches and noise-free first-order stages; all-node detector overhead omitted')

def continuous(r,memory_tau,step='0.5u',duration_s=None):
 duration=duration_s if duration_s is not None else max(20*memory_tau,500e-6)
 text=deck(r['p'],r['Y'])
 omit=('Vreset ','Vsample ','Vupdate ','Sreset ','Ssample ','Supdate ','Cnext ','Rnext ','Bstored ')
 lines=[line for line in text.splitlines() if not line.startswith(omit)]
 lines=[f'tran {step} {duration:.17g} uic' if line.startswith('tran ') else line for line in lines]
 lines.insert(lines.index('.control'),f'Bfeedback 0 state I=(v(candidate)-v(state))*{10e-9/memory_tau:.17g}')
 with tempfile.TemporaryDirectory(prefix='pandrosion-continuous-') as tmp:
  path=Path(tmp);(path/'cell.cir').write_text('\n'.join(lines)+'\n')
  p=subprocess.run(['ngspice','-b','cell.cir'],cwd=path,text=True,capture_output=True,timeout=120)
  if p.returncode:raise RuntimeError(p.stdout+p.stderr)
  a=np.loadtxt(path/'wave.txt',skiprows=1)
 qs=reference_q(r);delta=a[:,1]-qs
 guarded=bool(a[:,5].min()<=.25 or abs(a[:,6]).max()>=2 or a[:,7].max()>=1.99)
 outside=np.flatnonzero(abs(delta)>1e-6)
 settling=None if len(outside) and outside[-1]==len(delta)-1 else float(a[outside[-1]+1,0]) if len(outside) else 0.
 # Require a full 10% tail inside the tolerance, not an accidental final crossing.
 stable_tail=bool(np.max(abs(delta[a[:,0]>=.9*duration]))<=1e-6)
 row=dict(p=r['p'],X=r['originalX'],extended=duration_s is not None,memory_tau_s=memory_tau,stage_tau_s=1e-6,duration_s=duration,
  q_final=float(a[-1,1]),relative_error=float(abs(delta[-1]/(r['p']+qs+delta[-1]))),
  tail_state_error_max_V=float(np.max(abs(delta[a[:,0]>=.9*duration]))),settling_time_s=settling,
  stable_tail=stable_tail,guard_activated=guarded,max_step=step)
 # Retain a bounded waveform for review, including failures rather than hiding them.
 indices=np.linspace(0,len(a)-1,min(1000,len(a)),dtype=int)
 row['waveform']=[dict(time_s=float(a[i,0]),q=float(a[i,1])) for i in indices]
 return row

def save(report):
 with (OUT/'clock_modes_waveforms.csv').open('w') as f:
  writer=csv.writer(f,lineterminator="\n");writer.writerow(['run','time_s','q'])
  for i,row in enumerate(report['continuous']):
   row['waveform_run']=i
   for point in row.pop('waveform'):writer.writerow([i,point['time_s'],point['q']])
 (OUT/'clock_modes_results.json').write_text(json.dumps(report,indent=2)+'\n')

def main():
 # Independent symbolic local-rate check for the instantaneous scalar ODE.
 import sympy as sp
 p,q,t=sp.symbols('p q t', positive=True)
 u=1+q/p;rate=2*u*(1-t)/(1+t+(t-1)/p)
 assert sp.simplify((sp.diff(rate,q)+sp.diff(rate,t)*t/u).subs(t,1)) == -1
 cases=prepare([[p,x] for p in [3,32,983039,1000000] for x in [.125,2,500000,1e300]])
 adaptive_rows=[adaptive(r) for r in cases]
 fine=adaptive(cases[-2],step=.125e-6)
 coarse=adaptive_rows[-2]
 assert abs(fine['q']-coarse['q'])<2e-7 and abs(fine['total_time_s']-coarse['total_time_s'])<5e-6
 print('Adaptive: 16 cases and step-halving passed',flush=True)
 continuous_rows=[]
 # Include multiple degrees AND multiple X, not just the showcase example.
 for r in cases:
  for tau in [2e-6,20e-6,200e-6]:
   row=continuous(r,tau);continuous_rows.append(row)
   print('continuous',r['p'],r['originalX'],tau,'stable tail',row['stable_tail'],'guard',row['guard_activated'],flush=True)
 # Refinement checks one deliberately aggressive and one slow feedback case.
 for tau in [2e-6,200e-6]:
  row=continuous(cases[-2],tau,step='0.125u')
  coarse=next(x for x in continuous_rows if x['p']==1000000 and x['X']==500000 and x['memory_tau_s']==tau)
  assert row['guard_activated']==coarse['guard_activated'] and row['stable_tail']==coarse['stable_tail']
  if row['stable_tail']:assert abs(row['q_final']-coarse['q_final'])<1e-6
  continuous_rows.append(row)
 # Distinguish delayed settling from persistent oscillation at the intermediate gain.
 for r in cases:
  if r['p'] in [983039,1000000] and r['originalX']==500000:
   continuous_rows.append(continuous(r,20e-6,duration_s=.01))
 save(dict(scope='Controller research, not physical asynchronous logic or a global delayed-loop stability theorem',
  adaptive=adaptive_rows,adaptive_fine=fine,continuous=continuous_rows))
 print('PASS solver refinements; unstable/guarded runs explicitly retained')
if __name__=='__main__':main()
