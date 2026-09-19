"""Noise-aware completion controller subsystem, not the SPICE memory/ADC circuit.
Finite detector offset/quantization, dwell/hysteresis, characterized delay bound,
and explicit timeouts. Fault runs must fail closed; no root participates in control.
"""
from pathlib import Path
import json
import numpy as np
from model import schedule,prepare
from clock_modes import reference_q
OUT=Path(__file__).parent

def simulate(r,seed,fault=None,step=.25e-6):
 rng=np.random.default_rng(seed);p=r['p'];ops=schedule(p);n=len(ops)
 w=np.array([o['product_weight'] for o in ops]);v=np.array([o.get('copy_weight',0) for o in ops]);sq=np.array([o['kind']=='square' for o in ops])
 tau=1e-6;characterized_bound=1.25*tau;guard=8*(n+2)*characterized_bound
 low=12e-6;high=24e-6;dwell=10e-6;timeout=max(2e-3,4*guard)
 y=np.zeros(n+2);q=0.;elapsed=0.;held=0.;quiet=False;quiet_time=0.;events=[]
 detector_offset=rng.uniform(-1e-6,1e-6,n+2);next_noise=0.;noise=np.zeros(n+2);candidate_noise=0
 q_history=[];decision=None;min_lag_error=[]
 def drives(z):
  read=z[0];prev=z[:-2];powers=prev+v*(read-prev)+w*np.where(sq,prev*prev,prev*read)
  t=r['Y']*(1+z[-2]);den=1+t+(t-1)/p
  candidate=read+2*(1+read/p)*(1-t)/den+candidate_noise
  return np.concatenate(([q],powers,[candidate]))
 for count in range(round(6*timeout/step)+1):
  if elapsed>=next_noise:
   sigma=100e-6 if fault=='excess_noise' else 2e-6
   noise=rng.normal(0,sigma,n+2);candidate_noise=rng.normal(0,.5e-6)
   next_noise+=1e-6
  def f(z):
   d=(drives(z)-z)/tau
   if fault=='stuck_candidate':d[-1]=0
   return d
  k1=f(y);k2=f(y+step*k1/2);k3=f(y+step*k2/2);k4=f(y+step*k3)
  y+=step*(k1+2*k2+2*k3+k4)/6;elapsed+=step;held+=step
  true_mismatch=drives(y)-y
  measured=np.rint((true_mismatch+detector_offset+noise)/(4/2**20))*(4/2**20)
  level=float(np.max(abs(measured)))
  if level>high:quiet=False;quiet_time=0
  elif level<low:quiet=True
  if quiet:quiet_time+=step
  q_history.append(float(y[-1]));q_history=q_history[-max(1,round(10e-6/step)):]
  if not np.all(np.isfinite(y)) or np.max(abs(y))>=2:decision='range_fault';break
  if held>=guard and quiet_time>=dwell:
   events.append(dict(time_s=elapsed,hold_s=held,detector_V=level,true_local_mismatch_V=float(np.max(abs(true_mismatch)))))
   q=float(np.mean(q_history));held=0.;quiet_time=0.;quiet=False;q_history=[]
   if len(events)==6:decision='completed';break
  if held>=timeout:decision='timeout';break
 qs=reference_q(r);delta=q-qs
 return dict(p=p,X=r['originalX'],seed=seed,fault=fault,status=decision or 'timeout',events=events,time_s=elapsed,
  guard_s=guard,timeout_s=timeout,q=q,relative_error=abs(delta/(p+qs+delta)),step_s=step,
  detector_low_V=low,detector_high_V=high)

def main():
 cases=prepare([[p,x] for p in [3,7,32,257,983039,1000000] for x in [.037,2.,1e100]])
 runs=[simulate(r,20263000+i) for i,r in enumerate(cases)]
 assert all(r['status']=='completed' for r in runs)
 assert all(e['hold_s']>=r['guard_s'] for r in runs for e in r['events'])
 faults=[]
 for r in prepare([[3,2],[1000000,2]]):
  for fault in ['stuck_candidate','excess_noise']:
   result=simulate(r,20263099,fault);faults.append(result)
   assert result['status']=='timeout' and not result['events'],result
 fine=simulate(cases[-2],20263000+len(cases)-2,step=.125e-6)
 assert fine['status']=='completed' and abs(fine['q']-runs[-2]['q'])<10e-6
 report=dict(scope='Noisy controller subsystem model; not the revised SPICE circuit or a hardware detector. Characterized stage delay bound is assumed.',
  runs=runs,faults=faults,fine_check=fine)
 (OUT/'noisy_controller_results.json').write_text(json.dumps(report,indent=2)+'\n')
 print('PASS',len(runs),'normal jobs,',len(faults),'fail-closed injected faults; timestep check')
 print('Worst subsystem root error',max(r['relative_error'] for r in runs))
if __name__=='__main__':main()
