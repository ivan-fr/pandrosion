"""Fixed-hardware timing sweep, then held-out validation of selected policies.
No oracle stopping: each policy fixes schedule, iteration count and averaging.
Times exclude preparation, calibration, converter latency and output decoding.
"""
from simulation_runtime import campaign_workers
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor, as_completed
import json, math
import numpy as np
import mpmath as mp
from model import prepare, decode
from spice import run
from revised_circuit import revision, calibrate_memory, calibrate_adc
from calibrate_cells import calibrate
ROOT=Path(__file__).parent
SCHEDULES=[('precision',350,400,20,1200),('medium',150,200,20,700),
 ('short',80,50,10,320),('aggressive',40,15,10,210),('minimum',20,10,10,180)]
POLICIES=[(n,a) for n in [2,3,4,6,8,12,20] for a in [1,2,4,8,16] if a<=n and (a==1 or n-a>=2)]

def configuration(p,temp,sign,seed,schedule):
 name,start,width,gap,period=schedule
 cfg=revision(temp,sign,seed)
 cfg.update(sample_start_us=start,sample_width_us=width,update_start_us=start+width+gap,
            update_width_us=width,period_us=period)
 trims,cell=calibrate(p,cfg,seed=seed+1)
 _,probe=calibrate_memory(cfg,seed+2)
 estimate=probe['estimated_residual_leak_A']
 assert abs(estimate)<1e-6
 cfg['leak_compensation_A']=round(estimate/2e-12)*2e-12
 memory,mem=calibrate_memory(cfg,seed+4)
 adc,ad=calibrate_adc(cfg,seed+3)
 return {**cfg,**trims,'memory_calibration':memory,'adc_calibration':adc},dict(cells=cell,probe=probe,memory=mem,adc=ad)

def worker(job):
 case,temp,sign,seed,schedule,step=job
 row=dict(p=case['p'],X=case['originalX'],temperature_C=temp,seed=seed,schedule=schedule[0])
 try:
  cfg,cal=configuration(case['p'],temp,sign,seed,schedule)
  sim=run(case,config=cfg,step=step)
  mp.mp.dps=80;ref=mp.exp(mp.log(mp.mpf(case['originalX']))/case['p'])
  initial=float(abs(mp.mpf(decode(case['c'],0,case['p']))/ref-1))
  pts=[]
  for n,avg in POLICIES:
   q=float(np.mean(sim['configured_adc_samples'][n-avg:n]))
   error=float(abs(mp.mpf(decode(case['c'],q,case['p']))/ref-1))
   latency=(cfg['update_start_us']+cfg['update_width_us']+15+(n-1)*cfg['period_us'])/1000
   pts.append(dict(iterations=n,average=avg,time_ms=latency,error=error))
  return dict(**row,status='ok',initial_error=initial,points=pts,simulation=sim,calibration=cal)
 except (AssertionError,RuntimeError) as exc:
  return dict(**row,status='rejected',reason=str(exc),points=[])

def batch(jobs,label):
 rows=[]
 with ProcessPoolExecutor(max_workers=campaign_workers()) as pool:
  futs={pool.submit(worker,j):i for i,j in enumerate(jobs)}
  for f in as_completed(futs):
   rows.append(dict(id=futs[f],**f.result()))
   if len(rows)%5==0:print(label,len(rows),'/',len(jobs),flush=True)
 return sorted(rows,key=lambda r:r['id'])

def envelope(rows):
 points=[]
 for sched in SCHEDULES:
  rr=[r for r in rows if r['schedule']==sched[0]]
  if not rr or any(r['status']!='ok' for r in rr):continue
  for i,(n,avg) in enumerate(POLICIES):
   points.append(dict(schedule=sched[0],iterations=n,average=avg,time_ms=rr[0]['points'][i]['time_ms'],
    worst_error=max(r['points'][i]['error'] for r in rr)))
 return points

def main():
 dev=prepare([[p,x] for p in [3,7,983039,1000000] for x in [2,500000]])
 jobs=[(r,85 if i%2 else 25,-1 if i%2 else 1,20264000+i,s,'1u') for s in SCHEDULES for i,r in enumerate(dev)]
 training=batch(jobs,'development');points=envelope(training)
 selected=[]
 for ppm in [100,10,1]:
  eligible=[x for x in points if x['worst_error']<=ppm*1e-6]
  selected.append(dict(target_ppm=ppm,policy=min(eligible,key=lambda x:(x['time_ms'],x['worst_error'])) if eligible else None))
 # Selection is complete before independent inputs/noise seeds are evaluated.
 (ROOT/'speed_accuracy_selection.json').write_text(json.dumps(dict(training=training,points=points,selected=selected),indent=2)+'\n')
 print('Frozen selection:',selected,flush=True)
 held=prepare([[p,x] for p in [3,5,31,257,65537,1000000] for x in [.037,1e-200,1e200]])
 names={r['policy']['schedule'] for r in selected if r['policy']}
 schedules=[s for s in SCHEDULES if s[0] in names]
 jobs=[(r,[-20,25,85][i%3],-1 if i%2 else 1,20265000+i,s,'1u') for s in schedules for i,r in enumerate(held)]
 validation=batch(jobs,'validation');summaries=[]
 for item in selected:
  pol=item['policy']
  if not pol:summaries.append(item);continue
  idx=POLICIES.index((pol['iterations'],pol['average']))
  rows=[r for r in validation if r['schedule']==pol['schedule']]
  good=[r for r in rows if r['status']=='ok']
  errors=[r['points'][idx]['error'] for r in good]
  summaries.append(dict(**item,cases=len(rows),completed=len(good),passes=sum(e<=item['target_ppm']*1e-6 for e in errors),worst_error=max(errors,default=None)))
 # Refine timestep on worst held-out case for each distinct selected policy.
 fine=[];seen=set()
 for item in selected:
  pol=item['policy']
  if not pol:continue
  key=(pol['schedule'],pol['iterations'],pol['average'])
  if key in seen:continue
  seen.add(key);idx=POLICIES.index(key[1:]);rr=[r for r in validation if r['schedule']==key[0] and r['status']=='ok']
  if not rr:continue
  worst=max(rr,key=lambda r:r['points'][idx]['error'])
  job=jobs[worst['id']];f=worker((*job[:-1],'.25u'))
  assert f['status']=='ok'
  delta=abs(f['points'][idx]['error']-worst['points'][idx]['error'])
  assert delta<.1e-6,('timestep sensitivity',delta)
  fine.append(dict(policy=pol,error_difference=delta,run=f))
 report=dict(scope='Behavioral fixed-hardware timing study; not physical latency or universal accuracy. Finite targets may fail and are retained.',
  schedules=SCHEDULES,policies=POLICIES,training=training,points=points,selected=selected,validation=validation,summary=summaries,fine=fine)
 (ROOT/'speed_accuracy_results.json').write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps(summaries,indent=2),flush=True)
if __name__=='__main__':main()
