"""Frozen-policy development and paired held-out validation of AD cell topologies.
All three share V30 preparation, power chain, memories, loading and calibration.
Only the two finite-bandwidth variants add the same two noisy correction cells.
"""
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor,as_completed
import json,random,math,time,subprocess
import numpy as np
from circuit import run,calibrate_correction,VARIANTS
from model import prepare
from speed_accuracy import configuration,SCHEDULES
HERE=Path(__file__).resolve().parent
TARGETS=[.1,1.,10.]

def worker(job):
 r=job['case'];cfg,cal=configuration(r['p'],job['temp'],job['sign'],job['seed'],job['schedule'])
 trims,bench=calibrate_correction(cfg,job['seed']+901)
 cfg.update(correction_calibration=trims,correction_noise_rms=cfg['noise_rms'])
 cfg.update(job.get('overrides',{}));results=[]
 for variant in job.get('variants',VARIANTS):
  try:
   keep=HERE/'examples'/f'{job["label"]}_{variant}' if job.get('keep') else None
   results.append(run(r,cfg,variant,step=job.get('step','1u'),keep=keep))
  except (AssertionError,RuntimeError,TimeoutError,subprocess.TimeoutExpired) as exc:
   results.append(dict(variant=variant,status='failed',reason=str(exc)[-2500:],points=[]))
 return dict(id=job['id'],label=job['label'],case=r,p=r['p'],X=r['originalX'],
  temperature_C=job['temp'],sign=job['sign'],seed=job['seed'],schedule=job['schedule'][0],
  config=cfg,calibration=dict(shared=cal,correction=bench),results=results)

def batch(jobs,label):
 rows=[];start=time.monotonic()
 with ProcessPoolExecutor(max_workers=3) as pool:
  fs={pool.submit(worker,j):j['id'] for j in jobs}
  for f in as_completed(fs):
   rows.append(f.result())
   if len(rows)%4==0 or len(rows)==len(jobs):
    print(label,len(rows),'/',len(jobs),round(time.monotonic()-start,1),'seconds',flush=True)
    (HERE/f'{label}_partial.json').write_text(json.dumps(sorted(rows,key=lambda r:r['id']))+'\n')
 return sorted(rows,key=lambda r:r['id'])

def result(row,variant):return next(x for x in row['results'] if x['variant']==variant)
def point(row,variant,policy):
 rr=result(row,variant)
 return next((x for x in rr['points'] if x['iterations']==policy['iterations'] and x['average']==policy['average']),None)

def select(rows):
 choices=[];frontier=[]
 for variant in VARIANTS:
  options=[]
  for schedule in SCHEDULES:
   group=[r for r in rows if r['schedule']==schedule[0]]
   if not group or any(result(r,variant)['status']!='ok' for r in group):continue
   for pt in result(group[0],variant)['points']:
    worst=max(point(r,variant,pt)['error'] for r in group)
    options.append(dict(variant=variant,schedule=schedule[0],iterations=pt['iterations'],average=pt['average'],time_ms=pt['time_ms'],worst_error=worst))
  frontier.extend(options)
  for ppm in TARGETS:
   good=[x for x in options if x['worst_error']<=ppm*1e-6]
   choices.append(dict(variant=variant,target_ppm=ppm,policy=min(good,key=lambda x:(x['time_ms'],x['worst_error'])) if good else None))
 return choices,frontier

def summarize(rows,selected):
 summaries=[]
 for sel in selected:
  policy=sel['policy']
  if policy is None:summaries.append(dict(**sel,cases=0,completed=0,passes=0));continue
  rr=[r for r in rows if r['schedule']==policy['schedule']]
  good=[r for r in rr if result(r,sel['variant'])['status']=='ok']
  errors=[point(r,sel['variant'],policy)['error'] for r in good]
  summaries.append(dict(**sel,cases=len(rr),completed=len(good),passes=sum(x<=sel['target_ppm']*1e-6 for x in errors),worst_error=max(errors,default=None),median_error=float(np.median(errors)) if errors else None))
 return summaries

def main():
 dev=prepare([[p,x] for p in [3,7,983039,1000000] for x in [2,500000]])
 jobs=[]
 for schedule in SCHEDULES:
  for i,r in enumerate(dev):
   jobs.append(dict(id=len(jobs),label=f'dev_{schedule[0]}_{i}',case=r,temp=85 if i%2 else 25,
     sign=-1 if i%2 else 1,seed=20269200+i,schedule=schedule))
 training=batch(jobs,'development');selected,frontier=select(training)
 selection=dict(selected=selected,frontier=frontier,runs=training)
 (HERE/'selection.json').write_text(json.dumps(selection,indent=2)+'\n')
 print('FROZEN SELECTION',json.dumps(selected),flush=True)
 degrees=[3,4,5,7,16,31,127,257,4095,65537,983039,1000000]
 pairs=[[p,x] for p in degrees for x in [1e-300,.071,1.000003,1e300]]
 rng=random.Random(20269919)
 pairs += [[max(3,round(10**rng.uniform(math.log10(3),6))),10**rng.uniform(-280,280)] for _ in range(16)]
 held=prepare(pairs)
 names={x['policy']['schedule'] for x in selected if x['policy']}
 names.add('precision') # Common reference schedule, independent of selection outcome.
 jobs=[]
 for schedule in SCHEDULES:
  if schedule[0] not in names:continue
  for i,r in enumerate(held):
   jobs.append(dict(id=len(jobs),label=f'validation_{schedule[0]}_{i}',case=r,temp=[-20,25,85][i%3],
    sign=-1 if i%2 else 1,seed=20269300+i,schedule=schedule))
 validation=batch(jobs,'validation');summary=summarize(validation,selected)
 (HERE/'validation.json').write_text(json.dumps(dict(runs=validation,summary=summary),indent=2)+'\n')
 print('VALIDATION',json.dumps(summary),flush=True)
 # Timestep refinement on each distinct selected topology/policy's worst completed case.
 fine=[];seen=set()
 for sel in selected:
  pol=sel['policy'];variant=sel['variant']
  if not pol:continue
  key=(variant,pol['schedule'],pol['iterations'],pol['average'])
  if key in seen:continue
  seen.add(key)
  group=[r for r in validation if r['schedule']==pol['schedule'] and result(r,variant)['status']=='ok']
  if not group:continue
  worst=max(group,key=lambda r:point(r,variant,pol)['error'])
  job=next(j for j in jobs if j['id']==worst['id'])
  rerun=worker({**job,'step':'.25u','variants':[variant],'keep':True,'label':f'fine_{variant}_{pol["iterations"]}_{pol["average"]}'})
  pt=point(rerun,variant,pol)
  difference=abs(pt['error']-point(worst,variant,pol)['error']) if pt else None
  fine.append(dict(policy=pol,coarse_case_id=worst['id'],error_difference=difference,within_point_one_ppm=difference is not None and difference<.1e-6,run=rerun))
  print('fine',key,difference,flush=True)
 (HERE/'fine_checks.json').write_text(json.dumps(fine,indent=2)+'\n')
 # Leave common hardware untouched while stress-testing the added cell assumptions.
 diagnostic=prepare([[3,.071],[7,1e-200],[1000000,500000]])
 profiles=[('full',{}),('no_inner_trim',{'correction_calibration':[[0,0],[0,0]]}),
  ('quiet_inner',{'correction_noise_rms':0.}),('double_inner_noise',{'correction_noise_rms':10e-6}),
  ('slow_inner',{'correction_tau_scale':10.})]
 jobs=[]
 for i,r in enumerate(diagnostic):
  for name,overrides in profiles:
   jobs.append(dict(id=len(jobs),label=f'ablation_{i}_{name}',case=r,temp=85,sign=-1 if i%2 else 1,
    seed=20269400+i,schedule=SCHEDULES[0],overrides=overrides,keep=name=='full'))
 ablation=batch(jobs,'ablation')
 (HERE/'ablation.json').write_text(json.dumps(dict(runs=ablation),indent=2)+'\n')
 for label in ['development','validation','ablation']:
  (HERE/f'{label}_partial.json').unlink(missing_ok=True)
 print('COMPLETE: paired policies, held-out tests, timestep refinement, and correction-cell ablations',flush=True)
if __name__=='__main__':main()
