"""Freeze memory hardware and readout policies before held-out validation."""
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor,as_completed
import json,math,random,time,subprocess
import numpy as np
import memory_model as m
from speed_accuracy import configuration,SCHEDULES as OLD_SCHEDULES
HERE=Path(__file__).resolve().parent

def write(name,value):
 (HERE/name).write_text(json.dumps(value,indent=2)+'\n')

def archive_metadata(cfg):
 return dict(profile=dict(name='archive100',memory_cap=cfg['memory_cap'],switch_ron=cfg['switch_ron'],edge_charge=abs(cfg['charge']),parasitic=0.),
  timing=dict(name='precision',start=cfg['sample_start_us'],width=cfg['sample_width_us'],
   gap=cfg['update_start_us']-cfg['sample_start_us']-cfg['sample_width_us'],period=cfg['period_us']))

def worker(job):
 base=dict(job)
 try:
  if job.get('archive'):
   cfg,cal=configuration(job['case']['p'],job['temp'],job['sign'],job['seed'],OLD_SCHEDULES[0])
   cfg['cycles']=12
   base.update(archive_metadata(cfg))
   result=m.circuit.run(job['case'],cfg,'legacy',step=job.get('step','1u'))
  else:
   cfg,cal=m.configure(job['case']['p'],job['temp'],job['sign'],job['seed'],job['profile'],job['timing'],job.get('overrides'))
   keep=HERE/'examples'/job['label'] if job.get('keep') else None
   result=m.run(job['case'],cfg,job.get('variant','legacy'),step=job.get('step','1u'),keep=keep)
  return dict(**base,config=cfg,calibration=cal,result=result)
 except (ValueError,RuntimeError,AssertionError,OSError,subprocess.TimeoutExpired) as exc:
  return dict(**base,result=dict(status='failed',reason=str(exc)[-3000:],points=[]))

def batch(jobs,name):
 rows=[];start=time.monotonic()
 with ProcessPoolExecutor(max_workers=3) as pool:
  fs=[pool.submit(worker,j)for j in jobs]
  for f in as_completed(fs):
   rows.append(f.result())
   if len(rows)%6==0 or len(rows)==len(jobs):
    print(name,len(rows),'/',len(jobs),round(time.monotonic()-start,1),'seconds',flush=True)
    write(name+'_partial.json',sorted(rows,key=lambda x:x['id']))
 rows.sort(key=lambda x:x['id']);return rows

def point(row,policy):
 return next(p for p in row['result']['points'] if p['iterations']==policy['iterations'] and p['average']==policy['average'])

def select(rows):
 frontier=[]
 for profile,timing in sorted(set((r['profile']['name'],r['timing']['name'])for r in rows)):
  group=[r for r in rows if r['profile']['name']==profile and r['timing']['name']==timing]
  if any(r['result']['status']!='ok'for r in group):continue
  for pt in group[0]['result']['points']:
   frontier.append(dict(profile=profile,timing=timing,iterations=pt['iterations'],average=pt['average'],time_ms=pt['time_ms'],
    worst_error=max(point(r,pt)['error']for r in group)))
 choices=[]
 for ppm in [1.,10.]:
  good=[p for p in frontier if p['worst_error']<=ppm*1e-6]
  choices.append(dict(target_ppm=ppm,policy=min(good,key=lambda x:(x['time_ms'],x['worst_error'])) if good else None))
 return choices,frontier

def main():
 dev=m.prepare([[3,2],[3,.037],[5,500000],[7,2],[983039,2],[1000000,500000]])
 jobs=[]
 for profile in m.PROFILES:
  for timing in m.SCHEDULES:
   if timing['name']=='precision' and profile['name']!='control100':continue
   for i,r in enumerate(dev):
    jobs.append(dict(id=len(jobs),label=f'dev_{profile["name"]}_{timing["name"]}_{i}',case=r,profile=profile,timing=timing,
      temp=[-20,25,85][i%3],sign=1 if i%2 else -1,seed=20270000+i))
 rows=batch(jobs,'development');selected,frontier=select(rows)
 write('selection.json',dict(runs=rows,selected=selected,frontier=frontier))
 print('FROZEN SELECTION',json.dumps(selected),flush=True)
 chosen=next(s['policy']for s in selected if s['target_ppm']==1)
 if chosen is None:
  print('No development policy achieves 1 ppm; no winning hardware is claimed.',flush=True);return
 profile=next(p for p in m.PROFILES if p['name']==chosen['profile'])
 timing=next(t for t in m.SCHEDULES if t['name']==chosen['timing'])
 # Fresh X values, additional low degrees, temperatures and independent seeds.
 pairs=[[p,x] for p in [3,4,5,7,16,31,127,257,4095,65537,983039,1000000] for x in [.019,1.000007,1e-250,1e250]]
 cases=m.prepare(pairs);jobs=[]
 for i,r in enumerate(cases):
  for variant in ['optimized','feedback','archive']:
   jobs.append(dict(id=len(jobs),case_id=i,label=f'validation_{i}_{variant}',case=r,profile=profile,timing=timing,
    temp=[85,-20,25][i%3],sign=1 if i%2 else -1,seed=20271000+i,
    variant='feedback' if variant=='feedback' else 'legacy',archive=variant=='archive',arm=variant))
 validation=batch(jobs,'validation')
 policies={'optimized':chosen,'feedback':chosen,'archive':dict(iterations=2,average=1,time_ms=2.385)}
 summary=[]
 for arm in policies:
  group=[r for r in validation if r['arm']==arm];good=[r for r in group if r['result']['status']=='ok']
  errors=[point(r,policies[arm])['error']for r in good]
  summary.append(dict(arm=arm,policy=policies[arm],cases=len(group),completed=len(good),passes=sum(e<=1e-6 for e in errors),
   worst_error=max(errors,default=None),median_error=float(np.median(errors)) if errors else None))
 write('validation.json',dict(runs=validation,summary=summary));print('VALIDATION',json.dumps(summary),flush=True)
 fine=[]
 for arm in policies:
  group=[r for r in validation if r['arm']==arm and r['result']['status']=='ok']
  if not group:continue
  worst=max(group,key=lambda r:point(r,policies[arm])['error'])
  job=next(j for j in jobs if j['id']==worst['id'])
  f=worker({**job,'step':'.25u','label':f'fine_{arm}','keep':True})
  n=policies[arm]['iterations'];a=policies[arm]['average'];difference=None
  if f['result']['status']=='ok':
   qc,qf=[float(np.mean(r['result']['configured_adc_samples'][n-a:n])) for r in [worst,f]]
   difference=abs((qc-qf)/(worst['case']['p']+qf))
  fine.append(dict(arm=arm,coarse_id=worst['id'],relative_readout_difference=difference,
   within_point_one_ppm=difference is not None and difference<.1e-6,run=f))
 write('fine_checks.json',fine)
 # Declared component sensitivity tests, same frozen policy, no reselection.
 diagnostic=m.prepare([[3,.019],[5,1e-250],[1000000,500000]])
 settings=[('nominal',{}),('half_current',dict(driver_limit_A=.001)),('double_current',dict(driver_limit_A=.004)),
  ('constant_charge',dict(charge_curvature=0.)),('double_curvature',dict(charge_curvature=.2)),
  ('double_charge',dict(charge=profile['edge_charge']*2))]
 jobs=[]
 for i,r in enumerate(diagnostic):
  for name,over in settings:
   jobs.append(dict(id=len(jobs),case=r,label=f'sensitivity_{i}_{name}',profile=profile,timing=timing,
    temp=85,sign=1,seed=20272000+i,overrides=over,keep=name=='nominal'))
 sensitivities=batch(jobs,'sensitivity');write('sensitivity.json',dict(policy=chosen,runs=sensitivities))
 for name in ['development','validation','sensitivity']:(HERE/(name+'_partial.json')).unlink(missing_ok=True)
 print('COMPLETE: development, frozen hardware/policy, held-out comparison, timestep and component sensitivity',flush=True)

if __name__=='__main__':main()
