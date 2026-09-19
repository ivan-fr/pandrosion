"""One explicit policy refinement, then a completely new held-out set."""
from pathlib import Path
import json
import numpy as np
import memory_campaign as c
import memory_model as m
HERE=Path(__file__).resolve().parent

def freeze():
 first=json.loads((HERE/'validation.json').read_text())['runs']
 secondary=json.loads((HERE/'secondary.json').read_text())['runs']
 selected=[]
 for arm in ['optimized','feedback','loaded_control','archive']:
  group=[r for r in first+secondary if r['arm']==arm]
  options=[]
  if all(r['result']['status']=='ok'for r in group):
   for pt in group[0]['result']['points']:
    worst=max(c.point(r,pt)['error']for r in group)
    if worst<=.7e-6:options.append(dict(iterations=pt['iterations'],average=pt['average'],time_ms=pt['time_ms'],worst_error=worst))
  policy=min(options,key=lambda p:(p['time_ms'],p['worst_error'])) if options else None
  metadata=c.archive_metadata(group[0]['config']) if arm=='archive' else dict(profile=group[0]['profile'],timing=group[0]['timing'])
  selected.append(dict(arm=arm,policy=policy,**metadata,training_cases=len(group)))
 c.write('refinement_selection.json',selected);print('FROZEN REFINEMENT',json.dumps(selected),flush=True)
 return selected

def main():
 selected=freeze()
 cases=m.prepare([[p,x]for p in [3,4,5,7,31,257,983039,1000000]for x in [.043,1.000011,1e-220,1e220]])
 jobs=[]
 for sel in selected:
  if not sel['policy']:continue
  for i,r in enumerate(cases):
   for repeat in range(2):
    k=2*i+repeat
    jobs.append(dict(id=len(jobs),case_id=k,label=f'final_{sel["arm"]}_{k}',case=r,profile=sel['profile'],timing=sel['timing'],
     temp=[-20,85,25][k%3],sign=1 if repeat else -1,seed=20274000+k,
     variant='feedback' if sel['arm']=='feedback' else 'legacy',archive=sel['arm']=='archive',arm=sel['arm']))
 rows=c.batch(jobs,'refinement');summary=[];fine=[]
 for sel in selected:
  pol=sel['policy'];group=[r for r in rows if r['arm']==sel['arm']]
  if not pol:
   summary.append(dict(arm=sel['arm'],policy=None,cases=0,completed=0,passes=0));continue
  good=[r for r in group if r['result']['status']=='ok'];errors=[c.point(r,pol)['error']for r in good]
  summary.append(dict(arm=sel['arm'],policy=pol,cases=len(group),completed=len(good),passes=sum(e<=1e-6 for e in errors),
   worst_error=max(errors,default=None),median_error=float(np.median(errors))if errors else None))
  if not good:continue
  worst=max(good,key=lambda r:c.point(r,pol)['error']);job=next(j for j in jobs if j['id']==worst['id'])
  f=c.worker({**job,'step':'.25u','label':'final_fine_'+sel['arm'],'keep':True});delta=None;n=pol['iterations'];a=pol['average']
  if f['result']['status']=='ok':
   qc,qf=[float(np.mean(r['result']['configured_adc_samples'][n-a:n]))for r in [worst,f]]
   delta=abs((qc-qf)/(worst['case']['p']+qf))
  fine.append(dict(arm=sel['arm'],coarse_id=worst['id'],relative_readout_difference=delta,within_point_one_ppm=delta is not None and delta<.1e-6,run=f))
  print('FINE',sel['arm'],delta,flush=True)
 c.write('refinement.json',dict(runs=rows,summary=summary,fine=fine));(HERE/'refinement_partial.json').unlink(missing_ok=True)
 print('FINAL VALIDATION',json.dumps(summary),flush=True)

if __name__=='__main__':main()
