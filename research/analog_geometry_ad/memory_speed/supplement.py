"""Validate the already development-selected 10-ppm policy and loaded control."""
import json
from pathlib import Path
import numpy as np
import memory_campaign as c
import memory_model as m
HERE=Path(__file__).resolve().parent

def freeze():
 s=json.loads((HERE/'selection.json').read_text())
 control=min((p for p in s['frontier']if p['profile']=='control100' and p['worst_error']<=1e-6),key=lambda p:(p['time_ms'],p['worst_error']))
 loose=next(x['policy']for x in s['selected']if x['target_ppm']==10)
 out=[dict(arm='loaded_control',target_ppm=1.,policy=control),dict(arm='optimized_10ppm',target_ppm=10.,policy=loose)]
 c.write('secondary_selection.json',out)
 return out

def main():
 selected=json.loads((HERE/'secondary_selection.json').read_text())
 cases=m.prepare([[p,x]for p in [3,4,5,7,16,31,127,257,4095,65537,983039,1000000]for x in [.019,1.000007,1e-250,1e250]])
 jobs=[]
 for sel in selected:
  if not sel['policy']:continue
  pol=sel['policy'];prof=next(p for p in m.PROFILES if p['name']==pol['profile']);timing=next(t for t in m.SCHEDULES if t['name']==pol['timing'])
  for i,r in enumerate(cases):
   jobs.append(dict(id=len(jobs),case_id=i,label=f'{sel["arm"]}_{i}',case=r,profile=prof,timing=timing,
    temp=[85,-20,25][i%3],sign=1 if i%2 else -1,seed=20271000+i,arm=sel['arm']))
 rows=c.batch(jobs,'secondary');summary=[];fine=[]
 for sel in selected:
  pol=sel['policy']
  if not pol:continue
  group=[r for r in rows if r['arm']==sel['arm']];good=[r for r in group if r['result']['status']=='ok']
  errors=[c.point(r,pol)['error']for r in good]
  summary.append(dict(**sel,cases=len(group),completed=len(good),passes=sum(e<=sel['target_ppm']*1e-6 for e in errors),worst_error=max(errors,default=None)))
  if not good:continue
  worst=max(good,key=lambda r:c.point(r,pol)['error']);job=next(j for j in jobs if j['id']==worst['id'])
  f=c.worker({**job,'step':'.25u','label':'fine_'+sel['arm'],'keep':True});delta=None;n=pol['iterations'];a=pol['average']
  if f['result']['status']=='ok':
   qc,qf=[float(np.mean(r['result']['configured_adc_samples'][n-a:n]))for r in [worst,f]]
   delta=abs((qc-qf)/(worst['case']['p']+qf))
  fine.append(dict(arm=sel['arm'],coarse_id=worst['id'],relative_readout_difference=delta,within_point_one_ppm=delta is not None and delta<.1e-6,run=f))
 c.write('secondary.json',dict(runs=rows,summary=summary,fine=fine));(HERE/'secondary_partial.json').unlink(missing_ok=True)
 print(json.dumps(summary),flush=True)

if __name__=='__main__':main()
