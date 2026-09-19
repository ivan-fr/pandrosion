"""Broad timed SPICE campaign with per-case results and explicit failures.
Use --quick for CI; default runs the complete matrix plus independent random cases.
"""
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor,as_completed
import argparse,json,math,random,sys,time
from model import prepare
from spice import run
from joint_spice import config
OUT=Path(__file__).parent

def worker(job):
 r,profile,temp,sign,seed=job
 cfg=config(profile,temp,sign,seed)
 try:
  result=run(r,config=cfg)
  return dict(status='completed',profile=profile,temperature_C=temp,**result,
   meets_1ppm=result['configured_adc_relative_error']<=1e-6,
   meets_1ppb=result['configured_adc_relative_error']<=1e-9)
 except Exception as e:
  return dict(status='failed',p=r['p'],X=r['originalX'],profile=profile,temperature_C=temp,config=cfg,error=f'{type(e).__name__}: {e}')

def main():
 parser=argparse.ArgumentParser();parser.add_argument('--quick',action='store_true');parser.add_argument('--workers',type=int,default=3)
 args=parser.parse_args();rng=random.Random(20260924)
 degrees=[3,4,5,7,16,31,32,127,257,4095,983039,1000000]
 xs=[math.ulp(0.),1e-300,1e-30,.125,.999999,1.,1.000001,2.,500000.,1e300,sys.float_info.max]
 pairs=[[p,x] for p in degrees for x in xs]
 pairs += [[max(3,round(10**rng.uniform(math.log10(3),6))),10**rng.uniform(-300,300)] for _ in range(16)]
 if args.quick:pairs=[[3,math.ulp(0.)],[7,.125],[32,1.000001],[1000000,sys.float_info.max]]
 cases=prepare(pairs);jobs=[]
 for i,r in enumerate(cases):
  for j,profile in enumerate(['untrimmed','trim_target']):
   jobs.append((r,profile,25 if i%2 else 85,1 if (i//2)%2 else -1,20260924+2*i+j))
 rows=[];start=time.monotonic();prefix='generalist_spice_quick' if args.quick else 'generalist_spice'
 with (OUT/(prefix+'.jsonl')).open('w') as journal,ProcessPoolExecutor(max_workers=args.workers) as pool:
  pending={pool.submit(worker,j):i for i,j in enumerate(jobs)}
  for f in as_completed(pending):
   row=dict(case_id=pending[f],**f.result());rows.append(row)
   journal.write(json.dumps(row)+'\n');journal.flush()
   if len(rows)%16==0 or len(rows)==len(jobs):print(f'{len(rows)}/{len(jobs)} transients; {sum(r["status"]=="failed" for r in rows)} execution/range failures; {time.monotonic()-start:.1f}s',flush=True)
 rows.sort(key=lambda r:r['case_id'])
 report=dict(scope='Independent reset per (p,X); timed behavioral circuits, not a fabricated programmable chip or streaming reconfiguration test',
  quick=args.quick,runs=rows,summary={})
 for profile in ['untrimmed','trim_target']:
  selected=[r for r in rows if r['profile']==profile];ok=[r for r in selected if r['status']=='completed']
  report['summary'][profile]=dict(runs=len(selected),execution_failures=len(selected)-len(ok),
   meets_1ppm=sum(r['meets_1ppm'] for r in ok),meets_1ppb=sum(r['meets_1ppb'] for r in ok),
   worst=max(ok,key=lambda r:r['configured_adc_relative_error']) if ok else None)
 (OUT/(prefix+'.json')).write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps({p:{k:v for k,v in s.items() if k!='worst'} for p,s in report['summary'].items()},indent=2))
 # Accuracy misses are reported as design failures, not hidden by a successful run.
 assert all(r['status']=='completed' for r in rows),'See retained per-case execution/range failures'
if __name__=='__main__':main()
