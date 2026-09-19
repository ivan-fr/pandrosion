"""Frozen revision, independent inputs/noise seeds, paired original/revised runs."""
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor,as_completed
import json,random,math,time
from model import prepare
from spice import run
from revised_circuit import prepare_revision
from joint_spice import config
OUT=Path(__file__).parent

def worker(job):
 r,temp,sign,seed=job
 before=run(r,step='1u',config=config('untrimmed',temp,sign,seed))
 cfg,cal=prepare_revision(r['p'],temp,sign,seed)
 after=run(r,step='1u',config=cfg)
 return dict(p=r['p'],X=r['originalX'],temperature_C=temp,sign=sign,noise_seed=seed,
  before=before,after=after,calibration=cal,
  meets_1ppm=after['configured_adc_relative_error']<=1e-6,
  improved=after['configured_adc_relative_error']<before['configured_adc_relative_error'])

def main():
 degrees=[3,4,5,7,16,31,127,257,4095,65537,983039,1000000]
 pairs=[[p,x] for p in degrees for x in [1e-300,.037,1.000001,1e300]]
 rng=random.Random(20261012)
 pairs += [[max(3,round(10**rng.uniform(math.log10(3),6))),10**rng.uniform(-280,280)] for _ in range(16)]
 cases=prepare(pairs);jobs=[(r,[-20,25,85][i%3],1 if i%2 else -1,20262000+i) for i,r in enumerate(cases)]
 rows=[];start=time.monotonic()
 with ProcessPoolExecutor(max_workers=3) as pool:
  futures={pool.submit(worker,j):i for i,j in enumerate(jobs)}
  for f in as_completed(futures):
   rows.append(dict(case_id=futures[f],**f.result()))
   if len(rows)%8==0:print(len(rows),'/64 paired tests',round(time.monotonic()-start,1),'s',flush=True)
 rows.sort(key=lambda r:r['case_id'])
 # Independent timestep and averaging checks on worst low-degree validation case.
 worst=max(rows,key=lambda r:r['after']['configured_adc_relative_error'])
 r=cases[worst['case_id']];fine=run(r,step='.25u',config=worst['after']['config'])
 assert abs(fine['configured_adc_q']-worst['after']['configured_adc_q'])<.5e-6
 summary=dict(pairs=len(rows),meets_1ppm=sum(x['meets_1ppm'] for x in rows),
  improved=sum(x['improved'] for x in rows),worst_after=max(x['after']['configured_adc_relative_error'] for x in rows),
  worst_before=max(x['before']['configured_adc_relative_error'] for x in rows))
 report=dict(scope='Held-out behavioral validation. Additional calibrated sources, 24-bit ADC, 100 nF memory, long acquisition and 16-result averaging; not measured hardware.',
  fixed_design='revised_circuit.revision; frozen before this campaign',summary=summary,runs=rows,fine_check=dict(case_id=worst['case_id'],run=fine))
 (OUT/'revised_validation.json').write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps(summary,indent=2))
 # Do not suppress an accuracy miss by only checking finite outputs.
 assert summary['meets_1ppm']==len(rows),'Revision misses the declared target; failures retained in JSON'
if __name__=='__main__':main()
