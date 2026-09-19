"""Continuous stage-state simulation across successive programmable jobs.
Input is a stream of digital (p,X), not an analog signal tracked without resets.
"""
from pathlib import Path
import json,random
from model import prepare
from clock_modes import adaptive

def main():
 rng=random.Random(20260925)
 pairs=[[p,10**(-300+15*i)] for p in [3,32,983039,1000000] for i in range(41)]
 pairs += [[rng.choice([3,7,31,257,4095,983039,1000000]),10**rng.uniform(-300,300)] for _ in range(32)]
 cases=prepare(pairs);state=None;time=0.;rows=[]
 for i,r in enumerate(cases):
  result=adaptive(r,initial_state=state,slots=37)
  state=result.pop('final_stage_state');time+=result['total_time_s']
  assert result['relative_error']<1e-6,result
  rows.append(dict(job=i,stream_time_s=time,**result))
 Path(__file__).with_name('streaming_results.json').write_text(json.dumps(dict(
  scope='Ideal reset of q and instantaneous coefficient programming at each job; analog stage states retained in 37 slots; no noise, converter latency or physical bypass switches',
  jobs=len(rows),total_analog_compute_s=time,worst_relative_error=max(r['relative_error'] for r in rows),runs=rows),indent=2)+'\n')
 print('PASS',len(rows),'streamed jobs; retained stage states; worst relative error',max(r['relative_error'] for r in rows))
if __name__=='__main__':main()
