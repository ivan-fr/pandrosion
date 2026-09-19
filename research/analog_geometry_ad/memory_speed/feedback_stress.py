"""Apply the same component diagnostics to the final feedback candidate."""
from pathlib import Path
import json
import memory_campaign as c
HERE=Path(__file__).resolve().parent

def main():
 source=json.loads((HERE/'sensitivity.json').read_text())
 selected=json.loads((HERE/'refinement_selection.json').read_text())
 policy=next(x['policy']for x in selected if x['arm']=='feedback')
 jobs=[]
 for row in source['runs']:
  job={k:v for k,v in row.items()if k not in ['config','calibration','result']}
  job.update(variant='feedback',label='feedback_'+row['label'],keep=False)
  jobs.append(job)
 rows=c.batch(jobs,'feedback_stress');c.write('feedback_sensitivity.json',dict(policy=policy,runs=rows))
 (HERE/'feedback_stress_partial.json').unlink(missing_ok=True)
 for row in rows:
  if row['result']['status']=='ok':print(row['label'],c.point(row,policy)['error']*1e6,'ppm',flush=True)
  else:print(row['label'],row['result']['status'],flush=True)

if __name__=='__main__':main()
