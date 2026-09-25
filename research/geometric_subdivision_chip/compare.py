"""Rerun original V30/P6 with their electrical calibrations; assumptions explicit."""
from pathlib import Path
import sys,json
P=Path(__file__).resolve().parent
sys.path.insert(0,str(P/'vendor/previous'))
import single_pass as S
import policies
from revised_circuit import prepare_revision
from spice import run as v30run

def main():
 rows=[]
 for case in S.prepare([[p,x] for p in [3,7,32,1000000] for x in [2,500000]]):
  cfg,cal=prepare_revision(case['p'],25,1,20261001)
  # Same electrical cell and ADC calibration; V30 keeps its required memories.
  cfg.update(cycles=4,output_average_count=2)
  v=v30run(case,step='1u',config=cfg)
  r=S.run(case,'ad1',cfg)
  times,errs=policies.errors(r,case)
  scores={k:errs[k][min(range(len(times)),key=lambda j:abs(times[j]-t))] for k,t in [('single',32e-6),('avg16',180e-6)]}
  rows.append(dict(p=case['p'],X=case['originalX'],Y=case['Y'],c=case['c'],calibration=cal,V30=v,P6=r,P6_policy_errors=scores))
  print(case['p'],case['originalX'],v['configured_adc_relative_error'],scores,flush=True)
  (P/'results/comparison.json').write_text(json.dumps(rows,indent=2)+'\n')
if __name__=='__main__':main()
