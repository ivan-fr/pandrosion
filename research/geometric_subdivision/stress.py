"""Independent noninteger-p stress cases and input/output resolution sensitivity."""
import json,random
from spice import ROOT,PROFILES,run_case,minimum_depth

def main():
 rng=random.Random(8675309);rows=[];out=ROOT/'stress';out.mkdir(exist_ok=True)
 for k in range(64):
  X=10**rng.uniform(0,12);p=10**rng.uniform(0,9);n=max(2,minimum_depth(X))
  for profile in ['ideal','trimmed']:
   row=run_case(X,p,n,profile,5,20260925+k,out/f'case_{len(rows):03d}');rows.append(row)
  if k%16==15:print(f'{len(rows)} random-p SPICE cases',flush=True)
 resolution=[]
 for bits in [12,16,18,20,24]:
  name=f'resolution{bits}';PROFILES[name]=dict(PROFILES['ideal'],dac_bits=bits,adc_bits=bits)
  row=run_case(500000.,1e6,6,name,5,271828,out/f'bits_{bits}');resolution.append(row)
 (out/'summary.json').write_text(json.dumps(dict(seed=8675309,scope='64 reproducible noninteger input pairs, X in [1,1e12], p in [1,1e9]; not exhaustive',rows=rows,resolution=resolution),indent=2)+'\n')
if __name__=='__main__':main()
