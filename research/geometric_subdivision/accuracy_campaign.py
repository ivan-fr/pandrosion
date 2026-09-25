"""Compare readout orders at the same a-priori ideal relative-width target.
Depth planning uses only integer binary exponents and rational arithmetic.
For X<2^(e+1), h=(e+1)/2^n gives z<exp(h)-1<=h/(1-h).
The classical width estimates are z²/4, z³/16 and z⁵/256.
The order-five estimate is checked in Lean; the others are independently tested.
"""
import json,math
from spice import ROOT,run_case
from check_results import target

def plan(X,order,tolerance):
 e=max(0,math.frexp(X)[1]-1);n=0
 while True:
  h=(e+1)/2**n
  if h<1 and (h/(1-h))**order/{2:4,3:16,5:256}[order]<=tolerance:return n
  n+=1

def main():
 source=json.loads((ROOT/'results/summary.json').read_text())['rows']
 pairs=sorted(set((r['X'],r['p']) for r in source));rows=[];out=ROOT/'accuracy';out.mkdir(exist_ok=True)
 for X,p in pairs:
  for order in [2,3,5]:
   n=plan(X,order,1e-6);L,U=target(X,p,n,order)
   assert U/L-1<=1e-6
   for profile in ['ideal','trimmed']:
    row=run_case(X,p,n,profile,order,271828,out/f'case_{len(rows):03d}');row['ideal_width_target']=1e-6;rows.append(row)
  print(f'Equal-target comparison X={X:g} p={p:g}',flush=True)
 (out/'summary.json').write_text(json.dumps(dict(relative_width_target=1e-6,rows=rows,scope='Fixed target for exact arithmetic; electrical errors are measured separately.'),indent=2)+'\n')
if __name__=='__main__':main()
