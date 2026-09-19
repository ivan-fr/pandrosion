"""Wide deterministic coverage. No amount of sampling proves all-input hardware accuracy."""
from pathlib import Path
import json,math,random,sys,csv
import mpmath as mp
from model import prepare,update,schedule
OUT=Path(__file__).parent
SEED=20260923

def inputs():
 rng=random.Random(SEED)
 degrees=sorted(set(list(range(3,65))+[2**k+d for k in range(7,20) for d in [-1,0,1]]+[100,1000,10000,100000,983039,999983,1000000]))
 xs=[math.ulp(0.),sys.float_info.min,1e-300,1e-100,.001,.125,.5,math.nextafter(1.,0.),1.,math.nextafter(1.,2.),2.,3.,10.,500000.,1e100,1e300,sys.float_info.max]
 pairs=[(p,x,'grid') for p in degrees for x in xs]
 # Dense logarithmic sweeps in X at several representative degrees.
 pairs += [(p,10**(-300+600*i/200),'X_sweep') for p in [3,7,32,257,4095,983039,1000000] for i in range(201)]
 # Both low-degree and log/uniform large-degree random samples, independent of tuning.
 for i in range(5000):
  p=rng.randint(3,1000000) if i%2 else max(3,round(10**rng.uniform(math.log10(3),6)))
  pairs.append((p,10**rng.uniform(-300,300),'random'))
 return pairs

def main():
 pairs=inputs();cases=prepare([[p,x] for p,x,_ in pairs]);mp.mp.dps=90
 rows=[];worst={'ideal':None,'untrimmed':None,'trim_target':None}
 for i,(r,(_,_,group)) in enumerate(zip(cases,pairs)):
  p=r['p'];ref=mp.exp(-mp.log(mp.mpf(r['originalX']))/p)
  for profile,offset,gain in [('ideal',0,0),('untrimmed',25e-6,.001),('trim_target',1e-6,20e-6)]:
   q=0.;peak=0.;valid=True
   # Two correlated signs spread across cases; not a statistical corner guarantee.
   sign=1 if i%2 else -1
   for _ in range(6):
    q,t,pk=update(q,p,r['Y'],gain=sign*gain,offset=sign*offset,sum_offset=sign*offset)
    peak=max(peak,abs(q),pk)
    valid &= math.isfinite(q) and peak<2 and t>0
   # Score decoded output in high precision, including the exact stored c and q.
   err=float(abs(ref/(mp.mpf(r['c'])*(1+mp.mpf(q)/p))-1))
   row=dict(p=p,X=r['originalX'],group=group,profile=profile,Y=r['Y'],stages=len(schedule(p)),relative_error=err,valid=valid)
   rows.append(row)
   if worst[profile] is None or err>worst[profile]['relative_error']:worst[profile]=row
   if profile=='ideal':assert valid and err<1e-12,row
 with (OUT/'generalist_algorithm.csv').open('w') as f:
  w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
 result=dict(seed=SEED,input_pairs=len(cases),distinct_degrees=len(set(r['p'] for r in cases)),
  evaluations=len(rows),groups={g:sum(x[2]==g for x in pairs) for g in ['grid','X_sweep','random']},
  worst=worst,invalid=sum(not r['valid'] for r in rows),
  scope='Six-step arithmetic sweep: no stage loading, dynamic timing, ADC or thermal model; see separate timed campaign')
 (OUT/'generalist_algorithm.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
