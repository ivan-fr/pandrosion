"""Same-host mpmath microbenchmark; not compiled-code or hardware latency."""
from pathlib import Path
import time,json,platform,subprocess,random,statistics
import mpmath as mp
P=Path(__file__).resolve().parents[1];mp.mp.dps=140
methods=['Newton','Halley','AD inverse','mpmath.root']
ps=[3,4,8,16,32];inputs=[mp.mpf('1.125'),mp.mpf('1.25'),mp.mpf('1.5'),mp.mpf('2')]
refs={(p,str(x)):mp.root(x,p)for p in ps for x in inputs}
eps=mp.mpf('1e-60')
def solve(method,p,x):
 if method=='mpmath.root':return mp.root(x,p),None
 r=refs[p,str(x)];z=mp.mpf(1)
 for n in range(1000):
  y=1/z if method=='AD inverse' else z
  if abs(y/r-1)<=eps:return y,n
  if method=='Newton':z=((p-1)*z+x/z**(p-1))/p
  elif method=='Halley':
   t=z**p;z=z*((p-1)*t+(p+1)*x)/((p+1)*t+(p-1)*x)
  else:
   t=x*z**p;z=z*((p+1)+(p-1)*t)/((p-1)+(p+1)*t)
 raise AssertionError('iteration cap')
checks=[]
for p in ps:
 for x in inputs:
  for method in methods:
   y,n=solve(method,p,x);err=abs(y/refs[p,str(x)]-1)
   assert err<=eps
   checks.append(dict(p=p,x=str(x),method=method,steps=n,error=str(err)))
# Warm-up once; batch 25 complete sweeps of four x values, nine shuffled rounds.
for p in ps:
 for method in methods:
  for x in inputs:solve(method,p,x)
rng=random.Random(17092026);timings={(p,m):[]for p in ps for m in methods}
for rnd in range(9):
 order=list(timings);rng.shuffle(order)
 for p,method in order:
  t=time.perf_counter_ns()
  for k in range(25):
   for x in inputs:solve(method,p,x)
  us=(time.perf_counter_ns()-t)/100/1000;timings[p,method].append(us)
rows=[]
for (p,m),vals in timings.items():
 rows.append(dict(p=p,method=m,median_us=statistics.median(vals),q1_us=sorted(vals)[2],q3_us=sorted(vals)[6],rounds_us=vals,steps=[x['steps'] for x in checks if x['p']==p and x['method']==m]))
try:cpu=subprocess.check_output(['sysctl','-n','machdep.cpu.brand_string'],text=True).strip()
except Exception:cpu=platform.processor()
meta=dict(python=platform.python_version(),mpmath=mp.__version__,backend=mp.libmp.BACKEND,platform=platform.platform(),cpu=cpu,dps=140,target_relative_error='1e-60',rounds=9,solves_per_round=100,seed=17092026,scope='Python+mpmath, oracle stopping included; references and setup excluded; root computes full working precision')
(P/'data/benchmark.json').write_text(json.dumps(dict(metadata=meta,rows=rows,checks=checks),indent=2)+'\n')
print(meta)
for row in rows:print(row['p'],row['method'],round(row['median_us'],2),row['steps'])
