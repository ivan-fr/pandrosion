"""Independent high-precision reference, depth study, and CPU baseline.
Root/log operations occur only in this validation/reference program.
"""
from pathlib import Path
import json,math,statistics,time,random,platform
import mpmath as mp
from spice import run_case,minimum_depth,schedule,ROOT
mp.mp.dps=100

def pade(t,z):return (12+6*(2+t)*z+(t+1)*(t+2)*z*z)/(12+6*(2-t)*z+(t-1)*(t-2)*z*z)
def exact(X,p,n):
 X=mp.mpf(X);p=mp.mpf(p);theta=1/p;a=mp.mpf(0);b=mp.mpf(1);A=mp.mpf(1);B=X
 for _ in range(n):
  M=mp.sqrt(A*B);m=(a+b)/2
  if theta<=m:b,B=m,M
  else:a,A=m,M
 t=(theta-a)/(b-a);z=B/A-1
 L=A*pade(t,z);U=B/pade(1-t,z);r=mp.power(X,theta)
 width=t*(1-t)*(2-t)*(1+t)*z**5/((12+6*(2+t)*z+(t+1)*(t+2)*z*z)*(12+6*(3-t)*z+(2-t)*(3-t)*z*z))
 tol=mp.mpf('1e-90')*max(r,1)
 assert L<=r+tol and U>=r-tol
 assert abs(U/L-1-width)<mp.mpf('1e-85')*max(1,abs(width))
 assert width<=z**5/256+mp.mpf('1e-85')
 return dict(L=mp.nstr(L,45),U=mp.nstr(U,45),reference=mp.nstr(r,45),width=mp.nstr(width,25))

def float_kernel(X,p,n):
 # Complete software counterpart, including n geometric means; no log/exp/root oracle.
 theta=1/p;a=0.;b=1.;A=1.;B=X
 for _ in range(n):
  M=math.sqrt(A)*math.sqrt(B);m=(a+b)/2
  if theta<=m:b,B=m,M
  else:a,A=m,M
 t=(theta-a)/(b-a);z=B/A-1
 return A*pade(t,z),B/pade(1-t,z)

def main():
 rng=random.Random(20260925);count=0
 for X in ['1.000001','2','500000','1e12']:
  for p in ['1','1.000001',mp.sqrt(2),'3.7','37.5','1000000','1000000.125','1e9']:
   for n in [0,1,2,5,8,12,20]:exact(X,p,n);count+=1
 for _ in range(200):exact(mp.mpf(10)**rng.uniform(0,12),mp.mpf(10)**rng.uniform(0,9),rng.randrange(1,16));count+=1
 studies=[]
 for X,p in [(2.,3.7),(500000.,1e6)]:
  for n in sorted(set([minimum_depth(X),2,5,6,8,12])):
   if n<minimum_depth(X):continue
   for order in [2,3,5]:
    for profile in ['ideal','trimmed']:
     out=ROOT/'depth'/f'case_{len(studies):03d}'
     row=run_case(X,p,n,profile,order,271828,out)
     row['exact_order5']=exact(X,p,n)
     studies.append(row)
   print(f'Depth study X={X}, p={p}, n={n}',flush=True)
 timings=[]
 for X,p in [(2.,3.7),(500000.,1e6)]:
  for n in [5,8,12]:
   samples=[]
   for _ in range(9):
    start=time.perf_counter_ns()
    for j in range(10000):float_kernel(X,p,n)
    samples.append((time.perf_counter_ns()-start)/10000)
   timings.append(dict(X=X,p=p,n=n,median_ns=statistics.median(samples),min_ns=min(samples),scope='Python scalar full digital kernel; not optimized ASIC/FPGA'))
 report=dict(high_precision_checks=count,precision_decimal_digits=100,depth=studies,cpu=timings,environment=dict(platform=platform.platform(),python=platform.python_version()),scope='Numerical cross-checks complement, do not replace, Lean proofs. Hardware front-end and control timing excluded from SPICE settling.')
 (ROOT/'validation.json').write_text(json.dumps(report,indent=2)+'\n')
 print(f'{count} high-precision checks passed; {len(studies)} depth-study SPICE runs',flush=True)
if __name__=='__main__':main()
