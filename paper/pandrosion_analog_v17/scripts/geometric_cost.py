"""Reproducible operation counts and high precision iteration comparisons.
Counts describe explicit protocols, not minimality or measured wall-clock time.
"""
from pathlib import Path
import json
import mpmath as mp
from fractions import Fraction as Q
OUT=Path(__file__).parent

def steps(method,p,X,s,d,dps):
 with mp.workdps(dps):
  X=mp.mpf(X);s=mp.mpf(s);r=mp.root(X,p);u=X*s**(p-1)
  eps=mp.power(10,-d)
  for n in range(20000):
   v=u if method=='bilateral' else X*s**(p-1)
   if abs(v/r-1)<=eps:return n
   if method=='raw':s=1-(X-1)/(X*sum(s**j for j in range(p)))
   elif method=='AK':s=p*s/(p-1+X*s**p)
   elif method=='AD':s=s*(p+1+(p-1)*X*s**p)/(p-1+(p+1)*X*s**p)
   elif method=='bilateral':
    assert p==3
    R=X/u**3;u=u*(2*R+1)/(R+2)
  raise ValueError('iteration cap')

def exact_cubic_count(method,d):
 X=Q(2);s=Q(3,4);u=X*s*s;eps=Q(1,10**d)
 if method=='raw':
  # Directed fixed-grid rational enclosure avoids exponential fraction growth.
  lower=upper=s;grid=10**(d+35)
  for n in range(500):
   vlo=2*lower**2;vhi=2*upper**2
   if X*(1-eps)**3<=vlo**3 and vhi**3<=X*(1+eps)**3:return n
   assert vhi**3<X*(1-eps)**3 or vlo**3>X*(1+eps)**3
   fl=1-Q(1)/(2*(1+lower+lower**2));fh=1-Q(1)/(2*(1+upper+upper**2))
   lower=Q((fl*grid).__floor__(),grid);upper=Q((fh*grid).__ceil__(),grid)
  raise ValueError('interval iteration cap')
 for n in range(150):
  v=u if method=='bilateral' else X*s*s
  # Exact equivalence to relative root error <= epsilon, no root oracle.
  if X*(1-eps)**3<=v**3<=X*(1+eps)**3:return n
  if method=='raw':s=1-Q(1)/(2*(1+s+s*s))
  elif method=='AK':s=3*s/(2+2*s**3)
  elif method=='AD':s=s*(4+4*s**3)/(2+8*s**3)
  else:
   R=X/u**3;u=u*(2*R+1)/(R+2)
 raise ValueError('exact iteration cap')

# Verify the optimized fixed-anchor compass construction over the earlier grid.
anchor_checks=0
for p in list(range(2,17))+[24,32,64]:
 for X in map(Q,['1/4','1/2','1','2','3','7','20']):
  for s in map(Q,['1/10','1/2','3/4','1','5/4','2']):
   W=X;H=2*X;E=(W,H*(1-s**p));AE=H-E[1]
   F=(W-2*W/(p-1),H-H*Q(p+1,p-1)/X)
   D=(F[0],F[1]-AE)
   assert D==(W-2*W/(p-1),E[1]-H*Q(p+1,p-1)/X)
   assert D[1]<F[1] and (D[1]-F[1])**2==AE**2
   anchor_checks+=1
rows=[]
for d in [6,12,30,60]:
 row={'relative_digits':d}
 for m in ['raw','AK','AD','bilateral']:
  n=steps(m,3,'2','.75',d,180)
  assert n==steps(m,3,'2','.75',d,260)==exact_cubic_count(m,d)
  # A common rectangle+axes, M, P and initial visible length are given.
  # Standalone root segment at end: last partial telescope included.
  setup={'raw':1,'AK':8,'AD':0,'bilateral':0}[m]
  total=0 if n==0 else (112*n if m=='bilateral' else setup+(34 if m=='AD' else 32)*n+16)
  row[m]={'steps':n,'elementary_traces':total}
 row['compact_halley']={'steps':row['bilateral']['steps'],'elementary_traces':27*row['bilateral']['steps']+1}
 rows.append(row)

sweep=[]
for p in [3,4,8,16,32,64]:
 for start in ['0.1','0.5','0.75','1','2','10']:
  # Numerical checks at two precisions; no exact-rational certification claimed here.
  counts={m:steps(m,p,'2',start,30,180) for m in ['raw','AK','AD']}
  assert counts=={m:steps(m,p,'2',start,30,260) for m in counts}
  totals={}
  for m,n in counts.items():
   extra=0 if m!='AD' else 2
   # Excludes method-specific initialization outside the cubic worked example.
   totals[m]=(10*p+2+extra)*n+10*p-14 if n else 0
   if m=='raw' and start=='1':totals[m]=None  # Geometric raw intersection is degenerate.
  sweep.append({'p':p,'X':2,'s0':start,'relative_digits':30,'steps':counts,'traces_excluding_specific_setup':totals})
result={'model':{'join':{'lines':1,'circles':0},'parallel':{'lines':2,'circles':3},'length_transfer':{'lines':0,'circles':1},'point_selections_counted':False,'compass_type':'retains aperture; circle or useful arc counts as one trace','wall_clock_measured':False},'cubic_reference':{'X':2,'s0':'3/4','u0':'9/8','exact_threshold_certification':True,'rows':rows},'sweep':sweep,'fixed_anchor_exact_checks':anchor_checks,'asymptotic_AD_over_AK':{'cubic_with_parallel_expansion':float(mp.log(2)/mp.log(3)*Q(34,32)),'cubic_macro_equal_weights':float(mp.log(2)/mp.log(3)*Q(10,8)),'general_formula':'log(2)/log(3) * (10*p+4)/(10*p+2)'}}
(OUT/'geometric_cost_results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'cubic':rows,'asymptotic':result['asymptotic_AD_over_AK'],'sweep_AD_wins':sum(x['traces_excluding_specific_setup']['AD']<x['traces_excluding_specific_setup']['AK'] for x in sweep),'sweep_cases':len(sweep)},indent=2))
