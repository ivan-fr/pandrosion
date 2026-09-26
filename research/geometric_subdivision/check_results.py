"""Audit recorded campaigns against an independent high-precision electrical target."""
import json
import mpmath as mp
from spice import ROOT
mp.mp.dps=80

def target(X,p,n,order):
 X,p=mp.mpf(X),mp.mpf(p);theta=1/p;a=mp.mpf(0);b=mp.mpf(1)
 for _ in range(n):
  mid=(a+b)/2
  if theta<=mid:b=mid
  else:a=mid
 A=X**a;B=X**b;t=(theta-a)/(b-a);z=B/A-1
 if order==2:return A*(1+z)/(1+(1-t)*z),A*(1+t*z)
 if order==3:R=lambda t:(2+(1+t)*z)/(2+(1-t)*z)
 else:R=lambda t:(12+6*(2+t)*z+(t+1)*(t+2)*z*z)/(12+6*(2-t)*z+(t-1)*(t-2)*z*z)
 return A*R(t),B/R(1-t)

def main():
 j=json.loads((ROOT/'results/summary.json').read_text());v=json.loads((ROOT/'validation.json').read_text());s=json.loads((ROOT/'stress/summary.json').read_text())
 a=json.loads((ROOT/'accuracy/summary.json').read_text());rows=j['rows']+v['depth']+s['rows']+s['resolution']+a['rows'];assert len(rows)==517
 assert all('error' not in r for r in rows)
 checked=0;worst=0
 for r in rows:
  if r['profile']!='ideal':continue
  low,high=target(r['X'],r['p'],r['n'],r['order'])
  discrepancy=max(abs(mp.mpf(r['lower'])/low-1),abs(mp.mpf(r['upper'])/high-1))
  assert discrepancy<mp.mpf('1e-8'),(r,discrepancy)
  worst=max(worst,float(discrepancy));checked+=1
 result=dict(status='PASS',spice_runs=len(rows),ideal_spice_vs_independent_reference_cases=checked,worst_relative_electrical_discrepancy=worst,threshold=1e-8,high_precision_checks=v['high_precision_checks'],note='The tolerance allows SPICE solver and finite-leakage error; this is not a proof of interval certification.')
 (ROOT/'audit.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
