"""Reproducible illustrative mismatch study, not a fabrication yield prediction.
Errors below are chosen stress parameters, not specifications of AD734 or a PDK.
"""
from pathlib import Path
import json
import numpy as np
import mpmath as mp
OUT=Path(__file__).parent

def ad(p,m,s):return s*(p+1+(p-1)*m*s**p)/(p-1+(p+1)*m*s**p)
def halley(p,m,y):return y*((p-1)*y**p+(p+1)*m)/((p+1)*y**p+(p-1)*m)

def ideal_checks():
 with mp.workdps(100):
  rows=[];cases=0
  for p in [2,3,4,8,16,32,64]:
   for m0 in ['1','1.01','1.25','1.5','2']:
    m=mp.mpf(m0);a=m**(-mp.mpf(1)/p);s=mp.mpf(1);y=mp.mpf(1)
    maxerr=mp.mpf(0);states=[]
    for k in range(5):
     sn=ad(p,m,s);yn=halley(p,m,y)
     assert abs(1/sn-yn)<mp.mpf('1e-90')
     assert sn>=a-mp.mpf('1e-95') and sn<=s+mp.mpf('1e-95')
     s,y=sn,yn;cases+=1
     states.append(float(abs(y/m**(mp.mpf(1)/p)-1)))
    rows.append({'p':p,'m':float(m),'inverse_output_relative_errors':states})
  # Independent rounded state perturbations: derivative ratio p-1.
  for p in [2,3,16,64]:
   a=mp.power(2,-mp.mpf(1)/p);r=1/a;delta=mp.mpf('1e-20')
   inv=(1/(a+delta)/r-1)/delta;geo=(2*(a+delta)**(p-1)/r-1)/delta
   assert abs(geo/inv+(p-1))<mp.mpf('1e-15')
 return cases,rows

def monte_carlo(p,n=2000,seed=1729):
 rng=np.random.default_rng(seed+p)
 # Fixed random mismatch per abstract arithmetic block and per virtual chip.
 m=rng.uniform(1,2,n);r=m**(1/p);s=np.ones(n)
 gain=rng.normal(0,1e-3,(p,n));offset=rng.normal(0,1e-4,(p,n))
 gnum,gden,gupdate,gout_i,gout_g=rng.normal(0,1e-3,(5,n))
 onum,oden,oupdate,oout_i,oout_g=rng.normal(0,1e-4,(5,n))
 al=(p-1)/(p+1);clamps=0
 def chain(state):
  q=state.copy();prior=q.copy()
  for j in range(2,p+1):
   prior=q.copy();q=(1+gain[j-2])*q*state+offset[j-2]
  t=(1+gain[p-1])*m*q+offset[p-1]
  return prior,t
 for k in range(12):
  prior,t=chain(s)
  num=(1+gnum)*(1+al*t)+onum;den=(1+gden)*(al+t)+oden
  sn=(1+gupdate)*s*num/den+oupdate+rng.normal(0,5e-5,n)
  clamps+=int(np.sum((sn<.5)|(sn>1.2)))
  s=np.clip(sn,.5,1.2)
 prior,t=chain(s)
 inv=(1+gout_i)/s+oout_i+rng.normal(0,5e-5,n)
 geo=(1+gout_g)*m*prior+oout_g+rng.normal(0,5e-5,n)
 def stats(y):
  e=(y/r-1)*1e6
  return {'median_abs_ppm':float(np.median(abs(e))),'p95_abs_ppm':float(np.quantile(abs(e),.95)),'max_abs_ppm':float(max(abs(e))),'mean_signed_ppm':float(np.mean(e))}
 return {'p':p,'samples':n,'state_clamps':clamps,'inverse':stats(inv),'geometry':stats(geo)}

def sensitivity():
 rows=[]
 for p in [2,3,4,8,16,32,64]:
  m=2.;a=m**(-1/p);r=1/a;delta=1e-4
  # A pure state hold bias, and a separate common residual measurement bias.
  eta=1e-3;biased=(m*(1+eta))**(-1/p)
  rows.append({'p':p,'state_bias_volts':delta,'inverse_state_bias_ppm':(1/(a+delta)/r-1)*1e6,'geometry_state_bias_ppm':(m*(a+delta)**(p-1)/r-1)*1e6,'residual_gain_error':eta,'inverse_residual_bias_ppm':(1/biased/r-1)*1e6,'geometry_residual_bias_ppm':(m*biased**(p-1)/r-1)*1e6})
 return rows

def main():
 cases,ideal=ideal_checks()
 out={'status':'passed','ideal_reciprocity_checks':cases,'ideal':ideal,'monte_carlo_assumptions':{'chips_per_degree':2000,'degrees':[2,3,4,8,16],'seed':1729,'gain_sigma':.001,'offset_sigma_volts':.0001,'per_update_noise_sigma_volts':.00005,'output_noise_sigma_volts':.00005,'updates':12,'input_m_uniform':[1,2],'distribution':'independent Gaussian mismatches, fixed within each simulated chip','limitation':'Illustrative behavioral stress, not process corners or predicted yield; ignores analog bandwidth.'},'monte_carlo':[monte_carlo(p) for p in [2,3,4,8,16]],'sensitivity':sensitivity()}
 (OUT/'error_results.json').write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps({'checks':cases,'monte_carlo':out['monte_carlo']},indent=2))
if __name__=='__main__':main()
