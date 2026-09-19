"""Finite coefficient/ADC sweep; does not use a root to initialize or update."""
from model import prepare,schedule,decode
from pathlib import Path
import json,math
import mpmath as m
m.mp.dps=80
cases=prepare([[p,X]for p in [3,32,1000000]for X in [2,500000,1e300]])
rows=[]
for r in cases:
 for bits in [12,16,20,24]:
  rnd=lambda x:round(x*2**bits)/2**bits
  Y=rnd(r['Y']);q=0.;p=r['p']
  for _ in range(6):
   d=q
   for op in schedule(p):
    if op['kind']=='square':d=d+rnd(op['product_weight'])*d*d
    else:d=d+rnd(op['copy_weight'])*(q-d)+rnd(op['product_weight'])*d*q
   t=Y*(1+d);invp=rnd(1/p)
   q=q+2*(1+q*invp)*(1-t)/(1+t+(t-1)*invp)
  q_adc=round(q/(4/2**18))*(4/2**18)
  ref=m.exp(m.log(m.mpf(r['originalX']))/p)
  rows.append(dict(p=p,X=r['originalX'],coefficient_fraction_bits=bits,q=q,adc18_error=float(abs(m.mpf(decode(r['c'],q_adc,p))/ref-1))))
Path(__file__).with_name('precision_results.json').write_text(json.dumps(rows,indent=2)+'\n')
assert all(math.isfinite(x['adc18_error']) for x in rows)
print('Finite-coefficient sweep:',len(rows),'cases; results in precision_results.json')
