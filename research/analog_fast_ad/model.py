"""P5 research model: centered-state exact AD and normalized binary powers."""
from pathlib import Path
import json,subprocess,math
ROOT=Path(__file__).resolve().parents[2]
def prepare(inputs):
 return json.loads(subprocess.check_output(['node',str(Path(__file__).with_name('prepare.mjs')),'--stdin'],input=json.dumps(inputs),cwd=ROOT,text=True))
def schedule(p):
 if not isinstance(p,int) or not 3<=p<=1000000:raise ValueError('Supported integer p: 3..1,000,000')
 n=1;ops=[]
 for bit in bin(p)[3:]:
  ops.append(dict(kind='square',n=n,product_weight=n/(2*p)));n*=2
  if bit=='1':ops.append(dict(kind='multiply',n=n,copy_weight=1/(n+1),product_weight=n/(p*(n+1))));n+=1
 assert n==p
 return ops

def centered_power(q,p,gain=0.,offset=0.,sum_offset=0.):
 d=q;peak=abs(q)
 for op in schedule(p):
  n=op['n']
  if op['kind']=='square':d=d+op['product_weight']*((1+gain)*d*d+offset)+sum_offset
  else:d=d+op['copy_weight']*(q-d)+op['product_weight']*((1+gain)*d*q+offset)+sum_offset
  peak=max(peak,abs(d))
 return 1+d,peak

def update(q,p,Y,**errors):
 power,peak=centered_power(q,p,**errors);t=Y*power
 return q+2*(1+q/p)*(1-t)/(1+t+(t-1)/p),t,peak

def decode(c,q,p):return 1/(c*(1+q/p))

def experiment():
 import mpmath as mp
 mp.mp.dps=100
 cases=prepare([[p,X]for p in [3,4,7,32,100,1000,1000000]for X in [1e-300,.125,2,500000,1e300]])
 rows=[]
 for r in cases:
  p=r['p'];q=0.;states=[]
  for i in range(6):q,t,peak=update(q,p,r['Y']);states.append(dict(q=q,t=t,peak=peak))
  reference=mp.exp(mp.log(mp.mpf(r['originalX']))/p)
  # Initialization is evaluated separately: it already does significant digital work.
  baseline=abs(mp.mpf(1)/mp.mpf(r['c'])/reference-1)
  err=abs(mp.mpf(decode(r['c'],q,p))/reference-1)
  rows.append(dict(**r,stages=len(schedule(p)),initial_relative_error=str(baseline),final_relative_error=str(err),states=states))
  assert err<mp.mpf('1e-12')
 # Stress is an algorithm-level deterministic corner sweep, not device Monte Carlo.
 stresses=[]
 for r in cases:
  for sign in [-1,1]:
   q=0.
   for _ in range(6):q,_,_=update(q,r['p'],r['Y'],gain=sign*1e-3,offset=sign*25e-6,sum_offset=sign*25e-6)
   ref=mp.exp(mp.log(mp.mpf(r['originalX']))/r['p'])
   stresses.append(dict(p=r['p'],X=r['originalX'],sign=sign,q=q,relative_error=float(abs(mp.mpf(decode(r['c'],q,r['p']))/ref-1))))
 result=dict(scope='Algorithm and deterministic error sensitivity; not a transistor simulation',cases=rows,stresses=stresses,
  sensitivity_example=dict(p=1000000,offset_volts=25e-6,raw_log_residual_error=1e6*math.log1p(25e-6),centered_log_residual_error=1e6*math.log1p(25e-6/1e6)))
 Path(__file__).with_name('model_results.json').write_text(json.dumps(result,indent=2)+'\n')
 print('PASS:',len(rows),'initialized cases;',len(stresses),'deterministic stress cases; max ideal error',max(float(r['final_relative_error'])for r in rows))
 print(next(r for r in rows if r['p']==1000000 and r['originalX']==500000))
if __name__=='__main__':experiment()
