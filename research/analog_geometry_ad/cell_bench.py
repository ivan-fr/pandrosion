"""Paired frozen-input steps: warm cells, finite loading, static offsets, two poles.
Time starts at the residual change; one volt encodes one centered state unit.
"""
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor,as_completed
import json
import numpy as np
from circuit import correction_lines,execute,calibrate_correction
HERE=Path(__file__).resolve().parent

def bench(job,resolution=100):
 p,w,scale,profile,variant=job
 cfg=dict(coeff_bits=24,stage_cap=100e-9,rin=50000,gain=0.,offset=0.,correction_tau_scale=scale)
 if profile!='nominal':cfg.update(gain=.0016,offset=55e-6)
 if profile=='calibrated':cfg['correction_calibration'],_=calibrate_correction(cfg,20269901)
 tau=1e-6*scale;delay=50*tau;end=delay+60*tau
 lines=['Frozen-input AD correction bench','.options reltol=1e-9 abstol=1e-13 vntol=1e-11',
  f'Vw w 0 PWL(0 0 {delay:.17g} 0 {delay+tau*1e-4:.17g} {w:.17g})']
 lines+=correction_lines(p,cfg,variant,w='v(w)',q='0')
 lines+=['.control','set numdgt=16','set wr_singlescale','set wr_vecnames',
  f'tran {tau/resolution:.17g} {end:.17g} uic','wrdata wave.txt v(w) v(delta) v(corr_first) v(corpeak) v(innerden)',
  'quit','.endc','.end']
 data,_,_=execute('\n'.join(lines)+'\n')
 invp=round(2**24/p)/2**24;aa=(1+invp)/2;target=-w/(1+aa*w)
 selected=data[:,0]>=delay;tt=data[selected,0]-delay;dd=data[selected,2];err=abs(dd-target)
 settling={}
 for tol in [1e-3,1e-5,1e-6]:
  bad=np.flatnonzero(err>tol)
  idx=0 if not len(bad) else bad[-1]+1
  settling[str(tol)]=float(tt[idx]*1e6) if idx<len(tt) else None
 overshoot=float(max(0,-dd.min()-abs(target))) if target<0 else float(max(0,dd.max()-target))
 row=dict(p=p,w=w,tau_scale=scale,profile=profile,variant=variant,target=target,
  static_error_V=float(err[-1]),settling_us=settling,overshoot_V=overshoot,
  peak=float(data[:,4].max()),denominator_min=float(data[:,5].min()),
  status='ok' if data[:,4].max()<1.99 and data[:,5].min()>.125 else 'rejected')
 if p==3 and w==1 and scale==1 and profile=='calibrated' and resolution==100:
  np.savetxt(HERE/f'cell_{variant}.csv',np.column_stack([tt,dd,np.full_like(tt,target)]),delimiter=',',header='time_since_step,delta,target',comments='')
 return row

def main():
 jobs=[(p,w,scale,profile,variant) for p in [3,1000000] for w in [-.1,0,.0001,.01,.1,.5,1,1.1]
  for scale in [1,10] for profile in ['nominal','untrimmed','calibrated'] for variant in ['direct','feedback']]
 rows=[]
 with ProcessPoolExecutor(max_workers=3) as pool:
  futures={pool.submit(bench,j):i for i,j in enumerate(jobs)}
  for f in as_completed(futures):
   rows.append(dict(id=futures[f],**f.result()))
   if len(rows)%64==0:print('cell bench',len(rows),'/',len(jobs),flush=True)
 rows.sort(key=lambda x:x['id'])
 # Four-times finer time grid; the comparison still includes static error.
 fine=[]
 for p in [3,1000000]:
  for w in [.01,1]:
   for variant in ['direct','feedback']:
    coarse=next(r for r in rows if r['p']==p and r['w']==w and r['variant']==variant and r['tau_scale']==1 and r['profile']=='calibrated')
    f=bench((p,w,1,'calibrated',variant),resolution=400)
    a=coarse['settling_us']['1e-06'];b=f['settling_us']['1e-06']
    assert a is not None and b is not None and abs(a-b)<.05
    assert abs(coarse['static_error_V']-f['static_error_V'])<1e-9
    fine.append(dict(coarse_id=coarse['id'],settling_difference_us=abs(a-b),fine=f))
 (HERE/'cell_results.json').write_text(json.dumps(dict(scope='Frozen-input behavioral steps, two loaded cells per topology; warmup excluded, residual step included.',runs=rows,fine=fine),indent=2)+'\n')
 print('PASS:',len(rows),'frozen-input SPICE steps (accuracy misses retained)',flush=True)
if __name__=='__main__':main()
