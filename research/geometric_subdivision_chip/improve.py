"""Frozen R2 calibration procedure. No target root is evaluated by calibration.
All accuracy scoring is after electrical calibration and held-out simulation.
"""
from transistor import *
import mpmath as mp
P=ROOT/'improvement';P.mkdir(exist_ok=True)
CAP=1e-11;N=6

def sim(label,**kw):
 return execute(*build(**kw),P/'raw'/label)

def calibrate_primitives():
 gains=mod.mirror_gains(I0=1e-5,level=1.,temp=25,ikf=.05)
 feedback=1.;measurements=[]
 for j in range(3):
  r=sim(f'primitive_cal{j}',kind='mean',A=1.,B=1.,mirror_gains=gains,mean_feedback=feedback,compensation=CAP)
  if 'error'in r:raise RuntimeError(r['error'])
  measurements.append(r);feedback*=r['final']**2
 return dict(mirror_gains=gains,mean_feedback=feedback,compensation=CAP,n=N),measurements

def calibrate_output(p,X,cfg,label):
 gain=1.;measurements=[]
 # theta<=2^-N means that the retained A is the exact unit rail.
 # At lambda=0, P=Q regardless of B: a known unit output with original loads.
 ref=dict(weight_override=0.) if p>=2**N else dict(readout_reference=1.)
 for j in range(3):
  r=sim(label+f'_cal{j}',kind='root',p=p,X=X,output_gain=gain,**cfg,**ref)
  if 'error'in r:raise RuntimeError(r['error'])
  measurements.append(r);gain*=r['scale']/r['final']
 return gain,measurements

def score(r,X,p):
 if 'error'in r:return r
 mp.mp.dps=80;ref=mp.power(mp.mpf(str(X)),1/mp.mpf(str(p)))
 r['reference']=str(ref)
 r['window_error']=float(max(abs(mp.mpf(v)/ref-1) for v in [r['tail_min'],r['tail_max']]))
 r['relative_error']=float(abs(mp.mpf(r['final'])/ref-1))
 r['excess_error']=float(abs((mp.mpf(r['final'])-ref)/(ref-1))) if ref!=1 else None
 return r

def main():
 cfg,primitive=calibrate_primitives();rows=[]
 # Development examples are labelled separately from frozen-procedure holdouts.
 dev=[(3.7,2),(1e6,500000),(3,2),(37.5,500000)]
 hold=[(p,X) for p in [1.2,math.sqrt(2),2.7,7.3,22.25,64.1,1200.5,999999.75] for X in [1.3,17,120000]]
 for i,(p,X) in enumerate(dev+hold):
  gain,cal=calibrate_output(p,X,cfg,f'job{i}')
  old=score(sim(f'job{i}_old',kind='root',p=p,X=X,n=N),X,p)
  new=score(sim(f'job{i}_r2',kind='root',p=p,X=X,output_gain=gain,**cfg),X,p)
  rows.append(dict(p=p,X=X,split='development' if i<len(dev) else 'heldout',output_gain=gain,calibration=cal,old=old,r2=new))
  print(i,p,X,old.get('window_error'),new.get('window_error'),flush=True)
  (P/'results.json').write_text(json.dumps(dict(config=cfg,primitive_calibration=primitive,jobs=rows),indent=2)+'\n')
 stress=[]
 for p,X in [dev[0],dev[1]]:
  gain=next(r['output_gain'] for r in rows if r['p']==p and r['X']==X)
  for variation in [dict(temp=-20),dict(temp=85),dict(vscale=.95),dict(vscale=1.05),dict(mismatch=.001,seed=72),dict(load=1e-10),dict(startup=True),dict(ramp=True)]:
   old=score(sim(f'stress{len(stress)}_old',kind='root',p=p,X=X,n=N,**variation),X,p)
   new=score(sim(f'stress{len(stress)}_r2',kind='root',p=p,X=X,output_gain=gain,**cfg,**variation),X,p)
   stress.append(dict(p=p,X=X,variation=variation,old=old,r2=new));print('stress',len(stress),new.get('window_error',new.get('error')),flush=True)
   (P/'stress.json').write_text(json.dumps(stress,indent=2)+'\n')
 # Bidirectional single-cell transitions, with and without compensation/calibration.
 transitions=[]
 for reverse in [False,True]:
  for mode in ['old','r2']:
   kw={k:v for k,v in cfg.items() if k!='n'} if mode=='r2' else {}
   r=score(sim(f'transition_{reverse}_{mode}',kind='mean',A=1,B=2 if reverse else 1,B2=1 if reverse else 2,**kw),1 if reverse else 2,2)
   transitions.append(dict(reverse=reverse,mode=mode,measurement=r))
 (P/'transitions.json').write_text(json.dumps(transitions,indent=2)+'\n')
if __name__=='__main__':main()
