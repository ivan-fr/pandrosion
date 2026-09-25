"""Reproducible transistor campaign; references are used only AFTER simulation."""
from transistor import *
import mpmath as mp
mp.mp.dps=80
OUT=ROOT/'results';OUT.mkdir(exist_ok=True)
rows=[]
def run(label,reference=None,**kw):
 dt=kw.pop('dt',1e-9);duration=kw.pop('duration',2e-6)
 try:r=execute(*build(**kw),OUT/'raw'/label,dt=dt,duration=duration)
 except (subprocess.TimeoutExpired,ValueError) as e:r=dict(error=str(e),**kw)
 r['id']=label
 if 'final' in r:
  ref=mp.mpf(reference) if reference is not None else (mp.sqrt(mp.mpf(str(kw.get('A2',kw.get('A',1))))*mp.mpf(str(kw.get('B2',kw.get('B',2))))) if kw.get('kind','mean')=='mean' else mp.exp(mp.log(mp.mpf(str(kw.get('X',2))))/mp.mpf(str(kw.get('p',3.7)))))
  r['reference']=str(ref);r['relative_error']=float(abs(mp.mpf(r['final'])/ref-1));r['excess_relative_error']=float(abs((mp.mpf(r['final'])-ref)/(ref-1))) if ref!=1 else None
  a=np.loadtxt(OUT/'raw'/label/'trace.txt',skiprows=1);t=a[:,0];v=a[:,1]/r['I0']*r['scale'];err=np.abs(v/float(ref)-1)
  r['window_error']=float(np.max(err[t>.8*duration]));r['settling_to_truth_s']={}
  start=0 if r.get('startup') else (100e-9+r.get('edge',1e-8) if ('A2'in kw or 'B2'in kw) else 0)
  for tol in [1e-4,1e-5,1e-6]:
   bad=np.flatnonzero((t>=start)&(err>tol));sel=np.flatnonzero(t>=start)
   r['settling_to_truth_s'][str(tol)]=(float(t[bad[-1]+1]-start) if bad.size and bad[-1]+1<len(t) else (0. if not bad.size and len(sel) else None))
 rows.append(r);print(label,r.get('relative_error',r.get('error')),flush=True)
 (OUT/'campaign-progress.json').write_text(json.dumps(rows,indent=2)+'\n')
 return r

def main():
 trims={}
 for device in ['generic','sky130']:
  train=[]
  for j,(u,v) in enumerate([(1,1),(1.25,1.25),(1.5,1.5),(1,1.5),(1.25,1.5)]):
   r=run(f'{device}_train{j}',device=device,A=u*u,B=v*v,reference=str(u*v));train.append(r)
  good=[r for r in train if 'final'in r];x=np.array([float(r['reference']) for r in good]);y=np.array([r['final'] for r in good]);k,o=np.linalg.lstsq(np.column_stack([x,np.ones(len(x))]),y,rcond=None)[0];trims[device]=[float(k),float(o)]
  for calibrated in [False,True]:
   for j,(a,b) in enumerate([(1.1,1.7),(.81,1.69),(1.21,2.56),(1.7,1.1)]):
    run(f'{device}_holdout{j}_{calibrated}',device=device,A=a,B=b,trim=trims[device] if calibrated else None)
 (OUT/'calibration.json').write_text(json.dumps(dict(training='five rational-square/diagonal currents; 25C, 1pF, 1kohm, I0=10uA',trims=trims),indent=2)+'\n')
 # Freeze n=6 for the common held-out grid; depth sweep reported separately.
 for p in [3,7,32,1e6,1.01,2**.5,3.7,37.5,1000000.125]:
  for X in [2,500000]:
   for cal in [False,True]:run(f'root_p{p}_X{X}_cal{cal}',kind='root',p=p,X=X,n=6,trim=trims['generic'] if cal else None)
 for p,X in [(3.7,2),(1e6,500000)]:
  for n in [1,2,4]:run(f'depth_p{p}_n{n}',kind='root',p=p,X=X,n=n)
 for device in ['generic','sky130']:
  for temp in [-20,25,85]:
   for vs in [.95,1.05]:run(f'pvt_{device}_{temp}_{vs}',kind='root',p=3.7,X=2,n=6,device=device,temp=temp,vscale=vs,trim=trims[device])
  for n in [1,2,4,6]:run(f'cascade_{device}_{n}',kind='rails',device=device,p=1e6,X=500000,n=n,reference=str(mp.power(500000,mp.mpf(1)/2**n)))
 for seed in range(1,11):run(f'mismatch{seed}',kind='root',p=3.7,X=2,n=6,mismatch=.001,seed=seed)
 for load in [1e-12,10e-12,100e-12]:
  for edge in [1e-9,100e-9]:
   for reverse in [False,True]:
    run(f'step_{load}_{edge}_{reverse}',A=1,B=2 if reverse else 1,B2=1 if reverse else 2,load=load,edge=edge,trim=trims['generic'])
 for kw in [dict(kind='mean'),dict(kind='root',p=3.7,X=2,n=6),dict(kind='root',p=1e6,X=500000,n=6)]:
  for device in ['generic','sky130']:run(f'start_{device}_{kw.get("p",0)}',**kw,device=device,startup=True,duration=5e-6)
 for dt in [1e-9,.25e-9]:run(f'timestep_{dt}',A=1,B=1,B2=2,dt=dt)
if __name__=='__main__':
 main()
 (OUT/'transistor.json').write_text(json.dumps(rows,indent=2)+'\n')
