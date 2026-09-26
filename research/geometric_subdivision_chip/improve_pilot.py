"""Measured reference calibration, using a loop feedback ratio and output mirror trim.
Calibration A=B=r is exact for all lambda. Never fits a target root.
"""
from transistor import *
P=ROOT/'improvement';P.mkdir(exist_ok=True)
def sim(label,**kw):
 r=execute(*build(**kw),P/'raw'/label)
 print(label,r.get('final',r.get('error')),flush=True)
 return r
if __name__=='__main__':
 rows=[]
 for cap in [0,1e-12,10e-12]:
  for fb in [1.,.99]:
   r=sim(f'gm_cap{cap}_fb{fb}',kind='mean',A=1,B=1,mean_feedback=fb,compensation=cap);rows.append(r)
 for p,X in [(3.7,2),(1e6,500000)]:
  cal=sim(f'cal{p}',kind='root',p=p,X=X,n=6,readout_reference=1.)
  gain=1/cal['final'] # ea=0 for these jobs; general code uses scale.
  for fb in [1.,.992]:
   r=sim(f'val{p}_{fb}',kind='root',p=p,X=X,n=6,output_gain=gain,mean_feedback=fb);r['relative_error']=abs(r['final']/X**(1/p)-1);rows.append(r)
 (P/'pilot.json').write_text(json.dumps(rows,indent=2)+'\n')
