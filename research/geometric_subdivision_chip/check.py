"""Meaningful checks: algebra, oracle exclusion, calibration separation, replay."""
from transistor import *
import mpmath as mp
mp.mp.dps=80
checks=0
for A in [mp.mpf('.7'),mp.mpf(1),mp.mpf('1.91')]:
 for ratio in [mp.mpf(1),mp.mpf('1.000001'),mp.mpf('1.7'),mp.mpf(2)]:
  B=A*ratio;z=ratio-1
  for t in [mp.mpf(0),mp.sqrt(2)-1,mp.mpf('.99999'),mp.mpf(1)]:
   al=(t+1)*(t+2)/12;be=(8-2*t*t)/12;ga=(t-1)*(t-2)/12
   assert min(al,be,ga)>=0
   hom=A*(al*B*B+be*A*B+ga*A*A)/(ga*B*B+be*A*B+al*A*A)
   pade=A*(12+6*(2+t)*z+(t+1)*(t+2)*z*z)/(12+6*(2-t)*z+(t-1)*(t-2)*z*z)
   assert abs(hom-pade)<mp.mpf('1e-75');checks+=1
r=json.loads((ROOT/'results/transistor.json').read_text());assert len(r)==118
train=[x for x in r if '_train'in x['id'] and x['device']=='generic']
k,o=np.linalg.lstsq(np.array([[float(x['reference']),1] for x in train]),np.array([x['final'] for x in train]),rcond=None)[0]
cal=json.loads((ROOT/'results/calibration.json').read_text())['trims']['generic'];assert np.max(np.abs(np.array(cal)-[k,o]))<1e-12
assert all((x['A'],x['B']) not in [(y['A'],y['B']) for y in train] for x in r if 'holdout'in x['id'])
replay=[]
for p,X,ident in [(3.7,2,'root_p3.7_X2_calFalse'),(1e6,500000,'root_p1000000.0_X500000_calFalse')]:
 lines,sense,meta=build(kind='root',p=p,X=X,n=6)
 assert all(not line.startswith(('F','E','G','H','B')) for line in lines if not line.startswith('*'))
 assert not re.search(r'\b(sqrt|pow|exp|log)\s*\(', '\n'.join(lines),re.I)
 result=execute(lines,sense,meta,ROOT/'results/replay_raw'/ident)
 old=next(x for x in r if x['id']==ident)
 assert abs(result['final']-old['final'])<1e-6
 assert abs(result['power_W']-old['power_W'])<1e-7
 replay.append(dict(id=ident,absolute_difference=abs(result['final']-old['final']),power_difference=abs(result['power_W']-old['power_W'])))
result=dict(algebra_cases=checks,calibration_separation=True,transistor_core_has_no_behavioral_arithmetic=True,replay=replay,scope='Verifies implementation and reported errors; does not assert that the chip meets an accuracy target')
(ROOT/'results/checks.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
