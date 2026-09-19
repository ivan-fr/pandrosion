"""Independent scalar checks, global-start campaigns and counted gate geometry."""
from pathlib import Path
import json
import mpmath as mp
from model import Diagram,costs,circle
mp.mp.dps=180
HERE=Path(__file__).resolve().parent
records=[];kinds=set();max_steps=0;max_readout=mp.mpf(0)
for p in [3,4,5,7,16,32,1000,1000000]:
 for Xstr in ['0.01','2','500000']:
  X=mp.mpf(Xstr)
  for logt in [-30,-5,-1,1,5,30]:
   # Root-related expression only generates a test input; the circuit never sees it.
   s=mp.exp((mp.mpf(logt)-mp.log(X))/p)
   d=Diagram(p,X,s);cc=costs(p)
   assert all(d.initial_count[k]==v for k,v in cc['initial'].items())
   counts={'circle':0,'AD':0};steps=0
   while abs(mp.log(d.value(d.tpoint)))>mp.mpf('1e-45'):
    old=d.s;t=X*old**p
    r=d.step();steps+=1;counts[r['kind']]+=1;kinds.add(r['kind'])
    assert d.s>0
    expected=old*(p+1+(p-1)*t)/(p-1+(p+1)*t) if r['kind']=='AD' else old*circle.phi(p,t)
    err=abs(d.s-expected)/expected;max_readout=max(max_readout,err)
    assert err<mp.mpf('1e-100'),(p,X,logt,r,err)
    newt=X*d.s**p
    assert abs(newt-r['t_after'])/newt<mp.mpf('1e-100')
    if r['kind']=='circle':
     assert abs(mp.log(newt))<=abs(mp.log(t))/2+mp.mpf('1e-100')
     assert all(r['cost'][k]<=v for k,v in cc['accepted'].items()),r
     assert r['cost']['identity_checks']==cc['m']+2
    else:
     assert abs(mp.log(newt))<abs(mp.log(t))
     assert all(r['cost'][k]<=v for k,v in cc['rejected_after_trial'].items())
    assert steps<100
   records.append({'p':p,'X':Xstr,'logt0':logt,'steps':steps,**counts})
   max_steps=max(max_steps,steps)
# Force an otherwise valid trial to exercise the full rejection/fallback cost.
forced=[]
for p in [3,4,7,32,1000000]:
 d=Diagram(p,2,mp.exp(-mp.log(2)/p+mp.mpf('.1')/p))
 r=d.step(force_reject=True)
 assert r['kind']=='AD' and r['reason']=='candidate'
 assert all(r['cost'][k]==v for k,v in costs(p)['rejected_after_trial'].items()),r
 forced.append({'p':p,'cost':r['cost']})
# Old affine exceptional input s=1 and the exact root at X=1 remain safe.
for p in [3,4,7,1000000]:
 d=Diagram(p,2,1);r=d.step();assert d.s>0 and abs(mp.log(d.value(d.tpoint)))<mp.log(2)
 d=Diagram(p,1,1);r=d.step();assert r['kind']=='exact' and all(v==0 for v in r['cost'].values())
# A failed gate: forces fallback even when a trial is positive. Exact rail inequalities.
for t,u in [('2','2'),('0.5','0.5'),('1','2')]:
 d=Diagram(3,2,mp.mpf('.75'));d.tpoint=d.R(mp.mpf(t))
 trial=d.R((mp.mpf(u)/2)**(mp.mpf(1)/3))
 accepted,*_=d.gate(trial);assert not accepted
# Explicit affine singularities v=rho and unavailable real crossings.
exceptional=[]
for p,t,reason in [(3,'7.75','readout chart singular'),(5,'16','readout chart singular'),
                    (3,'1e-30','no transverse crossing'),(3,'1e30','no transverse crossing')]:
 d=Diagram(p,2,mp.root(mp.mpf(t)/2,p));r=d.step()
 assert r['kind']=='AD' and r['reason']==reason,r
 exceptional.append({'p':p,'t':t,'reason':reason})
# Both inverse roots are positive here: the descending-arc rule must select the right one.
d=Diagram(3,2,mp.root(mp.mpf('.05')/2,3));s=d.s;r=d.step()
assert r['kind']=='circle' and abs(d.s/s-circle.phi(3,mp.mpf('.05')))<mp.mpf('1e-100')
# The product's unit shortcut has zero joins, even on the extended rail.
for a in ['0.1','1','1000']:
 d=Diagram(3,1,1);before=d.count['J']
 assert d.mul(d.R(mp.mpf(a)),d.B)==d.R(mp.mpf(a)) and d.count['J']==before
out={'scope':'High-precision finite tests; global convergence is proved separately in Lean.',
 'digits':mp.mp.dps,'geometric_trajectories':len(records),'max_iterations':max_steps,
 'max_relative_readout_disagreement':mp.nstr(max_readout,8),'kinds':sorted(kinds),
 'forced_rejection_costs':forced,'exceptional_cases':exceptional,
 'representative_costs':{str(p):costs(p) for p in [3,4,32,1000000]},
 'trajectories':records}
(HERE/'results.json').write_text(json.dumps(out,indent=2)+'\n')
print(f'PASS: {len(records)} geometric trajectories, degrees 3..1000000, max {max_steps} steps; costs and fallback checks')
