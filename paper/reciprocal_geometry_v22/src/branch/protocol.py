"""Independent geometric trajectories and accuracy/work table for V22."""
from pathlib import Path
import sys,json
import mpmath as mp
ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'research/fixed_circle_safeguard'))
from branch_entry import BranchEntryDiagram,branch_costs
from model import circle
mp.mp.dps=180
records=[];maximum=mp.mpf(0)
for p in [3,4,5,7,16,32,1000,1000000]:
 for Xstr in ['.01','2','500000']:
  X=mp.mpf(Xstr)
  for ell in [-30,-5,-1,1,5,30]:
   d=BranchEntryDiagram(p,X,mp.exp((ell-mp.log(X))/p));cc=branch_costs(p)
   count={'circle':0,'AD':0};steps=0
   tau=(7*p*p-4+4*p*mp.sqrt(3*(p*p-1)))/(p*p-4);band=mp.log(tau)
   while abs(mp.log(d.value(d.tpoint)))>mp.mpf('1e-45'):
    old=d.s;t=X*old**p;r=d.step();steps+=1;count[r['kind']]+=1
    expected=old*circle.phi(p,t) if r['kind']=='circle' else old*(p+1+(p-1)*t)/(p-1+(p+1)*t)
    err=abs(d.s/expected-1);maximum=max(maximum,err);assert err<mp.mpf('1e-100')
    newt=X*d.s**p;assert abs(mp.log(newt))<abs(mp.log(t))
    if abs(mp.log(t))<band:assert abs(mp.log(newt))<band
    budget=cc['circle'] if r['kind']=='circle' else cc['fallback_after_trial']
    assert all(r['cost'][k]<=v for k,v in budget.items()),r
    assert r['cost']['comparisons']==0 and r['cost']['identity_checks']==cc['m']
    assert steps<100
   records.append({'p':p,'X':Xstr,'logt0':ell,'steps':steps,**count})
exceptions=[]
for p,t,reason in [(3,'7.75','readout chart singular'),(5,'16','readout chart singular'),
                   (3,'1e-30','no transverse crossing'),(3,'1e30','no transverse crossing')]:
 d=BranchEntryDiagram(p,2,mp.root(mp.mpf(t)/2,p));r=d.step()
 assert r['kind']=='AD' and r['reason']==reason
 exceptions.append({'p':p,'t':t,'reason':reason})
for p in [3,4,7,32,1000000]:
 d=BranchEntryDiagram(p,2,mp.exp((mp.mpf('.1')-mp.log(2))/p));r=d.step(force_reject=True)
 assert all(r['cost'][k]==v for k,v in branch_costs(p)['fallback_after_trial'].items())
 d=BranchEntryDiagram(p,1,1);assert d.step()['kind']=='exact'
# Same state, target, precision convention and per-step counts for all methods.
mp.mp.dps=250
p=3;X=mp.mpf(2);a=mp.root(1/X,p);targets=[6,12,30,60]
A=(p-1)*(2*p-1);B=8*p*p-2;C=(p+1)*(2*p+1)
factors={
 'Pencil Halley':(lambda t:(p+1+(p-1)*t)/(p-1+(p+1)*t),9,0),
 'Pencil rational Pade':(lambda t:(A*t*t+B*t+C)/(C*t*t+B*t+A),13,0),
 'Circle, linear power':(lambda t:circle.phi(p,t),8,0),
 'Circle, branch entry':(lambda t:circle.phi(p,t),18,12),
 'Circle, residual gate':(lambda t:circle.phi(p,t),28,12)}
table={}
for name,(fn,cost,initial) in factors.items():
 s=mp.mpf('.75');j=0;rows=[]
 for digits in targets:
  while abs(s/a-1)>mp.mpf(10)**(-digits):s*=fn(X*s**p);j+=1
  rows.append({'digits':digits,'steps':j,'mobile_joins':j*cost,'with_cache':j*cost+initial})
 table[name]={'initial_cache_joins':initial,'targets':rows}
# Verify the optimized row by actual intersections, not only multiplying a formula.
d=BranchEntryDiagram(3,2,mp.mpf('.75'));j=0
for row in table['Circle, branch entry']['targets']:
 while abs(d.s/a-1)>mp.mpf(10)**(-row['digits']):
  assert d.step()['kind']=='circle';j+=1
 assert j==row['steps'] and d.count['J']==row['with_cache']
result={'scope':'Finite high-precision checks; whole-branch contraction is separately proved in Lean.',
 'trajectory_digits':180,'trajectories':records,'count':len(records),'max_steps':max(x['steps'] for x in records),
 'max_relative_readout_disagreement':mp.nstr(maximum,8),'exceptional_cases':exceptions,'accuracy_work':table,
 'costs':{str(p):branch_costs(p) for p in [3,4,32,1000000]}}
HERE=Path(__file__).resolve().parent
(HERE/'protocol_checks.json').write_text(json.dumps(result,indent=2)+'\n')
latex=[]
for name,v in table.items():
 label=name.replace('Pade',r"Pad\'e")
 latex.append(label+' & '+' & '.join(str(x['steps'])+' / '+str(x['mobile_joins']) for x in v['targets'])+r'\\')
tabletex=r'''\begin{tabularx}{\linewidth}{@{}Xcccc@{}}\toprule
Protocol & $d=6$ & $d=12$ & $d=30$ & $d=60$\\\midrule
'''+ '\n'.join(latex)+'\n'+r'\bottomrule\end{tabularx}'+'\n'
(HERE.parents[1]/'accuracy_table.tex').write_text(tabletex)
print(f'PASS: {len(records)} branch-entry geometric trajectories; max {result["max_steps"]} steps; costs, exceptions and accuracy table')
