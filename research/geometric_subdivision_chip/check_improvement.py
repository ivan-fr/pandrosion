"""Audit reference identities, trim provenance and transistor replay."""
from improve import *
d=json.loads((P/'results.json').read_text());assert len(d['jobs'])==28
h=[j for j in d['jobs'] if j['split']=='heldout'];assert len(h)==24
assert all('reference' not in x for j in d['jobs'] for x in j['calibration'])
for j in d['jobs']:
 assert len(j['calibration'])==3
 for r in j['calibration']:
  assert (r['weight_override']==0 if j['p']>=64 else r['readout_reference']==1)
 gain=1.
 for r in j['calibration']:gain*=r['scale']/r['final']
 assert abs(gain-j['output_gain'])<1e-14
j=d['jobs'][1];lines,sense,meta=build(kind='root',p=j['p'],X=j['X'],output_gain=j['output_gain'],**d['config'])
assert not any(l.startswith(('B','F','E','G','H')) for l in lines)
assert any(l.startswith('Ccomp_') for l in lines)
r=execute(lines,sense,meta,P/'replay')
assert abs(r['final']-j['r2']['final'])<1e-8
result=dict(heldout_improved=sum(j['r2']['window_error']<j['old']['window_error'] for j in h),heldout_total=len(h),regressions=[dict(p=j['p'],X=j['X']) for j in h if j['r2']['window_error']>=j['old']['window_error']],root_oracle_free_core=True,reference_calibration_only=True,replay_absolute_difference=abs(r['final']-j['r2']['final']))
(P/'checks.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
