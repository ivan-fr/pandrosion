"""Check frozen article figures against retained research records; no SPICE rerun."""
from pathlib import Path
import json
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1];DATA=ROOT/'research/analog_fast_ad'
read=lambda name:json.loads((DATA/name).read_text())
a=read('generalist_algorithm.json')
assert (a['input_pairs'],a['distinct_degrees'],a['evaluations'])==(8243,4278,24729)
v=read('revised_validation.json')['summary']
assert v['pairs']==v['meets_1ppm']==v['improved']==64
assert round(v['worst_after']*1e6,3)==.279
assert round(v['worst_before']*1e6,1)==403.5
s=read('speed_accuracy_results.json')
assert len(s['training'])==40 and len(s['validation'])==18 and len(s['fine'])==2
for result in s['summary']:
 assert result['passes']==result['cases']==18
 assert result['policy']['time_ms']==(4.785 if result['target_ppm']==1 else 2.385)
 expected=.652 if result['target_ppm']==1 else 1.238
 assert round(result['worst_error']*1e6,3)==expected
r=read('speed_accuracy_retrospective.json')['results']
assert all(x['passes']==x['cases']==64 for x in r)
assert round(r[1]['worst_error']*1e6,3)==.982
c=read('noisy_controller_results.json')
assert len(c['runs'])==18 and all(x['status']=='completed' for x in c['runs'])
assert len(c['faults'])==4 and all(x['status']=='timeout' and not x['events'] for x in c['faults'])
for name in ['precision_revision.png','speed_accuracy.png']:
 assert (HERE/'figures'/name).read_bytes()==(DATA/name).read_bytes(),name
text=(HERE/'main.tex').read_text()
for value in ['8,243','4,278','24,729','0.279','23.985','4.785','0.653','0.982','2.385','1.239']:
 assert value in text,('Missing article value',value)
print('PASS: V30 counts, errors, timings, controller outcomes and figure provenance')

g=json.loads((HERE/'fast_geometry_checks.json').read_text())
assert g['exponents']==[1,2,3,6,12,13]
assert abs(g['s_next']-g['expected'])<1e-12
assert (HERE/'figures/fast_geometry.pdf').exists()
print('PASS: geometric fast-power figure records')
