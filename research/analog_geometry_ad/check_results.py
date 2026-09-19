"""Check evidence consistency, including negative results; never assert that feedback wins."""
from pathlib import Path
import json,math
HERE=Path(__file__).resolve().parent
load=lambda name:json.loads((HERE/name).read_text())

def refinement_differences(validation, checks):
 """Compare the actual decoded readouts, not just their absolute reference errors."""
 differences=[]
 for check in checks:
  pol=check['policy'];v=pol['variant'];n=pol['iterations'];a=pol['average']
  coarse=next(r for r in validation['runs'] if r['id']==check['coarse_case_id'])
  pair=[next(x for x in r['results'] if x['variant']==v) for r in [coarse,check['run']]]
  if any(x['status']!='ok' for x in pair):
   differences.append(float('inf'));continue
  qc,qf=[sum(x['configured_adc_samples'][n-a:n])/a for x in pair]
  # root_fine/root_coarse - 1 = (q_coarse-q_fine)/(p+q_fine).
  differences.append(abs((qc-qf)/(coarse['p']+qf)))
 return differences

def main():
 selection=load('selection.json');val=load('validation.json');cells=load('cell_results.json');fine=load('fine_checks.json');abl=load('ablation.json');energy=load('passive_energy.json')
 assert len(selection['runs'])==40
 assert len(cells['runs'])==192 and len(cells['fine'])==8
 assert len(abl['runs'])==15 and len(energy['runs'])==6
 for group in [selection['runs'],val['runs'],abl['runs']]:
  assert len({r['id'] for r in group})==len(group)
  for r in group:
   assert {x['variant'] for x in r['results']}=={'legacy','direct','feedback'}
   assert r['calibration']['correction']['points']==81
   for x in r['results']:
    assert x['status'] in ['ok','failed','rejected']
    for p in x['points']:
     assert math.isfinite(p['error']) and p['error']>=0
     expected=(r['config']['update_start_us']+r['config']['update_width_us']+15+(p['iterations']-1)*r['config']['period_us'])/1000
     assert abs(expected-p['time_ms'])<1e-9
    if x['status']=='ok':assert not x['guards']
 for summary in val['summary']:
  assert summary['policy']==next(s['policy'] for s in selection['selected'] if s['variant']==summary['variant'] and s['target_ppm']==summary['target_ppm'])
  pol=summary['policy']
  if not pol:continue
  rows=[r for r in val['runs'] if r['schedule']==pol['schedule']];assert len(rows)==64
  results=[next(x for x in r['results'] if x['variant']==summary['variant']) for r in rows]
  good=[r for r in results if r['status']=='ok']
  err=[next(p['error'] for p in r['points'] if p['iterations']==pol['iterations'] and p['average']==pol['average']) for r in good]
  assert summary['completed']==len(good) and summary['passes']==sum(e<=summary['target_ppm']*1e-6 for e in err)
  assert summary['worst_error']==max(err)
 assert all(x['within_point_one_ppm'] for x in fine), 'Timestep disagreement must be investigated before a precision conclusion'
 assert len(fine)==4 and max(refinement_differences(val,fine))<.1e-6
 assert all(x['settling_difference_us']<.05 for x in cells['fine'])
 assert all(x['final_port_power_uW']>=0 and all(p['port_resistor_energy_nJ']>=0 for p in x['points']) for x in energy['runs'])
 for f in ['SIMULATION_RESULTS.md','comparison_results.png','comparison_topology.png','summary.json']:assert (HERE/f).exists()
 print('PASS: frozen selections, campaign inventories, precision misses, fine steps, and partial energy accounting')
if __name__=='__main__':main()
