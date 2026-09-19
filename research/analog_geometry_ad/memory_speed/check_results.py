"""Audit recorded evidence without requiring that a proposed circuit wins."""
from pathlib import Path
import json,math
import numpy as np
import memory_campaign as c
HERE=Path(__file__).resolve().parent
load=lambda n:json.loads((HERE/n).read_text())

def main():
 dev=load('selection.json');first=load('validation.json');sec=load('secondary.json');last=load('refinement.json');frozen=load('refinement_selection.json');sens=load('sensitivity.json');feedback=load('feedback_sensitivity.json')
 assert len(dev['runs'])==114 and len(first['runs'])==144 and len(sec['runs'])==96 and len(sens['runs'])==18
 assert len(last['runs'])==64*sum(x['policy'] is not None for x in frozen)
 assert len(feedback['runs'])==18
 for dataset in [dev,first,sec,last,sens,feedback]:
  assert len({r['id']for r in dataset['runs']})==len(dataset['runs'])
  for row in dataset['runs']:
   result=row['result'];assert result['status'] in ['ok','failed','rejected']
   if result['status']=='failed':continue
   cfg=row['config'];assert row['profile']['memory_cap']==cfg['memory_cap']
   assert row['timing']['period']==cfg['period_us']
   for p in result['points']:
    assert math.isfinite(p['error']) and p['error']>=0
    time=(cfg['update_start_us']+cfg['update_width_us']+15+(p['iterations']-1)*cfg['period_us'])/1000
    assert abs(time-p['time_ms'])<1e-10
   if not row.get('archive'):
    expected=math.sqrt(2*1.380649e-23*(row['temp']+273.15)/(cfg['memory_cap']+cfg['parasitic']))
    assert abs(expected-cfg['sample_noise_rms'])<1e-16
    assert max(result['driver_peak_A'])<=cfg['driver_limit_A']*(1+1e-10)
   if result['status']=='ok':assert not result['guards']
 # Recompute the second-stage selection from first-stage data only.
 for sel in frozen:
  training=[r for r in first['runs']+sec['runs'] if r['arm']==sel['arm']]
  assert len(training)==48 and sel['training_cases']==48
  if not sel['policy']:continue
  eligible=[]
  for p in training[0]['result']['points']:
   worst=max(c.point(r,p)['error']for r in training)
   if worst<=.7e-6:eligible.append(dict(iterations=p['iterations'],average=p['average'],time_ms=p['time_ms'],worst_error=worst))
  assert sel['policy']==min(eligible,key=lambda p:(p['time_ms'],p['worst_error']))
  summary=next(s for s in last['summary']if s['arm']==sel['arm']);assert summary['policy']==sel['policy']
  rows=[r for r in last['runs']if r['arm']==sel['arm']];assert len(rows)==64
  good=[r for r in rows if r['result']['status']=='ok'];errors=[c.point(r,sel['policy'])['error']for r in good]
  assert summary['completed']==len(good) and summary['passes']==sum(e<=1e-6 for e in errors)
  assert summary['worst_error']==max(errors)
 old_pairs={(r['case']['p'],r['case']['originalX'])for r in first['runs']}
 new_pairs={(r['case']['p'],r['case']['originalX'])for r in last['runs']}
 assert len(new_pairs)==32 and not old_pairs.intersection(new_pairs)
 assert not {r['seed']for r in first['runs']}.intersection(r['seed']for r in last['runs'])
 for data,checks in [(first,load('fine_checks.json')),(sec,sec['fine']),(last,last['fine'])]:
  for check in checks:
   assert check['within_point_one_ppm'] and check['relative_readout_difference']<.1e-6
   coarse=next(r for r in data['runs']if r['id']==check['coarse_id']);fine=check['run']
   assert fine['result']['status']=='ok'
   summary=next(s for s in data['summary']if s['arm']==check['arm']);n=summary['policy']['iterations'];a=summary['policy']['average']
   qc,qf=[float(np.mean(r['result']['configured_adc_samples'][n-a:n]))for r in [coarse,fine]]
   assert abs((qc-qf)/(coarse['case']['p']+qf))==check['relative_readout_difference']
 for f in ['RESULTS.md','memory_model.png','memory_results.png','summary.json']:assert (HERE/f).is_file()
 print('PASS: memory noise/current assumptions, archived metadata, frozen policies, disjoint final cases, accuracy misses and timestep checks')

if __name__=='__main__':main()
