"""Partial energy accounting: the TWO explicit correction port resistors only.
Behavioral source supply power, quiescent current, shared circuitry and trim area
are undefined by this model. These numbers are not total chip energy.
"""
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor
import json
import numpy as np
from circuit import execute,deck
HERE=Path(__file__).resolve().parent

def worker(job):
 row,variant=job;cfg=row['config'];data,_,_=execute(deck(row['case'],cfg,variant))
 power=(data[:,8]**2+data[:,9]**2)/cfg['rin']
 intervals=np.diff(data[:,0]);cumulative=np.r_[0,np.cumsum(intervals*(power[:-1]+power[1:])/2)]
 points=[]
 for n in [4,20]:
  t=(cfg['update_start_us']+cfg['update_width_us']+15+(n-1)*cfg['period_us'])*1e-6
  points.append(dict(iterations=n,time_ms=t*1000,port_resistor_energy_nJ=float(np.interp(t,data[:,0],cumulative)*1e9)))
 end=data[-1,0];window=100e-6
 final_power=(cumulative[-1]-np.interp(end-window,data[:,0],cumulative))/window
 return dict(p=row['p'],X=row['X'],variant=variant,
  final_port_power_uW=float(final_power*1e6),points=points)

def main():
 rows=json.loads((HERE/'ablation.json').read_text())['runs'];chosen=[r for r in rows if r['label'].endswith('_full')]
 with ProcessPoolExecutor(max_workers=3) as pool:runs=list(pool.map(worker,[(r,v) for r in chosen for v in ['direct','feedback']]))
 report=dict(scope='Only two modeled 50-kilohm correction-cell port resistors. Not circuit supply energy, chip power, area or system efficiency.',runs=runs)
 (HERE/'passive_energy.json').write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps(report,indent=2))
if __name__=='__main__':main()
