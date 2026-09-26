import sys,json
sys.path.insert(0,'research/geometric_subdivision_chip')
from improve import *
f=json.loads((P/'mirror-pilot.json').read_text());cfg=dict(mirror_gains=f['gains'],mean_feedback=f['feedback'],compensation=1e-11,n=6)
rows=[]
for p,X in [(3.7,2),(1e6,500000),(3,2),(37.5,500000)]:
 gain=1.
 for j in range(2):
  r=sim(f'readout_{p}_{j}',kind='root',p=p,X=X,**cfg,readout_reference=1.,output_gain=gain);gain*=r['scale']/r['final']
 r=sim(f'calibrated_{p}',kind='root',p=p,X=X,**cfg,output_gain=gain);r['relative_error']=abs(r['final']/X**(1/p)-1);rows.append(r)
print([(r['p'],r['relative_error']) for r in rows]);(P/'readout-pilot.json').write_text(json.dumps(rows,indent=2))
