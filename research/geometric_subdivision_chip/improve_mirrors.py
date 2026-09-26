import sys,json
sys.path.insert(0,'research/geometric_subdivision_chip')
from improve import *
g=mod.mirror_gains(I0=1e-5,level=1.,temp=25,ikf=.05);print('gains',g,flush=True)
fb=1.
for j in range(3):
 r=sim(f'mirror_gmcal{j}',kind='mean',A=1,B=1,mirror_gains=g,mean_feedback=fb,compensation=1e-11);fb*=r['final']**2
print('feedback',fb,flush=True)
rows=[]
for p,X in [(3.7,2),(1e6,500000),(3,2),(37.5,500000)]:
 r=sim(f'mirror_root{p}',kind='root',p=p,X=X,n=6,mirror_gains=g,mean_feedback=fb,compensation=1e-11);r['relative_error']=abs(r['final']/X**(1/p)-1);rows.append(r)
print([(r['p'],r['relative_error']) for r in rows]);(P/'mirror-pilot.json').write_text(json.dumps(dict(gains=g,feedback=fb,rows=rows),indent=2))
