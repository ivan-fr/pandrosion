from pathlib import Path
import json
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
OUT=Path(__file__).parent
r=next(x for x in json.loads((OUT/'model_results.json').read_text())['cases'] if x['p']==1000000 and x['originalX']==500000)
fig,ax=plt.subplots(1,2,figsize=(10,4))
for tag,label in [('ideal','Functional baseline'),('stress','Imposed loading / offsets / leakage')]:
 a=np.loadtxt(OUT/f'p1000000_{tag}.csv',delimiter=',',skiprows=1)
 ax[0].plot(a[:,0]*1000,a[:,1],label=label)
 tail=a[:,0]>2.9e-3;ax[1].plot((a[tail,0]-2.9e-3)*1e6,(a[tail,1]-a[tail,1][0])*1e6,label=label)
ax[0].set(xlabel='Time (ms)',ylabel='Centered state q (V)',title='p = 1,000,000; X = 500,000')
ax[1].set(xlabel='Time after 2.9 ms (µs)',ylabel='State change (µV)',title='Final hold: leakage remains visible')
ax[0].legend(fontsize=8);fig.tight_layout()
fig.savefig(OUT/'transients.png',dpi=150);fig.savefig(OUT/'transients.svg')
p=OUT/'transients.svg';p.write_text('\n'.join(x.rstrip() for x in p.read_text().splitlines())+'\n')
