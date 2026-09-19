"""Plots measured model outputs; no fitted/extrapolated precision claims."""
import json
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
root=Path(__file__).parent
data=json.loads((root/'characterization_results.json').read_text())
fig,axes=plt.subplots(1,2,figsize=(11,4.4),layout='constrained')
colors={'untrimmed':'#c2682b','trim_target':'#167897'}
for profile,color in colors.items():
 for temp,style in [(25,'-'),(85,'--')]:
  rows=[x for x in data['joint'] if x['profile']==profile and x['X']==500000 and x['temperature_C']==temp]
  rows.sort(key=lambda row:row['p'])
  axes[0].loglog([x['p'] for x in rows],[x['p99'] for x in rows],style+'o',color=color,label=f'{profile.replace("_"," ")} · {temp} °C')
axes[0].axhline(1e-6,color='#888',lw=.8);axes[0].axhline(1e-9,color='#888',lw=.8)
axes[0].set(xlabel='Degree p',ylabel='99th percentile relative root error',title='Assumed tolerances · 512 draws per point')
axes[0].legend(fontsize=8);axes[0].grid(alpha=.18,which='both')
rows=json.loads((root/'characterization_spice.json').read_text())
a=[x for x in rows if x['p']==1000000 and x['scenario']!='charge_0p5pC_fine_step']
labels=['Baseline','25 µV offsets','0.1% product gain','50 kΩ loading','5 nA leakage','0.5 pC injection','Correction gain + offset','30 µs stage settling','30 µs + 30× slower clock']
axes[1].barh(labels,[x['decoded_relative_error'] for x in a],color='#167897')
axes[1].set_xscale('log');axes[1].invert_yaxis()
axes[1].set(xlabel='Relative root error (before ADC)',title='ngspice · p = 1,000,000 · X = 500,000')
axes[1].grid(alpha=.18,axis='x')
fig.suptitle('Behavioral accuracy — not measured silicon',fontsize=13)
fig.savefig(root/'accuracy.png',dpi=170);fig.savefig(root/'accuracy.svg')
