"""Build broad-coverage tables and plots directly from completed campaign files."""
from pathlib import Path
import json,csv
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
ROOT=Path(__file__).parent
load=lambda name:json.loads((ROOT/name).read_text())
a=load('generalist_algorithm.json');s=load('generalist_spice.json');c=load('clock_modes_results.json');st=load('streaming_results.json')
lines=['# Generalist campaign results','',
 'Read [architecture and scope](GENERALIST.md) before interpreting the counts. Tests are simulations, not physical measurements.','',
 f"Arithmetic: {a['input_pairs']:,} pairs, {a['distinct_degrees']:,} distinct degrees, {a['evaluations']:,} evaluations. Maximum ideal relative error: {a['worst']['ideal']['relative_error']:.3g}.",
 '', '## Combined timed SPICE matrix','',
 '| Profile | Runs | Execution/range failures | At most 1 ppm | At most 1 ppb | Worst relative error | Worst p | Worst X |',
 '|:---|---:|---:|---:|---:|---:|---:|---:|']
for profile,row in s['summary'].items():
 w=row['worst'];lines.append(f"| {profile} | {row['runs']} | {row['execution_failures']} | {row['meets_1ppm']} | {row['meets_1ppb']} | {w['configured_adc_relative_error']:.4g} | {w['p']} | {w['X']:.4g} |")
lines += ['', '### Per-degree worst errors on the selected grid and random pairs','', '| p | X cases per profile | Initial profile | Tighter profile |','|---:|---:|---:|---:|']
for p in sorted(set(r['p'] for r in s['runs'])):
 rows=[r for r in s['runs'] if r['p']==p and r['status']=='completed']
 if not rows:continue
 v=[max(r['configured_adc_relative_error'] for r in rows if r['profile']==profile) for profile in ['untrimmed','trim_target']]
 lines.append(f'| {p} | {len(rows)//2} | {v[0]:.4g} | {v[1]:.4g} |')
lines += ['', '## Continuous feedback, nominal timestep only','',
 'A successful tail criterion is not a global stability proof. These runs have no imposed noise or mismatch.','',
 '| Memory time constant µs | Cases | Stable final tail within 1 µV | Range guard activated |', '|---:|---:|---:|---:|']
for tau in [2e-6,20e-6,200e-6]:
 rows=[r for r in c['continuous'] if r['memory_tau_s']==tau and r['max_step']=='0.5u' and not r.get('extended',False)]
 lines.append(f"| {tau*1e6:g} | {len(rows)} | {sum(r['stable_tail'] for r in rows)} | {sum(r['guard_activated'] for r in rows)} |")
lines += ['', 'Extended 10 ms observations at X=500,000 and memory time constant 20 µs:', '',
 '| p | Stable final tail | Maximum final-tail state error V |','|---:|:---|---:|']
for r in c['continuous']:
 if r.get('extended',False):lines.append(f"| {r['p']} | {r['stable_tail']} | {r['tail_state_error_max_V']:.4g} |")
lines += ['', '## Adaptive updates at X=500,000','',
 'Noise-free ideal memory/controller; six iterations, all-node completion threshold 0.1 µV. No detector hardware cost included.','',
 '| p | Analog model time µs | Relative error |','|---:|---:|---:|']
for r in c['adaptive']:
 if r['X']==500000:lines.append(f"| {r['p']} | {r['total_time_s']*1e6:.3f} | {r['relative_error']:.4g} |")
lines += ['',f"Streaming: {st['jobs']} jobs through 37 retained stage states, q reset and ideal reprogramming per job. Largest relative error: {st['worst_relative_error']:.4g}. Preparation and converter time are excluded.",
 '', '![Coverage and clock alternatives](generalist_results.svg)']
(ROOT/'GENERALIST_RESULTS.md').write_text('\n'.join(lines)+'\n')
fig,axs=plt.subplots(2,2,figsize=(12,8.6),layout='constrained')
for ax,profile in zip(axs[0],['untrimmed','trim_target']):
 rows=[r for r in s['runs'] if r['profile']==profile and r['status']=='completed']
 plot=ax.scatter([r['p'] for r in rows],[np.log10(r['X']) for r in rows],
  c=[np.log10(max(1e-14,r['configured_adc_relative_error'])) for r in rows],vmin=-12,vmax=-3,cmap='viridis_r',s=25)
 ax.set_xscale('log');ax.set(xlabel='Degree p',ylabel='log10(X)',title=f'Timed SPICE · {profile.replace("_"," ")}')
 fig.colorbar(plot,ax=ax,label='log10(relative root error)')
wave=np.genfromtxt(ROOT/'clock_modes_waveforms.csv',delimiter=',',names=True)
for r in c['continuous']:
 if r['p']==983039 and r['X']==500000 and r['max_step']=='0.5u' and not r.get('extended',False):
  z=wave[wave['run']==r['waveform_run']]
  axs[1,0].plot(z['time_s']*1e3,z['q'],label=f"τ = {r['memory_tau_s']*1e6:g} µs")
axs[1,0].set(xlabel='Time (ms)',ylabel='Analog state q (V)',title='Continuous loop · 37-stage case');axs[1,0].legend(fontsize=9)
axs[1,1].semilogy([r['job'] for r in st['runs']],[max(1e-18,r['relative_error']) for r in st['runs']],'.',color='#167897')
axs[1,1].axhline(1e-6,color='#c2682b',ls='--',label='1 ppm')
axs[1,1].set(xlabel='Successive input job',ylabel='Relative root error',title='Retained stage states · ideal adaptive control');axs[1,1].legend()
for ax in axs.flat:ax.grid(alpha=.15)
fig.suptitle('Broad root campaign — behavioral models, no silicon claim')
fig.savefig(ROOT/'generalist_results.png',dpi=160);fig.savefig(ROOT/'generalist_results.svg')
svg=ROOT/'generalist_results.svg'
svg.write_text('\n'.join(line.rstrip() for line in svg.read_text().splitlines())+'\n')
print('Generalist report generated from retained results')
