"""Plot tested timing policies, never an interpolated universal precision bound."""
from pathlib import Path
import json
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
ROOT=Path(__file__).parent
r=json.loads((ROOT/'speed_accuracy_results.json').read_text())
fig,ax=plt.subplots(figsize=(10,6),layout='constrained')
for name,*_ in r['schedules']:
 pts=[p for p in r['points'] if p['schedule']==name]
 if pts:ax.scatter([p['time_ms'] for p in pts],[p['worst_error']*1e6 for p in pts],s=24,alpha=.65,label=name)
front=[];best=float('inf')
for p in sorted(r['points'],key=lambda x:(x['time_ms'],x['worst_error'])):
 if p['worst_error']<best:front.append(p);best=p['worst_error']
ax.plot([p['time_ms'] for p in front],[p['worst_error']*1e6 for p in front],color='black',lw=1,label='Development frontier (8 cases)')
for s in r['summary']:
 if s.get('worst_error') is not None:ax.scatter(s['policy']['time_ms'],s['worst_error']*1e6,marker='X',s=110,color='crimson',zorder=5)
for ppm in [1,10,100]:ax.axhline(ppm,color='grey',ls=':',lw=.8)
ax.set(xscale='log',yscale='log',xlabel='Analog schedule to readout (ms; excludes calibration and conversion latency)',ylabel='Largest observed relative root error (ppm)',title='Precision–time tradeoff: fixed hardware, behavioral SPICE')
ax.legend(fontsize=9);ax.grid(alpha=.15)
fig.savefig(ROOT/'speed_accuracy.png',dpi=170);fig.savefig(ROOT/'speed_accuracy.svg')
p=ROOT/'speed_accuracy.svg';p.write_text('\n'.join(x.rstrip() for x in p.read_text().splitlines())+'\n')
lines=['# Precision–time study','',
 'This study changes the schedule and readout policy, retaining the calibrated precision circuit: 100 nF memories, 230 ohm switches, 24-bit coefficients/ADC and the same noise assumptions. It does not accelerate analog components or shrink their modeled time constants.',
 '', '## Protocol','',
 'Five schedules are explored on eight development inputs (p=3,7,983039,1000000; X=2 or 500000). Each schedule runs twenty iterations. Fixed policies read prefixes of 2,3,4,6,8,12 or 20 iterations and average 1,2,4,8 or 16 states where allowed. This prefix scoring avoids rerunning identical trajectories; it is not an oracle-controlled stopping rule. Different prefixes are correlated, not independent trials.',
 '', 'The fastest development policy meeting each target is frozen before testing eighteen new inputs (six degrees, X=0.037,1e-200,1e200), with three temperatures and new noise/calibration seeds. Failed simulations and held-out accuracy misses remain in the JSON. Each selected policy is checked with a four-times-finer timestep on its worst completed validation case.',
 '', '| Target | Selected schedule | Iterations / averaged | Time (ms) | Held-out passes | Worst held-out error (ppm) |',
 '|---:|:---|---:|---:|---:|---:|']
for s in r['summary']:
 p=s['policy']
 if p:lines.append(f"| {s['target_ppm']} ppm | {p['schedule']} | {p['iterations']} / {p['average']} | {p['time_ms']:.3f} | {s['passes']}/{s['cases']} | {s['worst_error']*1e6:.5g} |")
 else:lines.append(f"| {s['target_ppm']} ppm | No qualifying policy | — | — | — | — |")
lines+=['','Crimson crosses are held-out maxima; the black line connects development policies for readability, not an interpolated guarantee.','', '![Precision–time curve](speed_accuracy.svg)','',
 '## Failures and numerical checks','',
 f"Development: {sum(x['status']=='ok' for x in r['training'])}/{len(r['training'])} trajectories completed without a range/denominator rejection. Validation: {sum(x['status']=='ok' for x in r['validation'])}/{len(r['validation'])}. Finer-timestep checks: {len(r['fine'])}, each with a relative-error change below 0.1 ppm.",
 '', '## What is timed, and what preconditioning means','',
 'The analog time is the configured time from the prepared job/reset to the last required state sample. It is not ngspice execution time and does not include supply startup, electrical calibration, input preparation, coefficient programming, ADC conversion latency or final digital decoding. Therefore these numbers remain lower estimates of end-to-end physical latency. The ADC is a sampled transfer model, not a timed converter.',
 '', 'Powering the circuit beforehand eliminates power-up delay, but does not eliminate voltage changes after a new input. The hold and arithmetic states must settle to new values. Keeping the previous answer can help nearby inputs but may hurt large jumps; this study starts each job with its prescribed q=0 preparation and does not claim a warm-state streaming measurement. The older ideal streaming study retains stage states but omits the revised circuit errors.',
 '', 'The repository CPU benchmark is warmed up and uses varying inputs. Its approximately 13 ns per exp(log(X)/p) call is an amortized host-loop time, not an isolated dependent latency measurement or a universal processor specification. It is not directly equivalent to the analog schedule. No speed or energy advantage is established.',
 '', '## Scope and interpretation','',
 'The reference root is used only for scoring. Electrical calibration uses known reference voltages and is repeated for each temperature/schedule. No calibration or coefficient programming time is charged. High degrees benefit from digital preparation and from root-error sensitivity proportional to roughly 1/p; accuracy at p=1000000 alone would be a weak test. The low-degree cases are essential.',
 '', 'The plotted frontier is finite-sample evidence, not an optimum over all analog circuits or an all-input accuracy bound. Large memory, leakage compensation, precision references and idealized arithmetic transfer laws retain the limitations documented in PRECISION_REVISION.md. There is no transistor/PDK validation or measured chip.',
 '', 'Reproduce with `python research/analog_fast_ad/speed_accuracy.py` then `python research/analog_fast_ad/speed_accuracy_report.py`.']
# Rescore archived trajectories, clearly separated from new validation.
import mpmath as mp
import numpy as np
from model import prepare, decode
old=json.loads((ROOT/'revised_validation.json').read_text())['runs']
cases=prepare([[v['p'],v['X']] for v in old]);mp.mp.dps=80
retro=[]
for n,a,target in [(2,1,10),(4,2,1)]:
 rows=[]
 for v,c in zip(old,cases):
  q=float(np.mean(v['after']['configured_adc_samples'][n-a:n]))
  ref=mp.exp(mp.log(mp.mpf(c['originalX']))/c['p'])
  rows.append(dict(p=c['p'],X=c['originalX'],error=float(abs(mp.mpf(decode(c['c'],q,c['p']))/ref-1))))
 retro.append(dict(iterations=n,average=a,target_ppm=target,cases=len(rows),passes=sum(v['error']<=target*1e-6 for v in rows),worst_error=max(v['error'] for v in rows),rows=rows))
(ROOT/'speed_accuracy_retrospective.json').write_text(json.dumps(dict(scope='Retrospective prefix scoring of the earlier 64-case campaign, not new held-out tests or additional SPICE runs.',results=retro),indent=2)+'\n')
lines+=['','## Retrospective robustness check','', 'The selected early-readout policies were also scored on the existing 64 precision-mode trajectories. These are reused historical data, not another independent validation campaign.']
for v in retro:
 lines.append(f"- {v['iterations']} iterations, {v['average']} averaged: {v['passes']}/{v['cases']} below {v['target_ppm']} ppm; largest error {v['worst_error']*1e6:.5g} ppm.")
lines+=['', 'The four-iteration policy has little margin to 1 ppm on the historical set. The longer precision mode remains available; early readout is not a replacement accuracy guarantee.']
(ROOT/'SPEED_ACCURACY.md').write_text('\n'.join(lines)+'\n')
print('Speed/accuracy report generated')
