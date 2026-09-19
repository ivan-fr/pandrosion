"""Summarize retained held-out and fault-injection results."""
from pathlib import Path
import json
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
ROOT=Path(__file__).parent
load=lambda p:json.loads((ROOT/p).read_text())
v=load('revised_validation.json');a=load('revised_ablation.json');c=load('noisy_controller_results.json')
summary=v['summary']
lines=['# Revised circuit: measured simulation results','',
 'See [design and assumptions](PRECISION_REVISION.md). No physical chip measurements are claimed.','',
 f"Held-out inputs: {summary['pairs']}. Below 1 ppm: {summary['meets_1ppm']}. Improved over paired original: {summary['improved']}.",
 f"Worst original error: {summary['worst_before']*1e6:.4f} ppm. Worst revised error: {summary['worst_after']*1e6:.4f} ppm.",'',
 '| p | X | °C | Original error ppm | Revised error ppm |','|---:|---:|---:|---:|---:|']
for r in v['runs']:
 lines.append(f"| {r['p']} | {r['X']:.8g} | {r['temperature_C']} | {r['before']['configured_adc_relative_error']*1e6:.6g} | {r['after']['configured_adc_relative_error']*1e6:.6g} |")
lines+=['', '## Diagnostic ablation at p=3, X=0.037, 85 °C','', '| Variant | Error ppm |','|:---|---:|']
for r in a['runs']:lines.append(f"| {r['variant']} | {r['configured_adc_relative_error']*1e6:.6g} |")
lines+=['',f"Controller subsystem: {len(c['runs'])} normal completions; {len(c['faults'])} injected faults rejected with no transfer. This controller is not integrated into the revised SPICE circuit.",
 '', 'Revised readout: 23.985 ms, plus preparation/programming/calibration; original readout: 2.905 ms.','',
 '![Precision revision](precision_revision.svg)']
(ROOT/'PRECISION_REVISION_RESULTS.md').write_text('\n'.join(lines)+'\n')
fig,axes=plt.subplots(1,2,figsize=(11,4.5),layout='constrained')
x=[r['before']['configured_adc_relative_error']*1e6 for r in v['runs']]
y=[r['after']['configured_adc_relative_error']*1e6 for r in v['runs']]
axes[0].loglog(x,y,'o',color='#167897',ms=4);axes[0].axhline(1,color='#c2682b',ls='--',label='1 ppm')
axes[0].set(xlabel='Original error (ppm)',ylabel='Revised error (ppm)',title='64 held-out paired circuit tests');axes[0].legend()
labels=['Complete revision','One conversion','No ADC calibration','No cell calibration','No leakage compensation']
axes[1].barh(labels,[r['configured_adc_relative_error']*1e6 for r in a['runs']],color='#167897');axes[1].set_xscale('log');axes[1].invert_yaxis()
axes[1].set(xlabel='Relative error (ppm)',title='Hot low-degree diagnostic · p = 3')
for ax in axes:ax.grid(alpha=.2)
fig.suptitle('Precision mode — behavioral validation, with additional hardware assumptions')
fig.savefig(ROOT/'precision_revision.png',dpi=160);fig.savefig(ROOT/'precision_revision.svg')
path=ROOT/'precision_revision.svg';path.write_text('\n'.join(line.rstrip() for line in path.read_text().splitlines())+'\n')
print('Precision revision report generated')
