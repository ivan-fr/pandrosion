"""Report only values from completed runs; make failed design goals explicit."""
from pathlib import Path
import json
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
ROOT=Path(__file__).parent
joint=json.loads((ROOT/'joint_spice_results.json').read_text())['runs']
cal=json.loads((ROOT/'calibration_results.json').read_text())['runs']
bench=json.loads((ROOT/'benchmark_results.json').read_text())
lines=['# Engineering follow-up results','',
 'Behavioral simulations and host benchmarks only. See [assumptions and limits](ENGINEERING_REVIEW.md).',
 '', '## Joint transient errors','',
 'These are signed scenarios, not percentiles or exhaustive corner bounds. Targets: one ppm at p≤32, one ppb at larger p.','',
 '| p | Profile | Temperature °C | Clock scale | Maximum timestep parameter | Relative error after configured ADC | Target met |',
 '|---:|:---|---:|---:|:---|---:|:---|']
for r in joint:
 lines.append(f"| {r['p']} | {r['profile']} | {r['temperature_C']} | {r['config']['timing_scale']:g} | {r['max_step']} | {r['configured_adc_relative_error']:.6g} | {'yes' if r['meets_accuracy_target'] else '**no**'} |")
lines += ['', '## Simulated measured-cell calibration','',
 'Reference voltages are ideal; measurement noise and 24-bit coefficient rounding are included. Additional trim paths are behavioral.','',
 '| p | Before, 25 °C | After, 25 °C | Room-temperature trims at 85 °C | Recalibrated at 85 °C |',
 '|---:|---:|---:|---:|---:|']
for r in cal:
 vals=[r[k]['configured_adc_relative_error'] for k in ['uncalibrated','calibrated_25C','calibrated_85C','recalibrated_85C']]
 lines.append('| '+str(r['p'])+' | '+' | '.join(f'{v:.6g}' for v in vals)+' |')
lines += ['', '## Digital comparison at X=500,000','',
 f"Host: {bench['cpu']}, {bench['platform']}/{bench['arch']}, Node {bench['node']}. Median batched time per operation; not portable single-call latency.",'',
 '| p | Preparation µs | Six digital steps only µs | Full centered digital µs | Library exp/log µs | Analog schedule µs, excludes preparation/converters |',
 '|---:|---:|---:|---:|---:|---:|']
for r in bench['rows']:
 if r['X']!=500000:continue
 vals=[r[k]['median_us'] for k in ['preparation','centered_six_steps_only','full_centered_digital','standard_library']]
 lines.append('| '+str(r['p'])+' | '+' | '.join(f'{v:.5g}' for v in vals)+f" | {r['analog_core_nominal_us']} |")
lines += ['', 'All 24 representative digital outputs were independently scored below 2e-13 relative error. No analog speed or energy advantage is established. Energy is unmeasured.', '',
 '![Engineering follow-up](engineering_results.svg)', '',
 '19 combined timed runs, eight calibrated/uncalibrated timed runs and four DC calibration benches completed. A fine-timestep repeat is included among the 19 runs. The earlier baseline circuit was also checked for regressions at three degrees.']
(ROOT/'ENGINEERING_RESULTS.md').write_text('\n'.join(lines)+'\n')
fig,axes=plt.subplots(1,2,figsize=(11,4.5),layout='constrained')
r=next(x for x in cal if x['p']==1000000)
labels=['Before · 25 °C','Calibrated · 25 °C','Same trims · 85 °C','Recalibrated · 85 °C']
keys=['uncalibrated','calibrated_25C','calibrated_85C','recalibrated_85C']
axes[0].barh(labels,[r[k]['configured_adc_relative_error'] for k in keys],color=['#c2682b','#167897','#c2682b','#167897'])
axes[0].set_xscale('log');axes[0].invert_yaxis();axes[0].set(xlabel='Relative error after ADC',title='Calibration experiment · p = 1,000,000')
b=next(x for x in bench['rows'] if x['p']==1000000 and x['X']==500000)
axes[1].barh(['Library exp/log','Full centered digital','Analog core schedule'],[b['standard_library']['median_us'],b['full_centered_digital']['median_us'],b['analog_core_nominal_us']],color=['#167897','#167897','#c2682b'])
axes[1].set_xscale('log');axes[1].invert_yaxis();axes[1].set(xlabel='µs (host batch averages vs imposed circuit schedule)',title='No speed benefit at the present clock')
for ax in axes:ax.grid(axis='x',alpha=.2)
fig.suptitle('Simulation follow-up · X = 500,000 · no physical measurements')
fig.savefig(ROOT/'engineering_results.svg');fig.savefig(ROOT/'engineering_results.png',dpi=160)
