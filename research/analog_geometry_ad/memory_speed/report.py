"""Report both failed first-stage policies and the separate final validation."""
from pathlib import Path
import json,math
from collections import Counter
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import memory_campaign as c
import memory_model as m
HERE=Path(__file__).resolve().parent
load=lambda name:json.loads((HERE/name).read_text())
NAMES={'archive':'Archived V30','loaded_control':'100 nF, finite drivers','optimized':'33 nF, V30 correction','feedback':'33 nF, geometric feedback','optimized_10ppm':'10 nF / 23 Ω, 10 ppm'}
COLORS={'archive':'#697781','loaded_control':'#897497','optimized':'#176B9B','feedback':'#BD5A20'}

def main():
 sel=load('selection.json');first=load('validation.json');secondary=load('secondary.json');final=load('refinement.json');frozen=load('refinement_selection.json');sens=load('sensitivity.json');feedback_sens=load('feedback_sensitivity.json')
 feedback_policy=next(x['policy']for x in frozen if x['arm']=='feedback')
 nominal_feedback=[r for r in feedback_sens['runs']if r['label'].endswith('_nominal')]
 nominal_worst=max(c.point(r,feedback_policy)['error']for r in nominal_feedback if r['result']['status']=='ok')
 parts=['# Faster memory acquisition for centered AD','',
 'The memory redesign is tested with finite-current drivers, charge injection on both edges, electrical-reference calibration, recomputed sampling noise and the original fast-power/AD arithmetic. These are behavioral engineering hypotheses. See [the protocol](PROTOCOL.md) and [model schematic](memory_model.png).','',
 '**Finding: a faster candidate, but the 1-ppm accuracy target is not robust across all nominal tests.** The 33 nF feedback combination passes the separate 64-case final validation at 5.035 ms, versus 9.585 ms for the 100 nF control. However, an additional nominal signed-error/noise corner reaches '+f'**{nominal_worst*1e6:.4g} ppm**. '+
 'The 1.90× ratio therefore describes that final validation set; it is not an established all-nominal-case speedup at 1 ppm. No further tuning is performed to erase this failure.','',
 '## Final independent validation at 1 ppm','',
 'First-stage precision misses led to one explicit policy refinement. The first 48 cases were then used as development data: select the quickest fixed readout with worst error ≤0.7 ppm, retaining each arm’s hardware and clock. Freeze that choice before testing **32 new input pairs with two new seed/corner assignments each**. No further selection uses this final set.','',
 '| Implementation | Readout (ms) | Iterations / average | Passes ≤1 ppm | Worst error (ppm) |','|:--|--:|:--|:--|--:|']
 for r in final['summary']:
  p=r['policy']
  if not p:parts.append(f'| {NAMES[r["arm"]]} | — | No eligible policy | — | — |');continue
  parts.append(f'| {NAMES[r["arm"]]} | {p["time_ms"]:.3f} | {p["iterations"]} / {p["average"]} | {r["passes"]}/{r["cases"]} | {r["worst_error"]*1e6:.4g} |')
 control=next(r for r in final['summary']if r['arm']=='loaded_control');archive=next(r for r in final['summary']if r['arm']=='archive')
 gains=[]
 for arm in ['optimized','feedback']:
  r=next(x for x in final['summary']if x['arm']==arm)
  eligible=r['policy'] and r['passes']==r['cases'] and r['cases']==64
  validcontrol=control['policy'] and control['passes']==control['cases']==64
  ratio=control['policy']['time_ms']/r['policy']['time_ms'] if eligible and validcontrol else None
  nominal=[r for r in (sens if arm=='optimized'else feedback_sens)['runs']if r['label'].endswith('_nominal')]
  nominal_ok=all(x['result']['status']=='ok' and c.point(x,r['policy'])['error']<=1e-6 for x in nominal) if r['policy']else False
  gains.append(dict(arm=arm,all_final_cases_pass=bool(eligible),all_extra_nominal_cases_pass=nominal_ok,
   final_set_speedup_vs_loaded_control=ratio,supported_all_nominal_speedup=ratio if nominal_ok else None))
  if ratio:parts += ['',f'**{NAMES[arm]}: {ratio:.2f}× shorter readout time than the finite-driver 100 nF control**, with both passing all 64 final cases. This is the ratio of the frozen policies, not a proof of either architecture’s optimal possible latency. The remaining margin on the worst final case is only {1-r["worst_error"]*1e6:.4g} ppm. The comparison includes different fixed averaging policies, so it does not isolate an intrinsic advantage of the feedback geometry.']
  else:parts += ['',f'**{NAMES[arm]} has not established an all-case 1-ppm latency advantage** in the final validation. A selected latency is not a validated target when any case misses it.']
 parts += ['', 'The archived V30 uses the older, ideal transfer-buffer model. The 100 nF control includes the same new current limits and two-edge charge law as the 33 nF design, making it the primary comparison for the memory change. The additional finite transfer buffer has no separate device noise/offset model beyond the stated shared budgets. A manufacturer macromodel or PDK could change the result.','',
 '## First-stage misses are retained','', '| Design | Target (ppm) | Time (ms) | Passes | Worst ppm |','|:--|--:|--:|:--|--:|']
 for r in first['summary']+secondary['summary']:
  p=r['policy'];target=r.get('target_ppm',1)
  parts.append(f'| {NAMES[r["arm"]]} | {target:g} | {p["time_ms"]:.3f} | {r["passes"]}/{r["cases"]} | {r["worst_error"]*1e6:.5g} |')
 loose=next(r for r in secondary['summary']if r['arm']=='optimized_10ppm')
 parts += ['',f'The independently selected 10-ppm option uses a separate hardware profile and passes {loose["passes"]}/48 first-validation cases at {loose["policy"]["time_ms"]:.3f} ms. Its worst error is {loose["worst_error"]*1e6:.5g} ppm: the remaining margin to 10 ppm is small. This is not a 1-ppm result, a universal guarantee, or the final refined 33 nF design.','',
 '## Physical tradeoffs actually included','', '| Profile | Memory C (nF) | Ron (Ω) | Nominal Ron C (µs) | Sampling noise at 85 °C (µV RMS) | Nominal Q/C per edge (µV) |','|:--|--:|--:|--:|--:|--:|']
 for p in m.PROFILES:
  C=p['memory_cap']+p['parasitic'];noise=math.sqrt(2*1.380649e-23*358.15/C)
  parts.append(f'| {p["name"]} | {p["memory_cap"]*1e9:g} | {p["switch_ron"]:g} | {p["switch_ron"]*C*1e6:.3g} | {noise*1e6:.3g} | {p["edge_charge"]/C*1e6:.4g} |')
 parts += ['', 'The chosen 33 nF memory reduces the nominal switch/memory RC from 23 to 7.59 µs. Its sampling noise grows by about √(100/33); charge and leakage voltage errors also increase. The circuit therefore retains recalibration and averaging. Both source/sink driver currents are limited to 2 mA. At a 0.7 V step, charging a 100 nF memory alone requires at least 35 µs at that current; reducing Ron cannot remove this bound.','',
 'The 23-ohm profiles deliberately pay tenfold nominal injected charge and increased parasitic capacitance. These numerical profiles are assumptions rather than ADG1211/ADG1411 device models. [Manufacturer sample/hold guidance](https://www.analog.com/en/resources/app-notes/an-1515.html) describes the charge-injection and droop mechanisms motivating this sensitivity study.','',
 '## Component sensitivity','', 'These diagnostic trajectories use each arm’s **refined 33 nF policy**, fixed before final validation. Changed component assumptions are electrically recalibrated; they do not test drift after calibration. The feedback diagnostics also include the requested degree-one-million, X=500,000 case.','',
 '| Input / correction | Nominal | Half current | Double current | Constant charge | Double curvature | Double charge |','|:--|--:|--:|--:|--:|--:|--:|']
 for arm,dataset,prefix in [('optimized',sens,''),('feedback',feedback_sens,'feedback_')]:
  pol=next(x['policy']for x in frozen if x['arm']==arm)
  for i in range(3):
   group=[r for r in dataset['runs']if r['label'].startswith(f'{prefix}sensitivity_{i}_')];r=group[0];values=[]
   for name in ['nominal','half_current','double_current','constant_charge','double_curvature','double_charge']:
    r0=next(x for x in group if x['label']==f'{prefix}sensitivity_{i}_{name}')
    values.append(f'{c.point(r0,pol)["error"]*1e6:.4g}' if pol and r0['result']['status']=='ok'else r0['result']['status'])
   parts.append(f'| p={r["case"]["p"]}, X={r["case"]["originalX"]:g} / {arm} | '+' | '.join(values)+' |')
 parts += ['', 'Entries are decoded-root ppm, not electrical microvolts. Three diagnostics do not establish a tolerance envelope or silicon yield.','', '## Numerical checks and reproducibility','']
 checks=load('fine_checks.json')+secondary['fine']+final['fine']
 finegood=sum(x['within_point_one_ppm']for x in checks)
 parts.append(f'{finegood}/{len(checks)} worst-case readouts agree within 0.1 ppm at a four-times-finer timestep. Accuracy misses and calibration failures remain in the records. Development status counts: '+str(dict(Counter(r['result']['status']for r in sel['runs'])))+'.')
 counts=dict(development=len(sel['runs']),first_validation=len(first['runs']),control_and_10ppm=len(secondary['runs']),final_validation=len(final['runs']),sensitivity=len(sens['runs'])+len(feedback_sens['runs']),refinements=len(checks))
 completed_transients=sum('wall_seconds' in r['result']for data in [sel,first,secondary,final,sens,feedback_sens]for r in data['runs'])+sum('wall_seconds'in x['run']['result']for x in checks)
 parts += ['', f'This continuation records **{completed_transients} completed full-circuit transients out of {sum(counts.values())} trials**, excluding calibration benches and pilot runs. Six development trials were rejected at calibration before a circuit transient was attempted. Final data cover p up to one million and X from 1e-220 to 1e220; earlier stages also cover 1e±250 and the requested `(p=1,000,000, X=500,000)` diagnostic.','',
 'Root decoding attenuates centered-state error by approximately 1/p. Large-degree cases cannot substitute for small-degree precision tests. Quoted times start at reset and exclude preparation, programming, calibration, converter latency and decoding. No total supply energy, area, transistor stability or fabricated-hardware speedup is inferred from capacitor values or current limits.','',
 '```sh','python3 research/analog_geometry_ad/memory_speed/memory_model.py','python3 research/analog_geometry_ad/memory_speed/memory_campaign.py',
 'python3 -c "import sys; sys.path.insert(0,\'research/analog_geometry_ad/memory_speed\'); import supplement; supplement.freeze()"',
 'python3 research/analog_geometry_ad/memory_speed/supplement.py','python3 research/analog_geometry_ad/memory_speed/refinement.py','python3 research/analog_geometry_ad/memory_speed/feedback_stress.py',
 'python3 research/analog_geometry_ad/memory_speed/draw_memory.py','python3 research/analog_geometry_ad/memory_speed/report.py',
 'python3 research/analog_geometry_ad/memory_speed/check_results.py','```','',
 'Use ngspice and the parent study’s Python requirements. The secondary control/10-ppm choices use development data only; the refinement intentionally uses the first validation as training, then new inputs and seeds. Source hashes and versions are recorded in `provenance.json`. CI checks a small circuit smoke test and evidence consistency, not the complete optimization campaign.']
 (HERE/'RESULTS.md').write_text('\n'.join(parts)+'\n')
 c.write('summary.json',dict(trial_counts=counts,completed_transients=completed_transients,gains=gains,final=final['summary']))
 fig,axs=plt.subplots(1,3,figsize=(14,4.4),layout='constrained')
 for profile in m.PROFILES:
  rows=[r for r in sel['frontier']if r['profile']==profile['name']]
  if not rows:continue
  times=sorted(set(x['time_ms']for x in rows));errors=[min(x['worst_error']for x in rows if x['time_ms']<=t)*1e6 for t in times]
  axs[0].plot(times,errors,label=profile['name'],lw=1.2)
 axs[0].set(yscale='log',xlabel='Readout time (ms)',ylabel='Worst development error (ppm)',title='Hardware/timing sweep');axs[0].axhline(1,color='black',ls='--',lw=.8);axs[0].legend(fontsize=7);axs[0].grid(alpha=.15)
 arms=['archive','loaded_control','optimized','feedback'];labels=['V30','100 nF\ncontrol','33 nF\nV30 map','33 nF\nfeedback']
 for i,arm in enumerate(arms):
  sm=next(x for x in final['summary']if x['arm']==arm);pol=sm['policy']
  if not pol:continue
  good=[r for r in final['runs']if r['arm']==arm and r['result']['status']=='ok'];errors=[c.point(r,pol)['error']*1e6 for r in good]
  axs[1].scatter(i+np.linspace(-.15,.15,len(errors)),np.maximum(errors,1e-5),color=COLORS[arm],s=14,alpha=.7)
  axs[2].barh(3-i,pol['time_ms'],color=COLORS[arm]);axs[2].text(pol['time_ms']+.12,3-i,f'{pol["time_ms"]:.3f} ms\n{sm["passes"]}/{sm["cases"]} ≤1 ppm',va='center',fontsize=8)
 axs[1].set_xticks(range(4),labels,fontsize=8);axs[1].set(yscale='log',ylabel='Root error (ppm)',title='New final set: 64 cases per arm');axs[1].axhline(1,color='black',ls='--',lw=.8);axs[1].grid(alpha=.15);axs[1].text(.02,.02,'Display floor: 1e-5 ppm',transform=axs[1].transAxes,fontsize=7)
 axs[2].set_yticks(range(4),list(reversed(labels)),fontsize=8);axs[2].set(xlabel='Readout time (ms)',title='Frozen refined policies');axs[2].set_xlim(0,max(x['policy']['time_ms']for x in final['summary']if x['policy'])*1.35);axs[2].grid(axis='x',alpha=.15)
 axs[1].scatter([3.25],[nominal_worst*1e6],marker='D',s=38,color='#a53720',edgecolors='black',linewidths=.5)
 fig.suptitle('Memory/acquisition redesign: faster candidate, limited precision margin\n'+f'Additional nominal feedback diagnostic: {nominal_worst*1e6:.3f} ppm — exceeds the 1-ppm target',fontsize=12)
 for ext in ['png','svg']:fig.savefig(HERE/f'memory_results.{ext}',dpi=180,bbox_inches='tight')
 f=HERE/'memory_results.svg';f.write_text('\n'.join(x.rstrip()for x in f.read_text().splitlines())+'\n')
 print(json.dumps(dict(counts=counts,gains=gains),indent=2))
if __name__=='__main__':main()
