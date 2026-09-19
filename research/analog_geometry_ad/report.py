"""Render the paired simulation evidence without selecting policies on validation."""
from pathlib import Path
import json
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from check_results import refinement_differences
HERE=Path(__file__).resolve().parent
NAMES={'legacy':'V30 equation baseline','direct':'Direct, two cells','feedback':'Feedback, two cells'}
COLORS={'legacy':'#65727A','direct':'#176B9B','feedback':'#BD5A20'}
def load(name):return json.loads((HERE/name).read_text())
def rr(row,v):return next(x for x in row['results'] if x['variant']==v)
def pt(row,v,n,a):return next(x for x in rr(row,v)['points'] if x['iterations']==n and x['average']==a)
def fmt(x):return 'not available' if x is None else f'{x:.3f}'

def main():
 selection=load('selection.json');val=load('validation.json');cell=load('cell_results.json');fine=load('fine_checks.json');ablation=load('ablation.json');energy=load('passive_energy.json')
 rows=val['runs'];summary=val['summary']
 baseline=next(x for x in summary if x['variant']=='legacy' and x['target_ppm']==1)
 candidate=next(x for x in summary if x['variant']=='feedback' and x['target_ppm']==1)
 parts=['# AD correction geometry: paired SPICE results','',
 'The geometric feedback cell is evaluated against both the unchanged V30 equation-level correction and a matched two-cell direct implementation. All speed claims below concern the declared behavioral model, not fabricated hardware. See [the frozen protocol](SIMULATION_PROTOCOL.md).','',
 '**Finding: a local settling improvement, but no demonstrated whole-calculator speed advantage over V30 at the 1-ppm target.** At the selected '+f'{candidate["policy"]["time_ms"]:.3f} ms policy, feedback passes {candidate["passes"]}/{candidate["cases"]} held-out inputs versus {baseline["passes"]}/{baseline["cases"]} for the V30 equation baseline. '+
 'The two finite-cell topologies both add internal noise and calibration work. The isolated feedback cell is useful evidence for an implementation option, not sufficient evidence to replace the V30 architecture or claim a superior chip.','',
 '## Whole-calculator policies selected before validation','',
 '| Variant | Target (ppm) | Selected time (ms) | Iterations / averaged | Held-out passes | Worst completed error (ppm) |',
 '|:--|--:|--:|:--|:--|--:|']
 for x in summary:
  pol=x['policy']
  parts.append(f'| {NAMES[x["variant"]]} | {x["target_ppm"]:g} | {pol["time_ms"]:.3f} | {pol["iterations"]} / {pol["average"]} | {x["passes"]}/{x["cases"]} ({x["completed"]} completed) | {x["worst_error"]*1e6:.3f} |' if pol else f'| {NAMES[x["variant"]]} | {x["target_ppm"]:g} | — | No eligible development policy | — | — |')
 rejected=sum(x['status']=='rejected' for r in selection['runs'] for x in r['results'])
 parts += ['', '**An accuracy miss invalidates the selected target claim even when ngspice completes.** A selected time with fewer passes than cases is not a validated all-case latency. The 0.1-ppm target is also allowed to fail; no post-validation reselection is performed.','',
  f'Development retained {rejected} range/guard rejections out of 120 transients, all on the aggressive or minimum acquisition schedules. Those schedules are ineligible for selection. All 192 validation transients completed without guard rejection, but the accuracy misses above remain.','',
  '## Common fixed readout policies','', '| Variant | 4 iterations / average 2 at 4.785 ms | Worst ppm | 20 iterations / average 16 at 23.985 ms | Worst ppm |','|:--|:--|--:|:--|--:|']
 common=[]
 for v in NAMES:
  rs=[r for r in rows if r['schedule']=='precision'];good=[r for r in rs if rr(r,v)['status']=='ok']
  for n,a in [(4,2),(20,16)]:
   errors=[pt(r,v,n,a)['error'] for r in good]
   common.append(dict(variant=v,iterations=n,average=a,cases=len(rs),completed=len(good),passes_1ppm=sum(e<=1e-6 for e in errors),worst_error=max(errors),median_error=float(np.median(errors))))
  x,y=common[-2:];parts.append(f'| {NAMES[v]} | {x["passes_1ppm"]}/{x["cases"]} ≤ 1 ppm | {x["worst_error"]*1e6:.3f} | {y["passes_1ppm"]}/{y["cases"]} ≤ 1 ppm | {y["worst_error"]*1e6:.3f} |')
 parts += ['', 'These fixed reference policies were inherited from V30, not chosen to make the new topology win. All three models use the same acquisition clocks, 100 nF memories, 230-ohm switches, shared calibration and input preparation. Added-cell variants include two additional colored-noise streams and cell calibration.','',
  'For the decoded root, `d log(root)/dq = −1/(p+q)`. A given centered-voltage error therefore has a smaller relative effect at large degrees. The degree-one-million cases do not replace the low-degree precision tests; preparation also already contributes to their initial accuracy.','',
  '## Isolated correction-cell result','',
  'The cell bench measures time after a new residual step, with the cells already powered and settled beforehand. Tolerances here are correction **volts**, not decoded-root ppm. Dynamic disturbance sources are off on this bench; finite loading, affine errors and noisy calibration measurements remain.','',
  '| Residual step w | Direct settling to 1 µV (µs) | Feedback settling to 1 µV (µs) | Feedback reduction | Feedback overshoot (V) |','|--:|--:|--:|--:|--:|']
 comparisons=[]
 for w in [.01,.1,.5,1,-.1]:
  group={r['variant']:r for r in cell['runs'] if r['p']==3 and r['w']==w and r['tau_scale']==1 and r['profile']=='calibrated'}
  d=group['direct']['settling_us']['1e-06'];f=group['feedback']['settling_us']['1e-06'];reduction=1-f/d
  comparisons.append(dict(w=w,direct_us=d,feedback_us=f,reduction=reduction,feedback_overshoot=group['feedback']['overshoot_V']))
  parts.append(f'| {w:g} | {d:.3f} | {f:.3f} | {100*reduction:.1f}% | {group["feedback"]["overshoot_V"]:.6g} |')
 parts += ['', 'For the cubic full positive step, the feedback cell settles sooner but overshoots its equilibrium. The static geometric coordinate bounds do not bound this transient. The small negative-residual step tests a departure from the ideal initialized interval and shows why a uniform speedup should not be claimed. Eight four-times-finer timestep checks changed the 1-µV settling measurement by at most '+f'{max(x["settling_difference_us"] for x in cell["fine"]):.4f} µs.','',
  'Calibration is essential even on the isolated cell. At `p=3, w=1`, the final absolute errors are:','',
  '| Cell profile | Direct (µV) | Feedback (µV) |','|:--|--:|--:|']
 for prof,name in [('nominal','No affine error, finite load'),('untrimmed','Affine errors, no trim'),('calibrated','Electrical trim applied')]:
  group={r['variant']:r for r in cell['runs'] if r['p']==3 and r['w']==1 and r['tau_scale']==1 and r['profile']==prof}
  parts.append(f'| {name} | {group["direct"]["static_error_V"]*1e6:.3f} | {group["feedback"]["static_error_V"]*1e6:.3f} |')
 parts += ['', 'The first two profiles do not settle within the 1-µV accuracy band during the recorded step response. A better intersection angle does not remove loading and component error.','',
  '## What consumes the available time','',
  'Each added correction pole is about 1 µs, whereas the nominal switch/memory RC is 23 µs and each precision acquisition window is 400 µs. Shortening the acquisition schedule changes memory transfer errors even if the correction settles earlier. The full-circuit study includes this coupling. Preparation, programming, electrical calibration, ADC latency and decoding remain outside the quoted readout times.','',
  '## Partial passive-load accounting','',
  '**The following is only the loss in the two explicit correction-cell port resistors. It is not chip energy or supply power.** Behavioral sources have no transistor/quiescent-current model.','',
  '| Degree | X | Topology | Final two-port dissipation (µW) | Energy through 4.785 ms (nJ) |','|--:|--:|:--|--:|--:|']
 for e in energy['runs']:
  first=next(x for x in e['points'] if x['iterations']==4)
  parts.append(f'| {e["p"]} | {e["X"]:g} | {e["variant"]} | {e["final_port_power_uW"]:.6g} | {first["port_resistor_energy_nJ"]:.3f} |')
 parts += ['', 'The feedback summer holds a signal near `b≈1` at convergence, whereas the direct numerator and correction approach zero. With the modeled 50-kilohm shunt loads, that common-mode level costs passive power. Changing the physical input impedance could change this balance. A multiplier/summer versus multiplier/divider block inventory does not establish an area or energy reduction.','',
  '## Ablations and numerical reliability','', '| Diagnostic | Variant | Full | No inner trim | Quiet inner cells | Double inner noise | 10× slower inner poles |','|:--|:--|--:|--:|--:|--:|--:|']
 for p,X in [(3,.071),(7,1e-200),(1000000,500000)]:
  group=[r for r in ablation['runs'] if r['p']==p and r['X']==X]
  for v in ['direct','feedback']:
   vals=[]
   for prof in ['full','no_inner_trim','quiet_inner','double_inner_noise','slow_inner']:
    row=next(r for r in group if r['label'].endswith('_'+prof))
    vals.append(f'{pt(row,v,20,16)["error"]*1e6:.4g}' if rr(row,v)['status']=='ok' else rr(row,v)['status'])
   parts.append(f'| p={p}, X={X:g} | {v} | '+' | '.join(vals)+' |')
 parts += ['', 'Ablation entries are decoded-root ppm at the fixed 20/16 policy. These are three diagnostic cases, not universal component error bounds. A particular seeded disturbance can partially cancel deterministic bias: a smaller error with doubled noise does not mean that noise improves precision or that its variance is lower.','',
  f'Whole-circuit timestep checks: {sum(x<.1e-6 for x in refinement_differences(val,fine))}/{len(fine)} decoded readouts agree within 0.1 ppm under a four-times-finer step (maximum difference {max(refinement_differences(val,fine))*1e6:.4f} ppm). This compares the readouts themselves, not merely their absolute reference errors. All failures and guard/clamp activations remain in the JSON records.','',
  '## Interpretation','',
  'The finite-bandwidth cell can benefit from the geometric feedback factor, but the evidence must be assessed at the complete-calculator level. A shorter isolated settling transient does not automatically reduce the memory/acquisition budget. The old V30 scalar denominator was already well conditioned after centering, so this experiment tests an implementation topology rather than a better intrinsic condition number.','',
  'No transistor process, manufacturer arithmetic macromodel or measured prototype is used. The direct divider and feedback primitives are assigned the same generic pole/load/error model. Total energy, layout area, device count and silicon speed remain uncharacterized.','',
  '## Reproduce','', '```sh',
  'python3 research/analog_geometry_ad/verify.py',
  'python3 research/analog_geometry_ad/circuit.py',
  'python3 research/analog_geometry_ad/cell_bench.py',
  'python3 research/analog_geometry_ad/campaign.py',
  'python3 research/analog_geometry_ad/passive_energy.py',
  'python3 research/analog_geometry_ad/report.py',
  'python3 research/analog_geometry_ad/check_results.py','```','',
  'Requires ngspice and the existing `research/analog_fast_ad/requirements.txt`. Increase `PANDROSION_SPICE_TIMEOUT_SECONDS` on slower hosts; it changes only host execution limits. Development selection is saved before validation. Example decks, logs and thinned waveforms are in `examples/`.']
 (HERE/'SIMULATION_RESULTS.md').write_text('\n'.join(parts)+'\n')
 metrics=dict(common_policies=common,cell_comparisons=comparisons,
  counts=dict(cell_steps=len(cell['runs']),cell_fine=len(cell['fine']),development_jobs=len(selection['runs']),validation_jobs=len(rows),
    development_transients=sum(len(r['results']) for r in selection['runs']),validation_transients=sum(len(r['results']) for r in rows),whole_fine=len(fine),ablation_transients=sum(len(r['results']) for r in ablation['runs']),energy_transients=len(energy['runs'])))
 (HERE/'summary.json').write_text(json.dumps(metrics,indent=2)+'\n')
 # Separate microsecond cell settling from millisecond full-system accuracy.
 fig,axs=plt.subplots(1,3,figsize=(14,4.5),layout='constrained')
 for v in ['direct','feedback']:
  arr=np.loadtxt(HERE/f'cell_{v}.csv',skiprows=1,delimiter=',');mask=arr[:,0]<=22e-6
  axs[0].plot(arr[mask,0]*1e6,arr[mask,1],label=NAMES[v],color=COLORS[v])
 axs[0].axhline(-.6,color='#84939D',lw=.8,ls=':');axs[0].set(xlabel='Time after residual step (µs)',ylabel='Correction delta (V)',title='Isolated calibrated cell: p=3, w: 0→1');axs[0].legend(fontsize=8);axs[0].grid(alpha=.15)
 for i,v in enumerate(NAMES):
  rs=[r for r in rows if r['schedule']=='precision' and rr(r,v)['status']=='ok'];ee=np.array([pt(r,v,4,2)['error']*1e6 for r in rs])
  offsets=np.linspace(-.12,.12,len(ee));axs[1].scatter(i+offsets,np.maximum(ee,1e-5),s=12,alpha=.65,color=COLORS[v])
 axs[1].set_xticks(range(3),['V30','Direct','Feedback']);axs[1].set(yscale='log',ylabel='Decoded-root error (ppm)',title='Same 4.785 ms readout, 64 inputs');axs[1].axhline(1,color='black',lw=1,ls='--');axs[1].grid(axis='y',alpha=.15);axs[1].text(.03,.03,'Errors below 1e-5 ppm shown at floor',transform=axs[1].transAxes,fontsize=7)
 for v in NAMES:
  rr0=[r for r in selection['frontier'] if r['variant']==v]
  tt=sorted(set(x['time_ms'] for x in rr0));errs=[min(x['worst_error'] for x in rr0 if x['time_ms']<=t)*1e6 for t in tt]
  axs[2].plot(tt,errs,marker='o',ms=3,color=COLORS[v],label=NAMES[v])
 axs[2].set(xlabel='Fixed readout time (ms)',ylabel='Worst development error (ppm)',yscale='log',title='Development envelope; validation is separate');axs[2].axhline(1,color='black',ls='--',lw=1);axs[2].grid(alpha=.15);axs[2].legend(fontsize=7)
 fig.suptitle('Centered AD feedback: cell benefit versus whole-calculator constraints',fontsize=14)
 for ext in ['png','svg']:fig.savefig(HERE/f'comparison_results.{ext}',dpi=180,bbox_inches='tight')
 svg=HERE/'comparison_results.svg'
 svg.write_text('\n'.join(line.rstrip() for line in svg.read_text().splitlines())+'\n')
 print(json.dumps(metrics,indent=2))
if __name__=='__main__':main()
