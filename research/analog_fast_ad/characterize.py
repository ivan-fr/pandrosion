"""Seeded behavioral tolerance study, NOT foundry/device Monte Carlo.
DC stage equations match spice.py; extra error sources are explicitly assumed.
References score outputs only and are never used by the iteration.
"""
from pathlib import Path
import json, math
import numpy as np
import mpmath as mp
from model import prepare, schedule

OUT = Path(__file__).parent
SEED = 20260919
TRIALS = 512
# Bounds for independent uniform static mismatch; noise entries are RMS Gaussian.
# 'trim_target' means proposed residual tolerances, not an implemented calibration.
PROFILES = {
 'untrimmed': dict(offset=25e-6, gain=.001, offset_tc=.5e-6, gain_tc=10e-6,
   rin=50000., leak=5e-9, charge=.5e-12, coeff_bits=16, adc_bits=18,
   adc_offset=25e-6, adc_gain=100e-6, adc_inl_lsb=1., noise=5e-6),
 'trim_target': dict(offset=1e-6, gain=20e-6, offset_tc=.02e-6, gain_tc=.2e-6,
   rin=1e7, leak=50e-12, charge=.02e-12, coeff_bits=24, adc_bits=22,
   adc_offset=1e-6, adc_gain=2e-6, adc_inl_lsb=.5, noise=.5e-6),
}
CAP = 10e-9
HOLD = 460e-6  # 390 us switch release -> next candidate sampling at 850 us
READ_DELAY = 15e-6  # observed state at 405 us
BETWEEN_READ_AND_SAMPLE = 445e-6
KB = 1.380649e-23

def quantize(x, bits):
 return np.rint(np.asarray(x)*2.**bits)/2.**bits

def batch(r, profile, temperature, trials, seed, enabled=None):
 """Fixed per-device draws across six steps; fresh noise each step.
 One-at-a-time mode turns off every source outside the named group.
 Temperature leakage doubles each 10 C above 25 C (assumption, not data).
 """
 rng = np.random.default_rng(seed)
 p = r['p']; ops = schedule(p); n = len(ops)
 on = lambda group: enabled is None or enabled == group
 def mismatch(bound, shape):
  return rng.uniform(-bound, bound, shape)
 shape = (trials,n+1)
 dt = temperature-25
 offset = mismatch(profile['offset'],shape) + dt*mismatch(profile['offset_tc'],shape)
 gain = mismatch(profile['gain'],shape) + dt*mismatch(profile['gain_tc'],shape)
 if not on('arithmetic'): offset*=0; gain*=0
 # Per-port mismatch is ±20% of assumed input resistance; ideal source Rout=10 ohms.
 load = 1/(1+10/(profile['rin']*rng.uniform(.8,1.2,shape))) if on('loading') else np.ones(shape)
 leak = mismatch(profile['leak'],trials)*2**((temperature-25)/10) if on('memory') else np.zeros(trials)
 charge = mismatch(profile['charge'],trials) if on('memory') else np.zeros(trials)
 # Include residual multiplier/summer/divider errors, omitted in the first SPICE stress.
 target_offset = mismatch(profile['offset'],trials)+dt*mismatch(profile['offset_tc'],trials)
 target_gain = mismatch(profile['gain'],trials)+dt*mismatch(profile['gain_tc'],trials)
 if not on('arithmetic'): target_offset*=0; target_gain*=0
 adc_offset = mismatch(profile['adc_offset'],trials) if on('adc') else np.zeros(trials)
 adc_gain = mismatch(profile['adc_gain'],trials) if on('adc') else np.zeros(trials)
 # Fixed ADC INL realization per device; simplified bounded code error, not a transfer curve.
 lsb = 4/2**profile['adc_bits']
 adc_inl = mismatch(profile['adc_inl_lsb']*lsb,trials) if on('adc') else np.zeros(trials)
 coeff = on('coefficients')
 Y = float(quantize(r['Y'],profile['coeff_bits'])) if coeff else r['Y']
 invp = float(quantize(1/p,profile['coeff_bits'])) if coeff else 1/p
 sigma = math.sqrt(profile['noise']**2+2*KB*(temperature+273.15)/CAP) if on('noise') else 0.
 q = np.zeros(trials); peak = np.zeros(trials); bad = np.zeros(trials,dtype=bool)
 for iteration in range(6):
  # Memory continues to leak between the reported readout and the next update.
  prehold = 340e-6 if iteration == 0 else BETWEEN_READ_AND_SAMPLE
  q = q-leak*prehold/CAP
  read = (q+offset[:,0])*load[:,0]; d = read.copy()
  for i,op in enumerate(ops):
   w = float(quantize(op['product_weight'],profile['coeff_bits'])) if coeff else op['product_weight']
   product = d*d if op['kind']=='square' else d*read
   addition = 0
   if op['kind']=='multiply':
    v = float(quantize(op['copy_weight'],profile['coeff_bits'])) if coeff else op['copy_weight']
    addition = v*(read-d)
   d = (d+addition+w*((1+gain[:,i+1])*product+offset[:,i+1])+offset[:,i+1])*load[:,i+1]
   peak = np.maximum(peak,abs(d))
  t = Y*(1+d); den = 1+t+(t-1)*invp
  bad |= (den<=.25)|(peak>=2)
  # Do not silently clamp errors away: report invalid runs.
  q = (read+2*(1+read*invp)*(1-t)/den)*(1+target_gain)+target_offset
  q += charge/CAP - leak*READ_DELAY/CAP + rng.normal(0,sigma,trials)
  peak = np.maximum(peak,abs(q)); bad |= (abs(q)>=2)|(~np.isfinite(q))
 qread = (1+adc_gain)*q+adc_offset+adc_inl
 if on('adc'): qread = np.rint(qread/lsb)*lsb
 bad |= abs(qread)>=2
 # High precision root is a scoring reference only. Compare in q to avoid cancellation.
 mp.mp.dps=90
 qstar = float(p*(mp.exp(-mp.log(mp.mpf(r['originalX']))/p)/mp.mpf(r['c'])-1))
 delta = qread-qstar
 error = abs(delta/(p+qstar+delta))
 return dict(median=float(np.median(error)),p95=float(np.quantile(error,.95)),
  p99=float(np.quantile(error,.99)),max=float(np.max(error)),invalid=int(bad.sum()),
  q_error_p99=float(np.quantile(abs(delta),.99)),stage_peak=float(peak.max()),
  meets_1ppm=int((error<=1e-6).sum()),meets_1ppb=int((error<=1e-9).sum()))

def budgets():
 # Worst-band p+q >= p-ln2. Exact E <= D/(p-ln2-D).
 rows=[]
 for p in [3,32,1000000]:
  for target in [1e-6,1e-9]:
   total = target*(p-math.log(2))/(1+target)
   share = total/4 # Four equal state-domain allocations; not independent per-component bounds.
   rows.append(dict(p=p,relative_target=target,total_q_budget_V=total,
    quarter_budget_V=share,adc_min_bits=math.ceil(math.log2(2/share)),
    leakage_max_A_for_460us=share*CAP/HOLD,
    charge_max_C=share*CAP,
    minimum_C_for_3sigma_two_kTC=18*KB*300/share**2))
 return rows

def self_checks():
 # Decode bound and independent exact arithmetic endpoint over positive band.
 for p in [3,32,1000000]:
  for qstar in [-.69,-.2,0]:
   for delta in [-1e-4,1e-4]:
    ratio=(p+qstar)/(p+qstar+delta)-1
    exact=-delta/(p+qstar+delta)
    assert abs(ratio-exact)<3e-16
    assert abs(exact)<=1e-4/(p-math.log(2)-1e-4)
 assert abs(math.sqrt(KB*300/CAP)-.6435795988065502e-6)<1e-15


def main():
 self_checks()
 inputs=[[p,X] for p in [3,32,1000000] for X in [2,500000,1e300]]
 inputs += [[983039,X] for X in [2,500000,1e300]] # maximum 37-stage schedule
 inputs += [[p,1e-300] for p in [3,32,983039,1000000]]
 cases=prepare(inputs)
 rows=[]; individual=[]
 for index,r in enumerate(cases):
  for name,profile in PROFILES.items():
   for temp in [-20,25,85]:
    result=batch(r,profile,temp,TRIALS,SEED+index)
    rows.append(dict(p=r['p'],X=r['originalX'],profile=name,temperature_C=temp,**result))
    assert result['invalid']==0 and math.isfinite(result['max'])
   if r['originalX']==500000:
    for source in ['arithmetic','loading','memory','coefficients','adc','noise']:
     individual.append(dict(p=r['p'],profile=name,source=source,
       **batch(r,profile,25,TRIALS,SEED+index,source)))
 # Verify ideal arithmetic via same implementation (no active error group).
 for r in cases:
  assert batch(r,PROFILES['untrimmed'],25,1,SEED,'ideal')['max']<1e-12
 report=dict(scope='Assumed behavioral distributions, not device yield or a silicon guarantee',
  seed=SEED,trials_per_case=TRIALS,profiles=PROFILES,
  hold_capacitance_F=CAP,hold_time_s=HOLD,noise_kTC_rms_300K_V=math.sqrt(KB*300/CAP),
  joint=rows,one_source_at_a_time=individual,budgets=budgets())
 (OUT/'characterization_results.json').write_text(json.dumps(report,indent=2)+'\n')
 lines=['# Behavioral accuracy characterization','',
  'Reproduce with `python research/analog_fast_ad/characterize.py`. Fixed seed: 20260919; '
  '512 synthetic devices per case, six iterations, temperatures −20/25/85 °C. '
  'The same static mismatch draws are retained across iterations and temperatures. '
  'These are assumed distributions, not foundry statistics or measured yields.','',
  '## Joint errors','',
  '| p | X | Profile | °C | Median relative error | 99th percentile | Largest observed | Invalid |',
  '|---:|---:|:---|---:|---:|---:|---:|---:|']
 for r in rows:
  lines.append(f"| {r['p']} | {r['X']:g} | {r['profile']} | {r['temperature_C']} | {r['median']:.3g} | {r['p99']:.3g} | {r['max']:.3g} | {r['invalid']} |")
 lines += ['', '## Isolated error sources at X=500,000 and 25 °C','',
  'Each row activates one source group only; these percentiles must not be added as an error bound.','',
  '| p | Profile | Source | 99th percentile relative error |', '|---:|:---|:---|---:|']
 for r in individual:lines.append(f"| {r['p']} | {r['profile']} | {r['source']} | {r['p99']:.3g} |")
 lines += ['', '## Conservative state-domain allocations','',
  'For ideal q★ in [−ln 2,0], an additive state error |δ|≤D gives '
  '`relative error ≤ D/(p−ln 2−D)`. Thus `D=ε(p−ln 2)/(1+ε)` suffices. '
  'Divide this D into four equal allocations: conversion, deterministic memory, '
  'arithmetic/coefficients, and noise. Figures below apply to one allocation. '
  'They are individual necessary design targets under this allocation, not a system guarantee. '
  'Leakage and charge injection share the memory allocation; thermal noise and amplifier noise share the noise allocation.','',
  '| p | Target | Total q tolerance (V) | ADC ideal bits, ±2 V | Leakage ceiling (A), 460 µs / 10 nF | Charge ceiling (C), 10 nF | C floor (F), two kT/C samples, 3σ |',
  '|---:|---:|---:|---:|---:|---:|---:|']
 for r in report['budgets']:
  lines.append(f"| {r['p']} | {r['relative_target']:.0e} | {r['total_q_budget_V']:.3g} | {r['adc_min_bits']} | {r['leakage_max_A_for_460us']:.3g} | {r['charge_max_C']:.3g} | {r['minimum_C_for_3sigma_two_kTC']:.3g} |")
 (OUT/'CHARACTERIZATION.md').write_text('\n'.join(lines)+'\n')
 print('PASS',len(rows)*TRIALS,'joint samples;',len(individual)*TRIALS,'isolated samples; ideal and bound checks')
 for r in rows:
  if r['X']==500000 and r['temperature_C']==25:print(r)
if __name__=='__main__':main()
