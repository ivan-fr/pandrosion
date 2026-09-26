"""Reproducible mixed-signal macro-model, not a transistor-level chip model.
No root/log/exp oracle is used in the netlist/controller. Square roots are
positive feedback equilibria of multiplier, transconductance and capacitor cells.
"""
from pathlib import Path
import argparse, json, math, random, shutil, subprocess, time
import numpy as np
import mpmath as mp
ROOT=Path(__file__).resolve().parent
mp.mp.dps=70
PROFILES={
 'ideal':dict(gain=0.,offset=0.,leak=1e15,dac_bits=None,adc_bits=None,ripple=0.),
 'trimmed':dict(gain=1e-5,offset=2e-6,leak=1e10,dac_bits=20,adc_bits=20,ripple=1e-7),
 'untrimmed':dict(gain=1e-3,offset=2e-4,leak=1e8,dac_bits=16,adc_bits=16,ripple=1e-5),
}
def quant(v,bits,fullscale=4.):
 return v if bits is None else round(v/fullscale*2**bits)*fullscale/2**bits

def schedule(X,p,n):
 if not(math.isfinite(X) and X>=1 and math.isfinite(p) and p>=1):raise ValueError('X>=1, p>=1, finite')
 # frexp performs binary range selection, not evaluation of the root.
 mx,ex=math.frexp(X);mx*=2;ex-=1
 a,b=0.,1.;ea,eb=0,ex;na,nb='unit','x'
 theta=1/p;steps=[]
 for i in range(n):
  m=(a+b)/2;em=(ea+eb)//2;parity=ea+eb-2*em;nm=f'm{i}'
  steps.append(dict(node=nm,a=na,b=nb,factor=2**parity))
  if theta<=m:b,eb,nb=m,em,nm
  else:a,ea,na=m,em,nm
 return dict(X=X,p=p,n=n,mx=mx,ex=ex,A=na,B=nb,ea=ea,eb=eb,lam=(theta-a)/(b-a),steps=steps)

def minimum_depth(X):
 # Since log2(X)<e+1, 2**n>=e+1 ensures B/A<2 in exact arithmetic.
 e=math.frexp(X)[1]-1
 return max(0,max(e,0).bit_length())

def make_netlist(s,profile,order,seed):
 cfg=PROFILES[profile];rng=random.Random(seed)
 def err():return rng.gauss(0,cfg['gain']),rng.gauss(0,cfg['offset'])
 def filt(name,expr):
  g,o=err();lines.extend([f'B{name}src {name}src 0 V=({expr})*({1+g:.17g})+({o:.17g})',f'R{name} {name}src {name} 10000',f'C{name} {name} 0 20p IC=0',f'Rl{name} {name} 0 {cfg["leak"]:.17g}'])
 lam=quant(s['lam'],cfg['dac_bits'],1.)
 lines=['Geometric subdivision: multiplier-feedback square-root cells',
 '.options reltol=1e-9 abstol=1e-13 vntol=1e-10 method=gear',
 'Vunit unit 0 1',f'Vx x 0 {quant(s["mx"],cfg["dac_bits"]):.17g}',f'Vweight w 0 {lam:.17g}']
 for j,st in enumerate(s['steps']):
  g,o=err();name=st['node'];gain=1e-4*(1+rng.uniform(-.05,.05))
  # clamped OTA current models finite slew; equilibrium is m²=2^parity*A*B.
  target=f'{st["factor"]}*v({st["a"]})*v({st["b"]})*({1+g:.17g})+({o:.17g})'
  lines += [f'B{name} 0 {name} I=min(0.001,max(-0.001,{gain:.17g}*(({target})-v({name})*v({name}))))+{cfg["ripple"]*gain:.17g}*sin(6.28318530718*1e6*time+{j})',f'C{name} {name} 0 {20e-12*(1+rng.uniform(-.1,.1)):.17g} IC=1',f'Rl{name} {name} 0 {cfg["leak"]:.17g}']
 # Feedback divider rather than an ideal instantaneous quotient for B/A.
 ratiofactor=2.**(s['eb']-s['ea']);g,o=err()
 lines += [f'Bratio 0 ratio I=min(0.001,max(-0.001,1e-4*({ratiofactor:.17g}*v({s["B"]})*{1+g:.17g}+({o:.17g})-v({s["A"]})*v(ratio))))', 'Cratio ratio 0 20p IC=1',f'Rlratio ratio 0 {cfg["leak"]:.17g}']
 filt('z','v(ratio)-1')
 if order==5:
  # P-Q=6*t*z*(2+z): compute an increment directly, avoiding subtraction of P/Q and 1.
  filt('z2','v(z)*v(z)')
  filt('ql','1+(1-v(w)/2)*v(z)+(v(w)-1)*(v(w)-2)*v(z2)/12')
  filt('qu','1+(1-(1-v(w))/2)*v(z)+(-v(w))*(-1-v(w))*v(z2)/12')
  filt('nl','v(w)*v(z)*(1+v(z)/2)')
  filt('nu','(1-v(w))*v(z)*(1+v(z)/2)')
  pairs=[('dl','nl','ql'),('du','nu','qu')]
 elif order==3:
  filt('ql','1+(1-v(w))*v(z)/2');filt('qu','1+v(w)*v(z)/2')
  filt('nl','v(w)*v(z)');filt('nu','(1-v(w))*v(z)')
  pairs=[('dl','nl','ql'),('du','nu','qu')]
 else:
  filt('nl','v(w)*v(z)');filt('nu','(1-v(w))*v(z)')
  lines+=['Vql ql 0 1','Vqu qu 0 1'];pairs=[('dl','nl','ql'),('du','nu','qu')]
 for name,num,den in pairs:
  g,o=err();lines += [f'B{name} 0 {name} I=min(0.001,max(-0.001,1e-4*(v({num})*{1+g:.17g}+({o:.17g})-v({den})*v({name}))))',f'C{name} {name} 0 20p IC=0',f'Rl{name} {name} 0 {cfg["leak"]:.17g}']
 # For order2, arithmetic is upper; complementary arithmetic gives harmonic lower.
 if order==2:
  low=f'{ratiofactor:.17g}*v({s["B"]})/(1+v(du))' # equals B/(1+(1-lambda)z)
  high=f'v({s["A"]})*(1+v(dl))'
 else:
  low=f'v({s["A"]})*(1+v(dl))'
  high=f'{ratiofactor:.17g}*v({s["B"]})/(1+v(du))'
 filt('lower',low);filt('upper',high)
 # A centered lower readout avoids subtracting two nearly equal voltages.
 # Its final scale and weight are recombined digitally; this is a hybrid output.
 if order==5:filt('ncore','v(z)*(1+v(z)/2)')
 else:filt('ncore','v(z)')
 lines += ['Bcore 0 core I=min(0.001,max(-0.001,1e-4*(v(ncore)-v(ql)*v(core))))','Ccore core 0 20p IC=0',f'Rlcore core 0 {cfg["leak"]:.17g}']
 # A declared bias-current estimate, not actual power of dependent sources.
 cells=len(s['steps'])+1+sum(1 for x in lines if x.startswith('B') and not x.startswith('Bratio'))-len(s['steps'])
 lines += ['.control','set noaskquit','set wr_singlescale','set wr_vecnames','set numdgt=17','tran 20n 30u uic',f'wrdata trace.csv v(lower) v(upper) v({s["A"]}) v(dl) v(ratio) v(core)', 'quit','.endc','.end']
 return '\n'.join(lines)+'\n',dict(cells=cells,lambda_dac=lam,lambda_exact=s['lam'],scale=2.**s['ea'])

def steady_metrics(row,data):
 """Worst error over the last 5 us, not a favorable ripple phase."""
 tail=data[data[:,0]>=data[-1,0]-5e-6]
 bits=PROFILES[row['profile']]['adc_bits'] if row['profile'] in PROFILES else int(row['profile'].replace('resolution',''))
 q=lambda v:v if bits is None else np.rint(v/4*2**bits)*4/2**bits
 s=schedule(row['X'],row['p'],row['n']);scale=row['scale']
 direct=(tail[:,1]+tail[:,2])/2*scale
 adc=(q(tail[:,1])+q(tail[:,2]))/2*scale
 am=np.ones(len(tail)) if s['A']=='unit' else q(tail[:,3])
 centered=scale*am*(1+s['lam']*q(tail[:,6]))
 ref=mp.mpf(row['reference'])
 answer={}
 for label,v in [('direct',direct),('adc',adc),('centered',centered)]:
  extremes=[mp.mpf(float(np.min(v))),mp.mpf(float(np.max(v)))]
  answer['steady_'+label+'_worst_relative_error']=float(max(abs(x/ref-1) for x in extremes))
  answer['steady_'+label+'_worst_excess_error']=float(max(abs((x-ref)/(ref-1)) for x in extremes)) if ref!=1 else None
  answer['steady_'+label+'_peak_to_peak']=float(np.ptp(v))
 answer['steady_observed_enclosure_all_samples']=bool(np.all(tail[:,1]*scale<=float(ref)) and np.all(tail[:,2]*scale>=float(ref)))
 return answer

def run_case(X,p,n,profile,order,seed,out):
 s=schedule(X,p,n);net,meta=make_netlist(s,profile,order,seed);out.mkdir(parents=True,exist_ok=True);(out/'circuit.cir').write_text(net)
 exe=shutil.which('ngspice') or '/opt/homebrew/bin/ngspice'
 start=time.perf_counter();proc=subprocess.run([exe,'-b','circuit.cir'],cwd=out,capture_output=True,text=True,timeout=60)
 (out/'ngspice.log').write_text(proc.stdout+proc.stderr)
 if proc.returncode:raise RuntimeError(proc.stderr[-1000:])
 data=np.loadtxt(out/'trace.csv',skiprows=1)
 if not np.isfinite(data).all():raise RuntimeError('Nonfinite transient')
 scale=meta['scale'];lo=data[:,1]*scale;hi=data[:,2]*scale
 ref=mp.power(mp.mpf(X),1/mp.mpf(p));reference=float(ref)
 final=(lo[-1]+hi[-1])/2
 bits=PROFILES[profile]['adc_bits'];adc=(quant(data[-1,1],bits)+quant(data[-1,2],bits))/2*scale
 # The controller retains the exact unit rail; other A values require ADC.
 am=1. if s['A']=='unit' else quant(data[-1,3],bits)
 core=quant(data[-1,6],bits)
 centered=scale*am*(1+s['lam']*core)
 err=lambda v:float(abs(mp.mpf(float(v))/ref-1))
 excess=lambda v:float(abs((mp.mpf(float(v))-ref)/(ref-1))) if ref!=1 else None
 # Settling relative to the final electrical value, not to the true root.
 center=(lo+hi)/2;bad=np.flatnonzero(np.abs(center-final)>abs(final)*1e-6)
 settling=float(data[min(int(bad[-1])+1,len(data)-1),0]) if len(bad) else float(data[0,0])
 row=dict(X=X,p=p,n=n,order=order,profile=profile,seed=seed,reference=mp.nstr(ref,45),lower=float(lo[-1]),upper=float(hi[-1]),root_relative_error=err(final),excess_relative_error=excess(final),adc_root_relative_error=err(adc),adc_excess_relative_error=excess(adc),centered_root_relative_error=err(centered),centered_excess_relative_error=excess(centered),observed_enclosure=bool(lo[-1]<=reference<=hi[-1]),reversed_bounds=bool(lo[-1]>hi[-1]),relative_width=float((hi[-1]-lo[-1])/reference),settling_1ppm_to_final_s=settling,wall_s=time.perf_counter()-start,signal_min=float(data[:,1:].min()),signal_max=float(data[:,1:].max()),assumed_bias_energy_J=meta['cells']*10e-6*3.3*settling,**meta)
 row.update(steady_metrics(row,data))
 return row

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--quick',action='store_true');args=ap.parse_args()
 pairs=[(2.,3.7),(500000.,1000000.),(500000.,1000000.125),(500000.,math.sqrt(2)),(2.,1.),(2.,1.000001),(2.,math.sqrt(2)),(1.000001,3.7),(1e12,1.1),(1e12,1e6),(500000.,37.5),(2.,1e9)]
 if args.quick:pairs=pairs[:2]
 rows=[];base=ROOT/('quick' if args.quick else 'results');base.mkdir(exist_ok=True)
 for X,p in pairs:
  n=max(2,minimum_depth(X))
  for order in [2,3,5]:
   for profile in PROFILES:
    seeds=[271828] if profile=='ideal' or args.quick else [271828,314159,161803]
    for seed in seeds:
     idx=len(rows);out=base/f'case_{idx:03d}'
     try:row=run_case(X,p,n,profile,order,seed,out)
     except Exception as e:row=dict(X=X,p=p,n=n,order=order,profile=profile,seed=seed,error=str(e))
     rows.append(row)
     if len(rows)%12==0:print(f'{len(rows)} runs, {sum("error" in x for x in rows)} execution failures',flush=True)
 (base/'summary.json').write_text(json.dumps(dict(scope='Behavioral mixed-signal feasibility model; no transistor/PDK validation or measured chip power',profiles=PROFILES,rows=rows),indent=2)+'\n')
 print(f'Saved {len(rows)} runs to {base}',flush=True)
if __name__=='__main__':main()
