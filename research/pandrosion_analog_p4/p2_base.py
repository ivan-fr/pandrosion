"""P2: sampled functional core plus explicit closed-loop analog calibration.
Not manufacturer macromodels. Run with Python/numpy and ngspice.
"""
from pathlib import Path
import json, tempfile, subprocess
import numpy as np
from core_p1 import deck as core_deck, NG
P=Path(__file__).parent
V0=4.096
RUNS=0

def deck(mode,m,gain=1.,trim=0.,ref_ppm=0.,ratio_ppm=0.,amp_shift=0.):
 net,info=core_deck(mode,m,'untrimmed_stress')
 net=net.replace('Pandrosion P1','Pandrosion P2').replace('Vref ref 0 4\n',f'Vref ref 0 {V0*(1+ref_ppm*1e-6):.15g}\n')
 net=net.replace(f'Vm m 0 {4*m:.16g}',f'Vm m 0 {V0*m:.16g}')
 net=net.replace('Ron=100','Ron=120')
 # Isolate 10 nF memory capacitors from finite output drivers.
 net=net.replace('Sa sample_drive','Risoa sample_drive track_a 100\nSa track_a')
 net=net.replace('Sb memory_drive','Risob memory_drive track_b 100\nSb track_b')
 net=net.replace('Sr1 reset_drive','Risor reset_drive reset_iso 100\nSr1 reset_iso')
 net=net.replace('Sr2 reset_drive','Sr2 reset_iso')
 # Remove ideal reference scaling: divider + follower, closed-loop gain of two.
 net=net.replace('Ehalf ref_half 0 ref 0 0.5','Rhalf1 ref half_mid 10k\nRhalf2 half_mid 0 10k\nXhalf half_mid ref_half ref_half OA PARAMS: vo=0')
 net=net.replace('Edouble ref_double 0 ref 0 2','Rdouble1 ref_double double_fb 10k\nRdouble2 double_fb 0 10k\nXdouble ref double_fb ref_double OA PARAMS: vo=0')
 extra=f'''
* Two inverters implement a positive affine correction using real resistor KCL.
* Vtrim represents a bench trim source, not an implemented DAC/potentiometer.
Vtrim trim 0 {trim:.15g}
Rcalin out sum1 10k
Rcalfb neg sum1 {10000*gain*(1+ratio_ppm*1e-6):.15g}
Rcaloffset trim sum1 1meg
Xcal1 0 sum1 neg OA PARAMS: vo={25e-6+amp_shift:.15g}
Rcalin2 neg sum2 10k
Rcalfb2 corrected sum2 10k
Xcal2 0 sum2 corrected OA PARAMS: vo={-25e-6+amp_shift:.15g}
Rcal_load corrected 0 10k
Ccal_load corrected 0 20p
* Authored single-pole op amp: A0=1e6, GBW=10 MHz, SR=20 V/us,
* internal clamp +/-13 V, output limit 5 mA, Rout=10 ohms, bias=20 pA.
* This is not the OPA192 vendor model and does not prove load stability.
.subckt OA plus minus output PARAMS: vo=0
Bpole 0 internal I=1n*min(20meg,max(-20meg,(1meg*(v(plus)-v(minus)+vo)-v(internal))/0.0159154943092))
Brail internal 0 I=10*(max(0,v(internal)-13)+min(0,v(internal)+13))
Cpole internal 0 1n
Rbleed internal 0 1e12
Bdrive 0 output I=min(5m,max(-5m,(v(internal)-v(output))/10))
Rout output 0 1e12
Ibplus plus 0 20p
Ibminus minus 0 20p
.ends OA
'''
 net=net.replace('.control',extra+'\n.control')
 net=net.replace('v(cb) v(clipratio)','v(cb) v(clipratio) v(corrected) v(neg)')
 return net,info

def run(mode,m,gain=1.,trim=0.,ref_ppm=0.,ratio_ppm=0.,amp_shift=0.,keep=None):
 global RUNS
 net,info=deck(mode,m,gain,trim,ref_ppm,ratio_ppm,amp_shift)
 with tempfile.TemporaryDirectory(prefix='pandro_p2_') as tmp:
  d=Path(tmp); (d/'core.cir').write_text(net)
  p=subprocess.run([NG,'-b','core.cir'],cwd=d,capture_output=True,text=True,timeout=90)
  if p.returncode or not (d/'waveform.txt').exists(): raise RuntimeError(p.stdout+p.stderr)
  a=np.loadtxt(d/'waveform.txt',skiprows=1)
  assert np.isfinite(a).all()
  if keep:
   (P/f'{keep}.cir').write_text(net);(P/f'{keep}.log').write_text(p.stdout+p.stderr)
   np.savetxt(P/f'{keep}.csv',a[::5],delimiter=',',header='time,state,candidate,raw,geometry,next,num,den,ca,cb,port_ratio,corrected,negative',comments='')
 t=info['reset']+info['cycles']*info['period']-5e-6
 raw=float(np.interp(t,a[:,0],a[:,3]));out=float(np.interp(t,a[:,0],a[:,11]))
 mask=a[:,0]>80e-6
 row=dict(mode=mode,m=m,raw_volts=raw,corrected_volts=out,raw_error=raw/(V0*m**(1/3))-1,corrected_error=out/(V0*m**(1/3))-1,ref_ppm=ref_ppm,ratio_ppm=ratio_ppm,amp_shift_volts=amp_shift,port_peak=float(a[mask,10].max()),sample_us=t*1e6)
 assert row['port_peak']<.95, row
 RUNS+=1
 return row

def main():
 results=[]
 for mode in ['AD','Halley']:
  # Calibrate the complete electrical output stage, then freeze both controls.
  gain,trim=1.,0.
  tuning=[]
  for _ in range(2):
   r1=run(mode,1,gain,trim);r2=run(mode,2,gain,trim)
   a=V0*(2**(1/3)-1)/(r2['corrected_volts']-r1['corrected_volts'])
   b=V0-a*r1['corrected_volts']
   tuning.append(dict(gain=gain,trim_volts=trim,endpoint_errors=[r1['corrected_error'],r2['corrected_error']]))
   gain*=a;trim+=b/(gain*.01)
  assert .98<gain<1.02 and abs(trim)<2
  rows=[run(mode,m,gain,trim,keep=mode.lower()+'_p2' if m==2 else None) for m in [1.,1.1,1.35,1.6,1.9,2.]]
  corners=[]
  # Frozen calibration; one mechanism at a time, not vendor worst-case corners.
  for case,kw in [('ref_minus',dict(ref_ppm=-200)),('ref_plus',dict(ref_ppm=200)),('ratio_minus',dict(ratio_ppm=-100)),('ratio_plus',dict(ratio_ppm=100)),('amp_shift',dict(amp_shift=25e-6))]:
   for m in [1.1,1.9]:
    r=run(mode,m,gain,trim,**kw);r['case']=case;corners.append(r)
  results.append(dict(mode=mode,gain=gain,feedback_ohms=10000*gain,trim_volts=trim,tuning=tuning,nominal=rows,frozen_calibration_corners=corners))
  print(mode,'done',flush=True)
 out=dict(scope='Authored functional core plus explicit op-amp feedback and resistor calibration; not vendor models or fabricated circuit',vref_nominal=V0,input_convention='Vin=4.096*m fixed independently of reference drift; target Vout=4.096*cuberoot(m)',spice_runs=RUNS,results=results)
 (P/'results.json').write_text(json.dumps(out,indent=2)+'\n')
 for r in results:
  print(r['mode'],'raw max %',100*max(abs(x['raw_error']) for x in r['nominal']),'corrected heldout max %',100*max(abs(x['corrected_error']) for x in r['nominal'] if x['m'] not in [1,2]),'corners max %',100*max(abs(x['corrected_error']) for x in r['frozen_calibration_corners']))
 print('SPICE runs',RUNS)
if __name__=='__main__':main()
