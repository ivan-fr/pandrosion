"""Mixed-signal wrapper for the transistor core. Behavioral DAC/ADC, not CMOS converters.
Coefficients preloaded; one mantissa job transition. Fixed read at 2.1 us,
20 SAR decisions at 20 ns/bit. No time chosen from a target root.
"""
from transistor import *

def run(p,X,bits=20,core_config=None,label=None,reference_input=None,adc_calibration=None):
 options=dict(kind='root',p=p,X=X,n=6);options.update(core_config or {})
 lines,sense,meta=build(**options)
 mx=math.frexp(X)[0]*2;lsb=4/2**bits;command=round(mx/lsb)*lsb
 # DAC voltage RC and ideal transconductance: current delivered through the real
 # input mirrors. Quantized 0..4 unit current range, no perfect output-current copy.
 new=[]
 for l in lines:
  if l.startswith('Ix '):
   new += [f'Vdac dac_cmd 0 PULSE(1 {command:.17g} 100n 10n 10n 1 2)','Rdac dac_cmd dac 100','Cdac dac 0 1n',f'Bdac vcc n_x I=v(dac)*{meta["I0"]}']
  else:new.append(l)
 new += ['* Behavioral transimpedance read amplifier and finite sample/hold', 'Bread read_src 0 V=v(n_load)*100*(1+1e-5)+25u','Rread read_src read 100','Cread read 0 10p','.model SADC SW(Ron=120 Roff=1e12 Vt=0.5 Vh=0.1)','Vsample sample 0 PULSE(0 1 2u 1n 1n 100n 10u)','Ssample read held sample 0 SADC','Chold held 0 10p','Rhold held 0 1e12','Iinject 0 held PULSE(0 1u 2.101u .1n .1n .9n 10u)']
 if reference_input is not None:
  new=[l.replace('v(n_load)*100',f'({reference_input:.17g})') if l.startswith('Bread ') else l for l in new]
 end=2.101e-6+bits*20e-9
 path=ROOT/'results/interface_raw'/(f'p{p}_X{X}'+('' if label is None else '_'+label));path.mkdir(parents=True,exist_ok=True)
 ctrl=['.control','set numdgt=17','set wr_singlescale','set wr_vecnames',f'tran 1n {end+1e-8:.17g} 0 1n','wrdata trace.txt v(held) v(n_load) v(dac)','quit','.endc','.end']
 (path/'circuit.cir').write_text('\n'.join(new+ctrl)+'\n');proc=subprocess.run([NG,'-b','circuit.cir'],cwd=path,capture_output=True,text=True,timeout=60);(path/'ngspice.log').write_text(proc.stdout+proc.stderr)
 row=dict(p=p,X=X,bits=bits,acquisition_end_s=2.101e-6,conversion_end_s=end,latency_from_input_edge_s=end-100e-9,coefficient_programming='preloaded, excluded',converter_scope='behavioral DAC RC and current source, read amplifier, SPICE switch/hold, timed numerical SAR; no converter transistor design or converter power')
 if proc.returncode:row['error']=proc.stderr[-1500:];return row
 a=np.loadtxt(path/'trace.txt',skiprows=1);code=0;decisions=[]
 for bit in reversed(range(bits)):
  t=2.101e-6+(bits-bit)*20e-9;obs=float(np.interp(t,a[:,0],a[:,1]));trial=code+2**bit
  if obs>=trial*lsb:code=trial
  decisions.append(dict(t=t,bit=bit,observed_V=obs,code=code))
 voltage=code*lsb
 if reference_input is not None:
  row.update(reference_input=reference_input,adc_voltage=voltage,decisions=decisions)
  return row
 if adc_calibration is not None:
  offset,gain=adc_calibration;voltage=(voltage-offset)/gain
 output=voltage*meta['scale'];reference=X**(1/p)
 row.update(code=code,decoded=output,relative_error=abs(output/reference-1),excess_error=abs((output-reference)/(reference-1)),core_current_A=float(a[-1,2]/1000),decisions=decisions)
 return row
if __name__=='__main__':
 rows=[run(p,x) for p,x in [(3.7,2),(3.7,3),(1000000,500000)]]
 (ROOT/'results/interface.json').write_text(json.dumps(rows,indent=2)+'\n')
 print([(r['p'],r['X'],r.get('relative_error',r.get('error'))) for r in rows])
