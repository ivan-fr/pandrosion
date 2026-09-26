"""Electrical-reference calibration of the unchanged simulated read/hold/SAR chain."""
from improve import *
import interface

def main():
 d=json.loads((P/'results.json').read_text());records=[]
 for bits in [20,24]:
  refs=[.7,.85,1.,1.15,1.3];train=[]
  for k,ref in enumerate(refs):
   r=interface.run(3.7,2,bits=bits,label=f'cal_adc_{bits}_{k}',reference_input=ref)
   if 'error'in r:raise RuntimeError(r['error'])
   train.append(r)
  off,gain=np.linalg.lstsq(np.column_stack([np.ones(len(refs)),refs]),[r['adc_voltage'] for r in train],rcond=None)[0]
  vals=[]
  for j in d['jobs'][:2]:
   for mode in ['old','r2']:
    cfg={**d['config'],'output_gain':j['output_gain']} if mode=='r2' else None
    r=interface.run(j['p'],j['X'],bits=bits,core_config=cfg,label=f'{mode}_adc_cal_{bits}',adc_calibration=[off,gain]);vals.append(dict(mode=mode,**r));print(bits,mode,j['p'],r.get('relative_error'),flush=True)
  records.append(dict(bits=bits,training=train,calibration=[float(off),float(gain)],validation=vals))
 (P/'adc-calibrated.json').write_text(json.dumps(records,indent=2)+'\n')
if __name__=='__main__':main()
