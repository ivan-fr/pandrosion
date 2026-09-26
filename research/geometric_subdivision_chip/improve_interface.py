"""Keep the old converters; evaluate whether the core gain survives readout."""
from improve import *
import interface

def main():
 d=json.loads((P/'results.json').read_text());rows=[]
 for j in d['jobs'][:2]:
  cfg={**d['config'],'output_gain':j['output_gain']}
  for mode in ['old','r2']:
   r=interface.run(j['p'],j['X'],core_config=cfg if mode=='r2' else None,label=mode+'_r2study');rows.append(dict(mode=mode,**r))
 (P/'interface.json').write_text(json.dumps(rows,indent=2)+'\n')
 # A separate fixed bit-depth sensitivity; no policy is selected from these scores.
 bits=[];j=d['jobs'][1]
 for b in [16,20,24]:
  q=lambda x:round(x*2**b)/2**b
  cfg={**d['config'],'mirror_gains':{k:q(v) for k,v in d['config']['mirror_gains'].items()},'mean_feedback':q(d['config']['mean_feedback']),'output_gain':q(j['output_gain'])}
  r=score(sim(f'trimbits{b}',kind='root',p=j['p'],X=j['X'],**cfg),j['X'],j['p']);bits.append(dict(bits=b,result=r))
 (P/'trim-resolution.json').write_text(json.dumps(bits,indent=2)+'\n')
 print([(r['mode'],r['p'],r.get('relative_error')) for r in rows])
if __name__=='__main__':main()
