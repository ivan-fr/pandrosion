"""Paired small-signal noise check; deterministic error is not effective resolution."""
from improve import *

def main():
 d=json.loads((P/'results.json').read_text());rows=[]
 for j in d['jobs'][:2]:
  for mode in ['old','r2']:
   cfg={**d['config'],'output_gain':j['output_gain']} if mode=='r2' else dict(n=6)
   for band in [1e6,1e9]:
    label=f'noise_{j["p"]}_{mode}_{band}';path=P/'raw'/label;path.mkdir(parents=True,exist_ok=True)
    lines,_,_=build(kind='root',p=j['p'],X=j['X'],**cfg);lines=[l+' AC 1' if l.startswith('Ix ') else l for l in lines]
    lines+=['.control','set numdgt=17',f'noise v(n_load) Ix dec 30 1 {band:.17g}','setplot noise2','print onoise_total','quit','.endc','.end']
    (path/'circuit.cir').write_text('\n'.join(lines)+'\n');run=subprocess.run([NG,'-b','circuit.cir'],cwd=path,capture_output=True,text=True,timeout=60);log=run.stdout+run.stderr;(path/'ngspice.log').write_text(log)
    m=re.search(r'onoise_total\s*=\s*([\deE.+-]+)',log)
    rows.append(dict(p=j['p'],X=j['X'],mode=mode,band_Hz=[1,band],noise_V_RMS=float(m[1]) if m else None,error=None if m else log[-1000:]))
 (P/'noise.json').write_text(json.dumps(rows,indent=2)+'\n');print(json.dumps(rows,indent=2))
if __name__=='__main__':main()
