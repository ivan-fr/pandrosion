"""Noise and shared-device historical controls; no favorable-point calibration."""
from transistor import *
from v30_bridge import schedule
mod.schedule=schedule

def noise():
 rows=[]
 for device in ['generic','sky130']:
  for kind in ['mean','root']:
   path=ROOT/'results/noise_raw'/f'{device}_{kind}';path.mkdir(parents=True,exist_ok=True)
   lines,sense,meta=build(kind=kind,device=device,n=6)
   src='Ia' if kind=='mean' else 'Ix'
   lines=[l+' AC 1' if l.startswith(src+' ') else l for l in lines]
   lines+=['.control','set numdgt=17',f'noise v(n_load) {src} dec 30 1 1G','setplot noise2','print onoise_total','quit','.endc','.end']
   (path/'circuit.cir').write_text('\n'.join(lines)+'\n');r=subprocess.run([NG,'-b','circuit.cir'],cwd=path,capture_output=True,text=True,timeout=60);log=r.stdout+r.stderr;(path/'ngspice.log').write_text(log)
   m=re.search(r'onoise_total\s*=\s*([\deE.+-]+)',log);rows.append(dict(device=device,kind=kind,band_Hz=[1,1e9],output_voltage_noise_V=float(m[1]) if m else None,equivalent_current_noise_A=float(m[1])/1000 if m else None,scope='small-signal BJT/resistor noise around computed DC point; not transient noise or input-reference/converter noise',error=None if m else log[-1000:]))
 (ROOT/'results/noise.json').write_text(json.dumps(rows,indent=2)+'\n')

def controls():
 rows=[]
 for arch in ['P5','P6']:
  for p in ([3] if arch=='P5' else [3,7,32]):
   for x in [1.2,1.7,2.]:
    I0=1e-5
    if arch=='P5':
     net,sense=T.build_t2(I0=I0,m=x,ikf=.05);net.lines=[l.replace('Ikf=8m','Ikf=0.05') for l in net.lines];net.add('Vclampn clampn 0 -0.8','Vclampp clampp 0 2.3')
    else:
     q=p*((p+1+(p-1)*x)/(p-1+(p+1)*x)-1);net,sense=mod.build_chain3(p,x,q0=q,I0=I0,ikf=.05)
    meta=dict(I0=I0,scale=1.,level='T2',device='generic',kind=arch,transistors=len(net.junctions),p=p,X=x,vscale=1.)
    try:r=execute(net.lines,sense,meta,ROOT/'results/controls_raw'/f'{arch}_{p}_{x}',duration=1e-6)
    except subprocess.TimeoutExpired:r=dict(**meta,error='timeout')
    if 'final'in r:
     # P6 output is shifted normalized AD state 1+q, not the root.
     val=r['final'] if arch=='P5' else 1/(1+(r['final']-1)/p)
     r['decoded']=val;r['relative_error']=abs(val/x**(1/p)-1)
    rows.append(r);print(arch,p,x,r.get('relative_error',r.get('error')),flush=True)
    (ROOT/'results/controls.json').write_text(json.dumps(rows,indent=2)+'\n')
if __name__=='__main__':noise();controls()
