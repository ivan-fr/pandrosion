"""P4: explicit single-ended XY/Z loads and memory/attenuator isolation.
Custom functional arithmetic and amplifier macros; no vendor/PDK model.
"""
from pathlib import Path
import json
import numpy as np
import p3_base as base
P=Path(__file__).parent

def deck(mode,m,gain,trim,buffered=False,rin=50000,bias=50e-9,cinput=2e-12):
 net=base.build_chain(mode,m,gain,trim)
 ports= [('q2','state','state'),('q3','q2','state'),('t','q3','m'),('next','num','state'),('inverse','ref_half','ref_double'),('geometry','q2','m')] if mode=='AD' else [('q2','att_state','gainstate'),('q3','att_q2','gainstate'),('next','att_num','gainstate')]
 extras=[]
 if buffered:
  extras += ['Xread state state_read state_read OA PARAMS: vo=25u']
  if mode=='AD':
   lines=net.splitlines()
   for i,l in enumerate(lines):
    if l.startswith(('Bint_q2 ','Bint_q3 ','Bint_next ','Bclipratio ')):lines[i]=l.replace('v(state)','v(state_read)')
    if l.startswith('Xden_inverse '):lines[i]=l.replace(' state ',' state_read ')
   net='\n'.join(lines)+'\n'
   ports=[(n,'state_read' if x=='state' else x,'state_read' if y=='state' else y)for n,x,y in ports]
  else:
   net=net.replace('Egainstate gs_target 0 state 0','Egainstate gs_target 0 state_read 0')
   net=net.replace('v(state)+','v(state_read)+')
   for node in ['att_state','att_q2','att_num']:
    lines=net.splitlines()
    for i,l in enumerate(lines):
     if l.startswith(('Rtop_','Rbot_')):lines[i]=l.replace(' '+node+' ',' '+node+'_raw ')
    net='\n'.join(lines)+'\n'
    extras.append(f'Xbuf_{node} {node}_raw {node} {node} OA PARAMS: vo=25u')
 for name,x,y in ports:
  for tag,node in [('x',x),('y',y),('z',name)]:
   extras += [f'Rport_{name}_{tag} {node} 0 {rin:.12g}',f'Cport_{name}_{tag} {node} 0 {cinput:.12g}',f'Iport_{name}_{tag} {node} 0 {bias:.12g}']
 net=net.replace('.control','\n'.join(extras)+'\n.control')
 return net

def run(mode,m,gain,trim,buffered,rin=50000,bias=50e-9,cinput=2e-12,keep=None):
 a=base.execute(deck(mode,m,gain,trim,buffered,rin,bias,cinput),keep)
 out=float(np.interp(645e-6,a[:,0],a[:,11]))
 # Last hold: state switch opens near 625 us; sample 626..649 us.
 v1=float(np.interp(626e-6,a[:,0],a[:,1]));v2=float(np.interp(649e-6,a[:,0],a[:,1]))
 return dict(mode=mode,m=m,buffered=buffered,rin=rin,bias_amp=bias,cinput_pf=cinput*1e12,output_volts=out,error=out/(base.V0*m**(1/3))-1,hold_change_ppm=(v2/v1-1)*1e6,port_peak=float(a[a[:,0]>80e-6,10].max()))

def main():
 prior=json.loads((P/'p3_reference.json').read_text());results=[]
 for mode in ['AD','Halley']:
  old=next(x for x in prior['chains'] if x['mode']==mode)
  loaded=[run(mode,m,old['gain'],old['trim_volts'],False,keep=mode.lower()+'_loaded' if m==2 else None) for m in [1,1.1,1.35,1.6,1.9,2]]
  gain,trim=1.,0.
  for _ in range(2):
   a=run(mode,1,gain,trim,True);b=run(mode,2,gain,trim,True)
   slope=base.V0*(2**(1/3)-1)/(b['output_volts']-a['output_volts']);offset=base.V0-slope*a['output_volts']
   gain*=slope;trim+=offset/(gain*.01)
  fixed=[run(mode,m,gain,trim,True,keep=mode.lower()+'_buffered' if m==2 else None) for m in [1,1.1,1.35,1.6,1.9,2]]
  corners=[run(mode,m,gain,trim,True,rin,bias,10e-12)for rin,bias in [(40000,150e-9),(60000,-150e-9)]for m in [1.1,1.9]]
  results.append(dict(mode=mode,gain=gain,trim_volts=trim,loaded_without_new_buffers=loaded,buffered=fixed,frozen_calibration_corners=corners))
  print(mode,'completed',gain,trim,flush=True)
 result=dict(spice_runs=base.COUNT,scope='Ground-referenced 50 kohm XY/Z load model plus custom followers, not vendor models',results=results)
 (P/'results.json').write_text(json.dumps(result,indent=2)+'\n')
 for x in results:print(x['mode'],[(k,max(abs(v['error'])for v in x[k]))for k in ['loaded_without_new_buffers','buffered','frozen_calibration_corners']])
if __name__=='__main__':main()
