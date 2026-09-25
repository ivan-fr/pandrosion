"""Positive homogeneous Padé and transistor geometric means.
T1: real BJT junctions, ideal current copies (diagnostic only).
T2: BJT junctions AND real mirrors. Only input/bias/trim sources and rails ideal.
The inherited transistor topology is from the preserved P5/P6 sources.
"""
from pathlib import Path
import sys,types,math,tempfile,subprocess,json,hashlib,random,re
import numpy as np
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'vendor/previous'))
import translinear as T
# Only adapt imports; equations/mirror code in the vendored file remain intact.
source=(ROOT/'vendor/previous/translinear_chain3.py').read_text()
source=source.replace('from v30_bridge import schedule','')
mod=types.ModuleType('previous_t2');mod.__file__=str(ROOT/'vendor/previous/translinear_chain3.py');exec(compile(source,mod.__file__,'exec'),mod.__dict__)
NG='/opt/homebrew/bin/ngspice' if Path('/opt/homebrew/bin/ngspice').exists() else 'ngspice'

def header(level,temp=25,vscale=1.,device='generic',corner='t'):
 if device=='generic':return mod.headers(temp=temp,vcc=4*vscale,vee=-2.5*vscale,ikf=.05)
 return skyheader(temp,vscale,corner)

def build(kind='mean',level='T2',A=1.,B=2.,A2=None,B2=None,p=3.7,X=2.,n=2,I0=1e-5,temp=25,vscale=1.,edge=10e-9,device='generic',corner='t',mismatch=0.,seed=1,trim=None,load=1e-12,coeff_bits=24,load_R=1000.,startup=False,ramp=False):
 if not (math.isfinite(X) and X>=1 and math.isfinite(p) and p>=1 and isinstance(n,int) and n>=0):raise ValueError('Require finite X>=1, p>=1 and integer n>=0')
 net=mod.NetT2Chain(I0,clamps=True) if level=='T2' else T.Net(helper=True,bleed=.2*I0)
 # iid synthetic area perturbations, NOT a foundry statistical mismatch model.
 if mismatch:
  rng=random.Random(seed);oldq=net.q
  def q(name,c,b,e,kind='QN',area=1.):return oldq(name,c,b,e,kind,area*max(.5,1+rng.gauss(0,mismatch)))
  net.q=q
 net.add(f'* {kind} level={level} device={device}',*header(level,temp,vscale,device,corner))
 def inp(name,a,b=None):
  cur=f'{a*I0:.17g}' if b is None else f'PULSE({a*I0:.17g} {b*I0:.17g} 100n {edge:.17g} {edge:.17g} 10u 20u)'
  if level=='T2':return net.dac(name,cur)
  net.add(f'I{name} vcc n_{name} {cur}',f'Vin_{name} n_{name} vee 0');return f'Vin_{name}'
 unit=inp('unit',1.)
 def summ(name,items):
  items=[(src,r) for src,r in items if r>0]
  if level=='T2':return net.node(name,items,[])
  net.add(f'V{name} n_{name} vee 0')
  for src,r in items:net.source_copy(src,f'n_{name}',r)
  return f'V{name}'
 def loop(name,a,b,d):return net.loop(name,ups=[a,b],downs=[d,None])
 def mean(name,a,b,factor=1.):
  if level=='T2':
   feedback=mod.Sig('feedback','pnp',None)
   out=loop(name,[(a,factor)],[(b,1.)],[(feedback,1.)]);out.sinks.extend(feedback.sinks);out.sources.extend(feedback.sources)
  else:out=loop(name,[(a,factor)],[(b,1.)],[(f'V{name}_out',1.)])
  if trim:
   k,o=trim
   if level=='T2':
    out=net.node(name+'trim',[(out,1/k)]+([(unit,-o/k)] if o<0 else []),[(unit,o/k)] if o>0 else [])
   else:
    raw=out;out=summ(name+'trim',[(raw,1/k)]+([(unit,-o/k)] if o<0 else []))
    if o>0:net.sink_copy(unit,f'n_{name}trim',o/k)
  return out
 if kind=='mean':
  a=inp('a',A,A2);b=inp('b',B,B2);out=mean('gm',a,b);scale=1.
 elif kind in ('root','rails'):
  mx,ex=math.frexp(X);mx*=2;ex-=1
  # Change the mantissa X while preserving this job's programmed exponents/branches.
  a=unit;b=inp('x',mx, B2 if B2 is not None else None);ea=0;eb=ex;lo=0.;hi=1.
  for j in range(n):
   em=(ea+eb)//2;factor=2**(ea+eb-2*em);m=mean(f'gm{j}',a,b,factor)
   mid=(lo+hi)/2
   if 1/p<=mid:hi,b,eb=mid,m,em
   else:lo,a,ea=mid,m,em
  if kind=='rails':out=b;scale=2.**eb
  else:
   weight=(1/p-lo)/(hi-lo);weight=round(weight*2**coeff_bits)/2**coeff_bits
   # Physical rail currents are rescaled to the same binary unit before products.
   b=summ('bscale',[(b,2.**(eb-ea))])
   aa=loop('aa',[(a,1)],[(a,1)],[(unit,1)])
   ab=loop('ab',[(a,1)],[(b,1)],[(unit,1)])
   bb=loop('bb',[(b,1)],[(b,1)],[(unit,1)])
   alpha=(weight+1)*(weight+2)/12;beta=(8-2*weight**2)/12;gamma=(weight-1)*(weight-2)/12
   num=summ('num',[(bb,alpha),(ab,beta),(aa,gamma)])
   den=summ('den',[(bb,gamma),(ab,beta),(aa,alpha)])
   out=loop('pade',[(a,1)],[(num,1)],[(den,1)]);scale=2.**ea
 else:raise ValueError(kind)
 if level=='T2':
  out.sources.append(('n_meas',1.));net.add('Vmeas n_meas n_load 0',f'Rload n_load 0 {load_R:.17g}',f'Cload n_load 0 {load:.17g}');net.emit();sense='Vmeas'
 else:sense=out
 # All voltage-source power is included, including collector/cascode/clamp rails.
 # Ideal current references are external ports and are reported separately.
 lines=net.lines
 if device=='sky130':lines=convert_sky(lines)
 if ramp:
  ramped=['* Ramped supplies and reference currents', 'Venable enable 0 PWL(0 0 100n 0 1u 1)']
  for l in lines:
   w=l.split()
   if w and w[0].lower() in ['vcc','vee','vb','vcn','vcp','vclampn','vclampp']:
    l=' '.join(w[:3])+f' PWL(0 0 100n 0 1u {w[3]})'
   elif w and w[0].startswith('I') and len(w)==4:
    l='B'+w[0]+' '+' '.join(w[1:3])+f' I=({w[3]})*v(enable)'
   ramped.append(l)
  lines=ramped
 return lines,sense,dict(scale=scale,I0=I0,transistors=len(net.junctions),kind=kind,level=level,device=device,p=p,X=X,n=n,A=A,B=B,temp=temp,vscale=vscale,edge=edge,load=load,load_R=load_R,trim=trim,startup=startup,mismatch=mismatch,seed=seed,ramp=ramp)

def execute(lines,sense,meta,out,duration=2e-6,dt=1e-9):
 out=Path(out);out.mkdir(parents=True,exist_ok=True)
 ctrl=['.control','set noaskquit','set wr_singlescale','set wr_vecnames','set numdgt=17',f'tran {dt:.17g} {duration:.17g} 0 {dt:.17g}'+(' uic' if meta.get('startup') else ''),f'wrdata trace.txt i({sense}) i(vcc) i(vee) i(vb) i(vcn) i(vcp) i(vclampn) i(vclampp) v(vcc) v(vee) v(vb) v(vcn) v(vcp) v(clampn) v(clampp)','quit','.endc','.end']
 if meta['level']=='T1': # same supply list exists through headers
  pass
 text='\n'.join(lines+ctrl)+'\n';(out/'circuit.cir').write_text(text)
 try:pr=subprocess.run([NG,'-b','circuit.cir'],cwd=out,capture_output=True,text=True,timeout=45)
 except subprocess.TimeoutExpired as e:
  decode=lambda v:v.decode(errors='replace') if isinstance(v,bytes) else (v or '')
  (out/'ngspice.log').write_text(decode(e.stdout)+decode(e.stderr)+'\nSolver timeout after 45 seconds.\n')
  return dict(**meta,error='Solver timeout after 45 seconds')
 log=pr.stdout+pr.stderr;(out/'ngspice.log').write_text(log)
 if pr.returncode or not(out/'trace.txt').exists():return dict(**meta,error=log[-1500:])
 data=np.loadtxt(out/'trace.txt',skiprows=1)
 if data.ndim!=2 or not np.isfinite(data).all():return dict(**meta,error='nonfinite trace')
 values=data[:,1]/meta['I0']*meta['scale'];tail=values[data[:,0]>.8*duration]
 # signed sum of all explicit voltage-rail power delivered to the circuit
 power=-(data[:,2:9]*data[:,9:16]).sum(axis=1)
 return dict(**meta,final=float(values[-1]),tail_min=float(tail.min()),tail_max=float(tail.max()),tail_pp=float(np.ptp(tail)),power_W=float(np.mean(power[data[:,0]>.8*duration])),energy_J=float(np.trapezoid(power,data[:,0])),duration=duration,dt=dt,rail_accounting='explicit voltage rails only; external ideal input/bias current sources and converters not included',warnings=[l for l in log.splitlines() if any(k in l.lower() for k in ['warning','unrecognized','ignored'])])

def skyheader(temp,vscale,corner):
 # Explicit research adapter: retain foundry equations; area scaling and terminal
 # ties are our circuit assumptions, not a layout-qualified foundry cell array.
 from sky_adapter import models
 return [l for l in mod.headers(temp=temp,vcc=4*vscale,vee=-2.5*vscale) if not l.startswith(('.model QN','.model QP'))]+models(corner)
def convert_sky(lines):
 out=[]
 for l in lines:
  if l.startswith('Q'):
   w=l.split();w.insert(4,'vee' if w[4]=='QN' else 'vcc');l=' '.join(w)
  out.append(l)
 return out

if __name__=='__main__':
 for level in ['T1','T2']:
  for kind in ['mean','root']:
   r=execute(*build(kind=kind,level=level),ROOT/'pilot'/f'{level}_{kind}')
   print(json.dumps(r),flush=True)
