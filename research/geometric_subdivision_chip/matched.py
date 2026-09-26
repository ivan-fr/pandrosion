"""Matched primitive study. Behavioral multipliers/sums, feedback quotients/means.
Same errors, RC ports, input step, coefficient grid and ADC for both architectures.
No transistor speed/energy inference from this experiment.
"""
from transistor import *
from v30_bridge import prepare,schedule,decode
import mpmath as mp

def deck(arch,case,profile):
 p,X=case['p'],case['originalX'];g,o=(0.,0.) if profile=='ideal' else (.001,.0002)
 tau=1e-6;L=['Matched primitive benchmark','.options reltol=1e-8 abstol=1e-13','Vone one 0 1'];counter=0
 def c(x):return round(x*2**24)/2**24
 def cell(expr,kind='sum',den=None):
  nonlocal counter
  name=f'c{counter}';counter+=1
  if kind=='sum':L.extend([f'B{name} {name}_src 0 V=({expr})*{1+g}+{o}',f'R{name} {name}_src {name} 10',f'C{name} {name} 0 100n IC=0'])
  else:
   back=f'v({name})*v({name})' if kind=='mean' else f'({den})*v({name})'
   L.extend([f'B{name} 0 {name} I=0.1*(({expr})*{1+g}+{o}-({back}))',f'C{name} {name} 0 100n IC=1'])
  L.extend([f'Rport{name} {name} 0 50000',f'Cport{name} {name} 0 2p'])
  return name
 def v(n):return f'v({n})'
 if arch=='subdivision':
  mx,eb=math.frexp(X);mx*=2;eb-=1;ea=0;L+=[f'Vx x 0 PULSE(1 {c(mx)} 2u 10n 10n 1 2)'];a,b='one','x';lo,hi=0.,1.
  for j in range(6):
   em=(ea+eb)//2;m=cell(f'{2**(ea+eb-2*em)}*{v(a)}*{v(b)}','mean');mid=(lo+hi)/2
   if 1/p<=mid:b,eb,hi=m,em,mid
   else:a,ea,lo=m,em,mid
  b=cell(f'{2**(eb-ea)}*{v(b)}');t=c((1/p-lo)/(hi-lo));aa=cell(v(a)+'*'+v(a));ab=cell(v(a)+'*'+v(b));bb=cell(v(b)+'*'+v(b));al=c((t+1)*(t+2)/12);be=c((8-2*t*t)/12);ga=c((t-1)*(t-2)/12)
  num=cell(f'{al}*{v(bb)}+{be}*{v(ab)}+{ga}*{v(aa)}');den=cell(f'{ga}*{v(bb)}+{be}*{v(ab)}+{al}*{v(aa)}');prod=cell(v(a)+'*'+v(num));out=cell(v(prod),'div',v(den));scale=2.**ea
 else:
  Y=case['Y'];q0=p*((p+1+(p-1)*Y)/(p-1+(p+1)*Y)-1);L += [f'Vx x 0 PULSE(1 {c(Y)} 2u 10n 10n 1 2)',f'Vq q 0 PULSE(0 {c(q0)} 2u 10n 10n 1 2)'];q=cell('v(q)');d=q
  for op in schedule(p):
   prod=cell(v(d)+'*'+v(d if op['kind']=='square' else q));expr=v(d)+'+'+str(c(op['product_weight']))+'*'+v(prod)
   if op['kind']!='square':expr+='+'+str(c(op['copy_weight']))+'*('+v(q)+'-'+v(d)+')'
   d=cell(expr)
  powr=cell('1+'+v(d));res=cell('v(x)*'+v(powr));den=cell(f'1+{v(res)}+({v(res)}-1)*{c(1/p)}');u=cell(f'1+{v(q)}*{c(1/p)}');e=cell('1-'+v(res));prod=cell('2*'+v(u)+'*'+v(e));delta=cell(v(prod),'div',v(den));out=cell(v(q)+'+'+v(delta));scale=None
 L+=['.control','set wr_singlescale','set wr_vecnames','set numdgt=17','tran 50n 240u uic',f'wrdata trace.txt v({out})','quit','.endc','.end']
 return '\n'.join(L)+'\n',counter,scale

def main():
 rows=[]
 for case in prepare([[p,x] for p in [3,7,32,1000000] for x in [2,500000]]):
  for profile in ['ideal','untrimmed']:
   for arch in ['subdivision','P6']:
    label=f'{arch}_{profile}_{case["p"]}_{case["originalX"]}';path=ROOT/'results/matched_raw'/label;path.mkdir(parents=True,exist_ok=True);net,count,scale=deck(arch,case,profile);(path/'circuit.cir').write_text(net)
    run=subprocess.run([NG,'-b','circuit.cir'],cwd=path,capture_output=True,text=True,timeout=60);(path/'ngspice.log').write_text(run.stdout+run.stderr)
    r=dict(id=label,arch=arch,profile=profile,p=case['p'],X=case['originalX'],cells=count)
    if run.returncode:r['error']=run.stderr[-1000:]
    else:
     a=np.loadtxt(path/'trace.txt',skiprows=1);q=np.rint(a[:,1]/4*2**24)*4/2**24;v=q*scale if arch=='subdivision' else 1/(case['c']*(1+q/case['p']));ref=float(mp.exp(mp.log(case['originalX'])/case['p']));err=np.abs(v/ref-1);r['window_error']=float(err[a[:,0]>=200e-6].max());r['final']=float(v[-1]);r['settling_1ppm_s']=None;bad=np.flatnonzero((a[:,0]>=2.01e-6)&(err>1e-6))
     if len(bad) and bad[-1]+1<len(a):r['settling_1ppm_s']=float(a[bad[-1]+1,0]-2.01e-6)
    rows.append(r);print(label,r.get('window_error',r.get('error')),flush=True)
    (ROOT/'results/matched.json').write_text(json.dumps(rows,indent=2)+'\n')
if __name__=='__main__':main()
