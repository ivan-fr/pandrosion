"""High-precision falsification, not a convergence proof; reproducible fixed grids."""
from pathlib import Path
import json
import mpmath as mp
mp.mp.dps=180
OUT=Path(__file__).resolve().parent
PS=[3,4,5,7,10,32,100,1000]
def coefficients(p,n):
 # Diagonal and neighboring Padé around t=1, computed at high precision from exact recurrences.
 L,M=n
 a=[mp.mpf(1)]
 for j in range(1,L+M+2):a.append(a[-1]*(-mp.mpf(1)/p-j+1)/j)
 return mp.pade(a,L,M)
CACHE={(p,n):coefficients(p,n) for p in PS for n in [(3,2),(3,3),(4,3),(4,4)]}
def evaluate(name,p,t):
 p=mp.mpf(p)
 if name=='AK':return p/(p-1+t)
 if name=='AD':return (p+1+(p-1)*t)/(p-1+(p+1)*t)
 if name=='projective':return 2*p*((2*p-1)*t+p+1)/((p+1)*t*t+2*(2*p-1)*(p+1)*t+(2*p-1)*(p-1))
 if name=='AD5':
  g=(p-1)*mp.sqrt(((p-2)*(t*t+1)+(10*p+4)*t)/(12*p));return (1+g)/(t+g)
 if name.startswith('pade'):
  n={'pade32':(3,2),'pade33':(3,3),'pade43':(4,3),'pade44':(4,4)}[name]
  a,b=CACHE[int(p),n];return mp.polyval(a[::-1],t-1)/mp.polyval(b[::-1],t-1)
 z=(t-1)/(t+1)
 if name=='radical7':a=3*p*(p*p+1)/(2*(4*p*p-1));b=0;c=5*p*(p*p-1)/(2*(4*p*p-1));d=-4*(4*p*p-1)/(15*p*p)
 else:
  a=3*p*(71*p**4+90*p*p-26)/(5*(11*p*p-2)**2)
  b=(p*p-4)*(p*p-1)/(15*p*(11*p*p-2));c=98*p*(p*p-1)*(4*p*p-1)/(5*(11*p*p-2)**2);d=-2*(11*p*p-2)/(21*p*p)
 q=1+d*z*z
 if q<=0:raise ValueError('radicand_nonpositive')
 D=a+b*z*z+c*mp.sqrt(q)
 return (D-z)/(D+z)
def logerror(name,p,e):
 if abs(p*e)>mp.mpf('1e6'):raise ValueError('log_residual_safety_cap')
 C=evaluate(name,p,mp.exp(p*e))
 if not mp.isfinite(C) or C<=0:raise ValueError('nonpositive_correction')
 return e+mp.log(C)
names=['AK','AD','projective','AD5','pade32','pade33','pade43','pade44','radical7','radical9']
res={}
for name in names:
 r=dict(samples=0,invalid=0,noncontracting=0,crossing=0,first_failure=None,local_order={},reciprocity_max='0',orbit_failures=[],max_orbit_steps=0)
 symmetry=mp.mpf(0)
 for p in PS:
  ts=[mp.power(10,j) for j in range(-100,101)]+[mp.exp(mp.mpf(j)/100) for j in range(-200,201) if j]
  for t in ts:
   if t==1:continue
   r['samples']+=1
   try:
    C=evaluate(name,p,t)
    if not mp.isfinite(C) or C<=0:raise ValueError('nonpositive_correction')
    e=mp.log(t)/p;en=e+mp.log(C)
    if abs(en)>=abs(e):r['noncontracting']+=1
    if en*e<0:r['crossing']+=1
    other=evaluate(name,p,1/t);symmetry=max(symmetry,abs(C*other-1))
   except (ValueError,ZeroDivisionError) as exc:
    r['invalid']+=1
    if r['first_failure'] is None:r['first_failure']={'p':p,'t':mp.nstr(t,12),'reason':str(exc)}
  es=[mp.mpf('1e-5')/p,mp.mpf('5e-6')/p]
  errs=[abs(logerror(name,p,e)) for e in es]
  r['local_order'][p]=mp.nstr(mp.log(errs[0]/errs[1])/mp.log(2),15)
  for exponent in [-100,-10,-1,1,10,100]:
   e=exponent*mp.log(10)/p
   for i in range(1000):
    try:en=logerror(name,p,e)
    except (ValueError,ZeroDivisionError):r['orbit_failures'].append([p,exponent,'invalid']);break
    if abs(en)<mp.mpf('1e-120'):r['max_orbit_steps']=max(r['max_orbit_steps'],i+1);break
    if not mp.isfinite(en):r['orbit_failures'].append([p,exponent,'nonfinite']);break
    e=en
   else:r['orbit_failures'].append([p,exponent,'iteration_cap'])
 r['reciprocity_max']=mp.nstr(symmetry,12);res[name]=r
 print(name,r['invalid'],r['noncontracting'],r['crossing'],r['first_failure'],flush=True)
(OUT/'benchmark_results.json').write_text(json.dumps({'precision_digits':mp.mp.dps,'p_grid':PS,'results':res},indent=2)+'\n')
# Plot the actual log-error, including gaps outside the radical domains.
try:
 import matplotlib;matplotlib.use('Agg')
 import matplotlib.pyplot as plt
 fig,ax=plt.subplots(figsize=(7,4.5));xs=[-4+8*i/400 for i in range(401)]
 for name in ['AD5','pade33','pade44','radical7','radical9']:
  ys=[]
  for x in xs:
   try:ys.append(float(logerror(name,3,mp.mpf(x)/3)))
   except ValueError:ys.append(float('nan'))
  ax.plot(xs,ys,label=name)
 ax.axhline(0,color='gray',lw=.5);ax.set(xlabel='log(t), p = 3',ylabel='next logarithmic error',title='Same scalar target, different orders and real domains');ax.legend();fig.tight_layout();fig.savefig(OUT/'figures/error_maps.svg');plt.close(fig)
 artifact=OUT/'figures/error_maps.svg'
 artifact.write_text('\n'.join(line.rstrip() for line in artifact.read_text().splitlines())+'\n')
except ImportError: print('Matplotlib unavailable; numerical report still written.')
