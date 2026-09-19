"""Independent high-precision scalar and incidence falsification."""
import json
from pathlib import Path
import mpmath as m
m.mp.dps=180
OUT=Path(__file__).parent
PS=[3,4,5,7,10,32,100,1000,1000000]
def correction(p,t):
 z=(t-1)/(t+1);a=(3*p*p-2)/(5*p*p);b=(4*p*p-1)/(15*p*p)
 D=p*(1-a*z*z)/(1-b*z*z)
 return (D-z)/(D+z)
def cross(a,b):return [a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0]]
def point(x,y):return [m.mpf(x),m.mpf(y),m.mpf(1)]
def meet(a,b,rail):
 q=cross(cross(a,b),rail)
 if not q[2]:raise ArithmeticError('intersection_at_infinity')
 return [v/q[2] for v in q]
def geometry(p,t,s,X):
 L=[1,0,0];R=[1,0,-1];H=[0,1,-1]
 def mobius(u,n1,n0,d1,d0):
  a=n1/d1;b=2*(a*d0-n0)/(d1*(1-a));beta=b+2*d0/d1
  Y=meet(u,point(-1,1+beta),R)
  return meet(Y,point(a,1-b),H)
 top=meet(point(1,1-t/X),point(-2,1+2/X),H)
 Z=meet(top,point(4,-2),L)
 center=meet(Z,point(1,-1),H);twice=meet(Z,point(-1,1),R)
 square=meet(twice,center,L)
 a=(3*p*p-2)/(5*p*p);b=(4*p*p-1)/(15*p*p)
 V=mobius(square,-b,m.mpf(1),2*p*a-b,1-2*p)
 ratio=meet(twice,V,L)
 Vc=mobius(ratio,m.mpf(8),m.mpf(8),m.mpf(9),m.mpf(7))
 eight=meet(point(1,1-s),point(m.mpf(8)/7,1),L)
 return 1-meet(eight,Vc,R)[1]
res=dict(digits=180,scalar_samples=0,scalar_failures=[],geometry_samples=0,max_geometry_error='0',orders={},orbits=[])
worst=m.mpf(0)
for k in PS:
 p=m.mpf(k)
 ts=[m.power(10,j) for j in range(-100,101)]+[m.exp(m.mpf(j)/100) for j in range(-200,201) if j]
 for t in ts:
  if t==1:continue
  C=correction(p,t);e=m.log(t)/p;en=e+m.log(C)
  res['scalar_samples']+=1
  if C<=0 or not (0<en/e<1):res['scalar_failures'].append([k,m.nstr(t,10)])
 es=[m.mpf('1e-5')/p,m.mpf('5e-6')/p];errs=[abs(e+m.log(correction(p,m.exp(p*e)))) for e in es]
 res['orders'][k]=m.nstr(m.log(errs[0]/errs[1])/m.log(2),15)
 for j in [-100,-10,-1,1,10,100]:
  e=j*m.log(10)/p
  for i in range(500):
   e=e+m.log(correction(p,m.exp(p*e)))
   if abs(e)<m.mpf('1e-120'):break
  else:raise AssertionError('orbit did not converge within cap')
  res['orbits'].append(dict(p=k,initial_log10_t=j,steps=i+1))
 if k<=1000:
  for X in map(m.mpf,['.25','2','4']):
   for j in range(-60,61,3):
    t=m.power(10,j);s=m.exp((m.log(t)-m.log(X))/p)
    got=geometry(p,t,s,X);want=s*correction(p,t)
    worst=max(worst,abs(got-want)/max(1,abs(want)));res['geometry_samples']+=1
assert not res['scalar_failures']
assert worst<m.mpf('1e-110')
res['max_geometry_error']=m.nstr(worst,12)
(OUT/'benchmark_results.json').write_text(json.dumps(res,indent=2)+'\n')
print({k:v for k,v in res.items() if k not in ['orders','orbits']})
print('All 54 extreme-start orbits converged; maximum steps:',max(x['steps'] for x in res['orbits']))
def ad5(p,t):
 g=(p-1)*m.sqrt(((p-2)*(t*t+1)+(10*p+4)*t)/(12*p))
 return (1+g)/(t+g)
res['reference_costs']=[]
for digits in [6,12,30,60,120]:
 row={'digits':digits}
 for name,f in [('AD5',ad5),('global7',correction)]:
  p=m.mpf(3);X=m.mpf(2);s=m.mpf(3)/4;a=X**(-1/p)
  for n in range(1,10):
   s=s*f(p,X*s**3)
   if abs(s/a-1)<m.power(10,-digits):break
  row[name]={'iterations':n,'native_expanded_traces':39+34*(n-1) if name=='AD5' else 38*n,'binary_expanded_traces':30*n if name=='AD5' else 29*n}
 res['reference_costs'].append(row)
(OUT/'benchmark_results.json').write_text(json.dumps(res,indent=2)+'\n')
print(res['reference_costs'])
