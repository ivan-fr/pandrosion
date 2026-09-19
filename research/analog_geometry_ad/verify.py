"""Exact identities and finite checks for a compact AD correction geometry.
No circuit simulation, power-stage change, or formal Lean theorem is claimed.
"""
from pathlib import Path
import json
import sympy as sp
import mpmath as mp
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

HERE=Path(__file__).resolve().parent
p,q,w=sp.symbols('p q w',positive=True)
a=(p+1)/(2*p);b=1+q/p
step=-w*b/(1+a*w)
old=2*(1+q/p)*(1-(1+w))/(1+(1+w)+w/p)
assert sp.cancel(step-old)==0
assert sp.cancel(step+w*(b+a*step))==0
# The denominator and the determinant are identical up to the factor two.
assert sp.cancel(2*(1+a*w)-(2+w+w/p))==0
A,W,B=sp.symbols('A W B',real=True)
assert sp.expand((1+A*W)**2-(1+W**2)-W*(2*A-(1-A**2)*W))==0
expr=-W*B/(1+A*W)
assert sp.simplify(sp.diff(expr,W)+B/(1+A*W)**2)==0
assert sp.simplify(sp.diff(expr,B)+W/(1+A*W))==0
assert sp.simplify(sp.diff(expr,A)-B*W**2/(1+A*W)**2)==0

mp.mp.dps=120
rows=[];maxerr=mp.mpf(0);minsin=mp.mpf(1);maxfb=mp.mpf(0)
for p in [3,4,5,7,16,32,1000,1000000]:
 for Ystr in ['1','1.01','1.25','1.5','2']:
  Y=mp.mpf(Ystr);u0=mp.power(Y,-mp.mpf(1)/p);qroot=p*(u0-1)
  for fracstr in ['0','.25','.5','.75','1']:
   q=mp.mpf(fracstr)*qroot;u=1+q/p;t=Y*mp.power(u,p);w=t-1
   a=mp.mpf(p+1)/(2*p);b=1+q/p
   # Actual intersection of y=b+a*x and x+w*y=0.
   x,y=mp.lu_solve(mp.matrix([[-a,1],[1,w]]),mp.matrix([b,0]))
   refq=p*(u*(p+1+(p-1)*t)/(p-1+(p+1)*t)-1)
   err=abs(q+x-refq);maxerr=max(maxerr,err)
   tol=mp.mpf('1e-108')
   assert err<tol
   assert -tol<=w<=1+tol
   assert -mp.mpf(2)/3-tol<=x<=tol
   assert mp.mpf(3)/5*mp.power(2,-mp.mpf(1)/3)-tol<=y<=1+tol
   sine=(1+a*w)/mp.sqrt((1+a*a)*(1+w*w))
   assert sine>=3/mp.sqrt(13)-tol
   assert abs(a*w)<=mp.mpf(2)/3+tol
   # An inner algebraic fixed-point iteration, with q and w frozen.
   d=mp.mpf(0)
   for j in range(20):
    dn=-w*(b+a*d)
    assert abs(dn-x)<=mp.mpf(2)/3*abs(d-x)+tol
    d=dn
   minsin=min(minsin,sine);maxfb=max(maxfb,abs(a*w))
   rows.append({'p':p,'Y':Ystr,'fraction_to_root':fracstr,'x':mp.nstr(x,12),'y':mp.nstr(y,12)})
result={'scope':'Symbolic identities and finite ideal-geometry checks; not Lean or SPICE validation.',
 'decimal_digits':120,'cases':len(rows),'max_absolute_AD_disagreement':mp.nstr(maxerr,8),
 'minimum_sine_angle':mp.nstr(minsin,12),'max_frozen_feedback_factor':mp.nstr(maxfb,12),
 'theoretical_min_angle_degrees':float(mp.asin(3/mp.sqrt(13))*180/mp.pi),
 'rows':rows}
(HERE/'checks.json').write_text(json.dumps(result,indent=2)+'\n')

# Equal-scale figures: initial state, same prepared residual, very different degree.
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10})
fig,axs=plt.subplots(1,2,figsize=(10.4,5.4),layout='constrained')
for ax,p in zip(axs,[3,1000000]):
 a=(p+1)/(2*p);b=1.;w=1.;x=-w*b/(1+a*w);y=b/(1+a*w)
 xx=[-1.15,1.15]
 ax.plot(xx,[b+a*xx[0],b+a*xx[1]],color='#176B9B',lw=2,label='Fixed direction: y = b + ax')
 ax.plot([0,-w*1.65],[0,1.65],color='#BD5A20',lw=2,label='Residual line: x + wy = 0')
 ax.plot([0,x],[y,y],color='#A9B4BC',ls=':');ax.plot([x,x],[0,y],color='#218369',ls=':')
 for X,Y,label,off in [(0,0,'O',(6,-14)),(-w,1,'(-w, 1)',(5,8)),(0,b,'(0, b)',(6,6)),(x,y,'Intersection',(8,-15))]:
  ax.plot(X,Y,'o',ms=4,color='#253640');ax.annotate(label,(X,Y),xytext=off,textcoords='offset points',fontsize=9)
 ax.text(x,-.17,r'$\delta=q^+-q$',ha='center',color='#218369')
 ax.text(.08,.10,f'delta = {x:.6f}\na = {a:.6f}',fontsize=10)
 ax.axhline(0,lw=.7,color='#A9B4BC');ax.axvline(0,lw=.7,color='#A9B4BC')
 ax.set(xlim=(-1.2,1.1),ylim=(-.25,1.72),aspect='equal',title=f'p = {p:,}; Y = 2; q = 0')
 ax.grid(alpha=.12)
axs[0].legend(loc='lower center',bbox_to_anchor=(.5,-.25),fontsize=9,frameon=False)
fig.suptitle('Centered AD correction: a uniformly transverse intersection\nTwo lines once the input points are prepared; same exact order-three update',fontsize=13)
fig.savefig(HERE/'centered_ad_geometry.png',dpi=180,bbox_inches='tight')
fig.savefig(HERE/'centered_ad_geometry.svg',bbox_inches='tight')
svg=HERE/'centered_ad_geometry.svg'
svg.write_text('\n'.join(line.rstrip() for line in svg.read_text().splitlines())+'\n')
print('PASS:',len(rows),'ideal intersections at 120 digits; same AD map; coordinate, angle and frozen-feedback bounds')
print(json.dumps({k:v for k,v in result.items() if k!='rows'},indent=2))
