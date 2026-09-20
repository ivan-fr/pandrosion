"""V24: independent checks of the uniform written proof and exact formula comparisons.

These finite checks are not a substitute for the convexity proof in main.tex.
No inherited Lean theorem is extended by this script.
"""
from pathlib import Path
import json
import sympy as sp
from mpmath import mp

p, v, x, t, g = sp.symbols('p v x t g', real=True)
A=(p+1)*(p+2); B=p*p-4; C=(p-1)*(p-2)
N=C*v*v-2*B*v+A; D=A*v*v-2*B*v+C
Y=3*p*x/(3+(p*p-1)*x*x)
checks={}
def zero(name, expression):
    checks[name] = sp.cancel(expression) == 0
    assert checks[name], name

zero('cayley_model', (N/D).subs(v,(1+x)/(1-x))-(1-Y)/(1+Y))
zero('branch_derivative', sp.diff(Y,x)-3*p*(3-(p*p-1)*x*x)/(3+(p*p-1)*x*x)**2)
zero('convexity_second_derivative', sp.diff(sp.atanh(x),x,2)-2*x/(1-x*x)**2)
zero('defect_derivative_numerator', p*N*D+v*(sp.diff(N,v)*D-N*sp.diff(D,v))-p*A*C*(v-1)**4)
zero('circle_discriminant', (B*(t-1))**2-(C-t*A)*(A-t*C)-((42*p*p-24)*t-3*(p*p-4)*(1+t*t)))
S=(p-2)*(t*t+1)+(10*p+4)*t
V=(1+g)/(t+g)
implicit=(p-1)**2*S*(v-1)**2-12*p*(t*v-1)**2
zero('arc_elimination', implicit.subs(v,V)-(t-1)**2*((p-1)**2*S-12*p*g*g)/(t+g)**2)

# Truncated formal power series at t=1, with exact rational functions of p.
# Build the radical and quotient by recurrences, independently of log-derivative certificates.
def convolution(a,b,n):
    return [sp.factor(sum(a[j]*b[k-j] for j in range(k+1))) for k in range(n+1)]
def quotient(a,b,n):
    q=[]
    for k in range(n+1):
        q.append(sp.factor((a[k]-sum(b[j]*q[k-j] for j in range(1,k+1)))/b[0]))
    return q
n=5
truth=[sp.factor(sp.prod(-1/p-j for j in range(k))/sp.factorial(k)) for k in range(n+1)]
q=[sp.Integer(1)]
radicand=[sp.Integer(1),sp.Integer(1),(p-2)/(12*p),0,0,0]
for k in range(1,n+1):
    q.append(sp.factor((radicand[k]-sum(q[j]*q[k-j] for j in range(1,k)))/2))
arc_num=[p]+[(p-1)*q[k] for k in range(1,n+1)]
arc_den=arc_num.copy(); arc_den[1]+=1
arc=quotient(arc_num,arc_den,n)
a5=(p-1)*(2*p-1); b5=8*p*p-2; c5=(p+1)*(2*p+1)
rat=quotient([a5+b5+c5,2*a5+b5,a5,0,0,0],[a5+b5+c5,2*c5+b5,c5,0,0,0],n)
# Inverse quadratic solved coefficient-by-coefficient through its nonzero derivative -12p.
inverse=[sp.Integer(1)]
for k in range(1,n+1):
    trial=inverse+[sp.Integer(0)]
    sq=convolution(trial,trial,k)
    # (C-(1+h)A)v² + 2B h v + A-(1+h)C
    residual=(C-A)*sq[k]-A*sq[k-1]+2*B*trial[k-1]-(C if k==1 else 0)
    inverse.append(sp.factor(residual/(12*p)))
coeffs={
    'circle':-(p*p-1)*(p*p-4)/720,
    'arc':(p-2)*(p*p-1)*(3*p+1)/1440,
    'rational':(p*p-1)*(4*p*p-1)/720,
}
for name, seq in [('circle',inverse),('arc',arc),('rational',rat)]:
    for k in range(5): zero(f'{name}_contact_{k}',seq[k]-truth[k])
    zero(f'{name}_log_error_coefficient',p**5*(seq[5]-truth[5])-coeffs[name])
zero('arc_vs_rational_nonidentity',coeffs['arc']-coeffs['rational']+p*(p+1)*(p*p-1)/288)

# Off-integer degrees, p->2+, large p, endpoints and severe root cancellation.
# Evaluate log errors with original N,D, separately from transformed expressions.
mp.dps=400
parameters=['2.000000000001','2.001','2.1','2.5','2.999','3','3.141592653589793','4','17','100','1000000','1e20']
fractions=['1e-30','1e-12','1e-5','.01','.25','.5','.9','.999','0.999999999999999999999999999999','1']
cases=0; max_ratio=mp.mpf(0); endpoint_rows=[]
for pp_str in parameters:
    pp=mp.mpf(pp_str); xx_star=mp.sqrt(3/(pp*pp-1))
    aa=(pp+1)*(pp+2); bb=pp*pp-4; cc=(pp-1)*(pp-2)
    for fraction in fractions:
        xx=xx_star*mp.mpf(fraction)
        for sign in [-1,1]:
            xx_signed=sign*xx; vv=(1+xx_signed)/(1-xx_signed)
            tt=(cc*vv*vv-2*bb*vv+aa)/(aa*vv*vv-2*bb*vv+cc)
            yy=3*pp*xx_signed/(3+(pp*pp-1)*xx_signed*xx_signed)
            assert abs(mp.log(tt)+2*mp.atanh(yy)) < mp.mpf('1e-170')
            e=mp.log(tt)/pp; enew=e+mp.log(vv)
            assert e*enew < 0, (pp_str,fraction,sign,'alternation')
            assert abs(enew)<abs(e), (pp_str,fraction,sign,'contraction')
            ratio=abs(enew/e); max_ratio=max(max_ratio,ratio); cases+=1
        if fraction=='1':
            endpoint_rows.append({'p':pp_str,'margin':mp.nstr(4*mp.atanh(pp*xx/2)-2*pp*mp.atanh(xx),30)})

# Stable independent scalar orbits in log residual coordinates. Circle inversion
# uses the original quadratic formula, while the monotone arc uses its positive radical.
trajectories=[]
for pp_str in ['2.001','2.5','3','3.141592653589793','4','17','100','1000000']:
    pp=mp.mpf(pp_str); aa=(pp+1)*(pp+2); bb=pp*pp-4; cc=(pp-1)*(pp-2)
    tau=(7*pp*pp-4+4*pp*mp.sqrt(3*(pp*pp-1)))/(pp*pp-4)
    for f in ['-.999999','.001','.5','.999999']:
        z=mp.mpf(f)*mp.log(tau); steps=0
        while abs(z)>mp.mpf('1e-60'):
            tt=mp.exp(z); delta=(42*pp*pp-24)*tt-3*(pp*pp-4)*(1+tt*tt)
            vv=(aa-tt*cc)/(bb*(1-tt)+mp.sqrt(delta)) if tt<=1 else (mp.sqrt(delta)-bb*(1-tt))/(tt*aa-cc)
            zn=z+pp*mp.log(vv)
            assert z*zn<0 and abs(zn)<abs(z)
            z=zn; steps+=1; assert steps<=60
        trajectories.append({'map':'circle','p':pp_str,'start_fraction':f,'steps':steps})
    for z0 in ['-100','-1','.00001','1','100']:
        z=mp.mpf(z0); steps=0
        while abs(z)>mp.mpf('1e-60'):
            tt=mp.exp(z); qq=mp.sqrt(((pp-2)*(tt*tt+1)+(10*pp+4)*tt)/(12*pp))
            vv=(1+(pp-1)*qq)/(tt+(pp-1)*qq); zn=z+pp*mp.log(vv)
            assert z*zn>0 and abs(zn)<abs(z)
            z=zn; steps+=1; assert steps<=200
        trajectories.append({'map':'arc','p':pp_str,'initial_log_residual':z0,'steps':steps})
report={'scope':'Symbolic identities and finite checks of written V24 results; not a new Lean theorem',
        'symbolic_checks':checks,'precision_decimal_digits':mp.dps,'contraction_cases':cases,
        'largest_sampled_ratio':mp.nstr(max_ratio,30),'endpoint_margins':endpoint_rows,
        'trajectories':trajectories,'max_trajectory_steps':max(r['steps'] for r in trajectories),
        'coefficients':{k:str(sp.factor(vv)) for k,vv in coeffs.items()}}
Path(__file__).with_name('checks.json').write_text(json.dumps(report,indent=2)+'\n')
print(f'PASS: {len(checks)} symbolic checks, {cases} branch/endpoint cases and {len(trajectories)} scalar trajectories at {mp.dps} digits')
