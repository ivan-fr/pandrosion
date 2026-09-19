"""Exact, bounded ansatz search; no floating-point fitting. Run from repository root."""
from pathlib import Path
import json
import sympy as S
OUT=Path(__file__).resolve().parent
p,z=S.symbols('p z',positive=True)
def factor(x): return S.factor(x)
# w=tanh(atanh(z)/p) solves p(1-z^2)w'=1-w^2, w(0)=0.
w={0:S.S.Zero}
for n in range(12):
    w[n+1]=factor(((1 if n==0 else 0)-sum(w[i]*w[n-i] for i in range(n+1)))/p/(n+1)+S.Rational(n-1,n+1)*w.get(n-1,0))
D=[p]
for n in range(1,6):D.append(factor(-p*sum(w[2*i+1]*D[n-i] for i in range(1,n+1))))
# AD5 bounded Cayley core and arbitrary nonzero homogeneous scaling.
t,h,k,r=S.symbols('t h k r', nonzero=True)
g2=(p-1)**2*((p-2)*(t*t+1)+(10*p+4)*t)/(12*p)
assert factor(g2/(1+t)**2-(p-1)**2/4*(1-2*(p+1)/(3*p)*((t-1)/(t+1))**2))==0
assert factor(h*k/(h*k-h*r)-k/(k-r))==0
# D7=a+c sqrt(1+d z^2): the first three even coefficients determine a,c,d uniquely.
d7=factor(-4*D[2]/D[1]);c7=factor(2*D[1]/d7);a7=factor(p-c7)
assert factor(c7*d7/2-D[1])==0 and factor(-c7*d7**2/8-D[2])==0
err7=factor(c7*d7**3/16-D[3])
# D9=a+b z^2+c sqrt(1+d z^2): one additional rational stage.
d9=factor(-2*D[3]/D[2]);c9=factor(-8*D[2]/d9**2);a9=factor(p-c9);b9=factor(D[1]-c9*d9/2)
assert factor(c9*d9/2+b9-D[1])==0 and factor(-c9*d9**2/8-D[2])==0
assert factor(c9*d9**3/16-D[3])==0
err9=factor(-5*c9*d9**4/128-D[4])
assert factor(d7+1+(p-2)*(p+2)/(15*p**2))==0
assert factor(d9+1+(p-2)*(p+2)/(21*p**2))==0
# The nonzero first defects prove exact orders 7 and 9 in these analytic families.
results={'target_D_even_coefficients':list(map(str,D)),
 'radical7':dict(a=str(a7),b='0',c=str(c7),d=str(d7),D_defect=str(err7),log_error_coefficient=str(factor(err7*p**5/64)),max_order_in_this_ansatz=7),
 'radical9':dict(a=str(a9),b=str(b9),c=str(c9),d=str(d9),D_defect=str(err9),log_error_coefficient=str(factor(err9*p**7/256)),max_order_in_this_ansatz=9),
 'two_radicals':{},'rational_pade':{}}
# Two shared square roots: moment recurrence recovers constructible nodes for fixed p.
for k in [3,4,5,7]:
 m=[None]+[factor(D[i]/S.binomial(S.Rational(1,2),i)).subs(p,k) for i in range(1,5)]
 U,V=S.symbols('U V');sol=S.solve([m[3]-U*m[2]+V*m[1],m[4]-U*m[3]+V*m[2]],[U,V])
 disc=factor(sol[U]**2-4*sol[V]);d=(sol[U]-S.sqrt(disc))/2;f=(sol[U]+S.sqrt(disc))/2
 c=S.simplify((m[2]-f*m[1])/(d*(d-f)));e=S.simplify((m[2]-d*m[1])/(f*(f-d)));a=k-c-e
 for i in range(1,5):assert S.simplify(c*d**i+e*f**i-m[i])==0
 defect=S.simplify(S.binomial(S.Rational(1,2),5)*(c*d**5+e*f**5)-D[5].subs(p,k))
 assert defect!=0
 results['two_radicals'][k]={key:str(val) for key,val in dict(a=a,c=c,e=e,d=d,f=f,defect=defect).items()}
# Nonsymmetric and reciprocal classical rational controls: exact Padé around t=1.
def pade(k,L,M):
 coeff=[S.binomial(-S.Rational(1,k),j) for j in range(L+M+2)]
 qs=S.symbols('q1:'+str(M+1));Q=[S.S.One,*qs]
 sol=S.solve([sum(Q[i]*coeff[n-i] for i in range(M+1)) for n in range(L+1,L+M+1)],qs)
 Q=[q.subs(sol) for q in Q];P=[sum(Q[i]*coeff[n-i] for i in range(min(n,M)+1)) for n in range(L+1)]
 defect=factor(sum(Q[i]*coeff[L+M+1-i] for i in range(M+1)))
 assert defect!=0
 return P,Q,defect
for k in [3,4,5,7]:
 for L,M in [(3,2),(3,3),(4,3),(4,4)]:
  P,Q,defect=pade(k,L,M)
  results['rational_pade'][f'{k}:{L}/{M}']={'P':list(map(str,P)),'Q':list(map(str,Q)),'order':L+M+1,'defect':str(defect)}
(OUT/'symbolic_results.json').write_text(json.dumps(results,indent=2)+'\n')
print('PASS: exact orders 6/7/8/9 rational controls, radical orders 7/9, two-radical order 11 for p=3,4,5,7; strict real-domain obstructions.')
