// Homogeneous incidence engine. Scalar formulas are used only as independent readout checks.
export const methods={AK:'Pandrosion AK',AD:'Pandrosion AD',projective:'AD projectif [2/1]',arc:'AD à arc décentré',halley:'Pinceaux · Halley',pade:'Pinceaux · Padé [2/2]',circle:'Cercle fixe · inverse [2/2]'};
export const orders={AK:2,AD:3,projective:4,arc:5,halley:3,pade:5,circle:5};
export function cross(a,b){const c=[a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0]],m=Math.max(...c.map(Math.abs));if(!c.every(Number.isFinite))throw Error('Données trop grandes pour les intersections du navigateur. Renormaliser.');if(m<1e-14)throw Error('Points confondus ou intersection non unique : changer de carte ou de départ.');return c.map(x=>x/m);}
export function affine(q){return Math.abs(q[2])<1e-11?null:[q[0]/q[2],q[1]/q[2]];}
export const point=(x,y)=>[x,y,1];
const hub=f=>[2*f,4*(f-1),f-1];
export function parameters(p,chart='compact'){
 if(chart==='uniform'){
  const q=p-3,D=625*q**5+10525*q**4+56797*q**3+88639*q*q+14758*q+664,K=625*q**5+1975*q**4+4147*q**3+2905*q*q+448*q+340;
  const A=(p+1)*(p+2),C=(p-1)*(p-2),E=288*p*(p-2)*(25*p*p-244)/D,u=5-4*A/(9*C),w=8*(5-2*p)/(9*(p-1)),j=-3*E*w/4;
  return {rho:1/3,h:2+2*j-E*u/2,j,zx:2-E,zy:384*p*(25*p**3-50*p*p-415*p+974)/D,k:K/D};
 }
 if(p===4)return {rho:1/3,h:13502/7167,j:3328/2389,zx:-214/2389,zy:2432/2389,k:145/2389};
 const D=p**3+12*p*p+39*p-26;
 return {rho:.5,h:2-72*p*(p+4)/((p-1)*D),j:24*p*(p-2)*(p+4)/((p-1)*D),zx:2-24*p*(p+4)*(p-2)/((p-4)*D),zy:24*p*(p*p+2*p-26)/((p-4)*D),k:(p-2)*(p*p-4*p+13)/D};
}
export function correction(mode,p,t){
 if(mode==='AK')return p/(p-1+t);
 if(mode==='AD'||mode==='halley')return (p+1+(p-1)*t)/(p-1+(p+1)*t);
 if(mode==='projective')return 2*p*((2*p-1)*t+p+1)/((p+1)*t*t+2*(2*p-1)*(p+1)*t+(2*p-1)*(p-1));
 if(mode==='arc'){const g=(p-1)*Math.sqrt(((p-2)*(t*t+1)+(10*p+4)*t)/(12*p));return (1+g)/(t+g);}
 if(mode==='pade'){const a=(p-1)*(2*p-1),b=8*p*p-2,c=(p+1)*(2*p+1);return (a*t*t+b*t+c)/(c*t*t+b*t+a);}
 const A=(p+1)*(p+2),B=p*p-4,C=(p-1)*(p-2),disc=(42*p*p-24)*t-3*B*(1+t*t);
 if(disc<=0)throw Error('Le résidu est hors du domaine réel transverse du cercle. Choisir un départ plus proche.');
 return t<=1?(A-t*C)/(B*(1-t)+Math.sqrt(disc)):(Math.sqrt(disc)-B*(1-t))/(t*A-C);
}
export function construct(mode,p,X,s,chart='compact'){
 if(!methods[mode]||!Number.isInteger(p)||p<3||p>32||!(X>0&&s>0)||!Number.isFinite(X+s))throw Error('Choisir un entier 3 ≤ p ≤ 32 et X, s strictement positifs.');
 const t=X*s**p,expected=s*correction(mode,p,t);
 if(!(t>0&&expected>0)||!Number.isFinite(t+expected))throw Error('Les données dépassent la précision du navigateur.');
 const points={},birth={},ops=[],circles=[],fixed=[],counts={J:0,P:0,C:0},warnings=[];
 const add=(name,q,at=ops.length)=>{points[name]=q;birth[name]=at;return name;};
 for(const [name,xy]of Object.entries({O:[0,4],A:[2,4],B:[2,0],C:[0,0],P:[2,4*(1-s)]}))add(name,point(...xy),0);
 const top=[0,1,-4],left=[1,0,0],right=[1,0,-2],diagonal=cross(points.O,points.B);
 fixed.push({line:diagonal,label:'OB'});
 const op=(label,kind,line,names=[])=>{counts[kind]++;ops.push({label,kind,line,names});for(const n of names)birth[n]=ops.length;};
 const meet=(a,b,rail,name,label)=>{const l=cross(points[a],points[b]);add(name,cross(l,rail),ops.length+1);op(label||`${a}${b} → ${name}`,'J',l,[name]);return name;};
 const parallel=(l,q)=>[l[0]*q[2],l[1]*q[2],-l[0]*q[0]-l[1]*q[1]];
 if(['AK','AD','projective','arc'].includes(mode)){
  add('M',point(0,4*(1-1/X)),0);
  let horizontal=[0,1,-4*(1-s)];add('L1',cross(horizontal,left),1);add('B1',cross(horizontal,diagonal),1);op('Horizontale par P : L₁ et B₁','P',horizontal,['L1','B1']);
  const red=cross(points.L1,points.B);op('Joindre L₁ à B','J',red);let prev='B1';
  for(let i=2;i<=p;i++){
   const l=parallel(red,points[prev]),li='L'+i,bi='B'+i;
   add(li,cross(l,left),ops.length+1);op(`Parallèle par ${prev} → ${li}`,'P',l,[li]);
   horizontal=parallel([0,1,0],points[li]);add(bi,cross(horizontal,diagonal),ops.length+1);let names=[bi];
   if(i===p){add('E',cross(horizontal,right),ops.length+1);names.push('E');}
   op(`Horizontale par ${li}`,'P',horizontal,names);prev=bi;
  }
  let support;
  if(mode==='AK'){add('K',point(2*(1-X/p),0),0);support=cross(points.A,points.K);fixed.push({line:support,label:'AK'});}
  if(mode==='AD'||mode==='arc'){
   let F,radius,dx;
   if(mode==='AD'){F=point(2-4/(p-1),4-4*(p+1)/(X*(p-1)));radius=4*s**p;dx=F[0];}
   else{const beta=(p-1)*Math.sqrt((p-2)/(12*p)),alpha=(5*p+2)/(p-2),d=2/beta,delta=4/X*Math.sqrt(alpha*alpha-1);F=point(2-d+delta,4-4/(X*beta));const G=point(2,4+4*alpha/X);add('G',G,0);radius=Math.hypot(...affine(points.E).map((x,i)=>x-G[i]));dx=2-d;}
   add('F',F,0);fixed.push({line:[1,0,-dx],label:'Verticale de D'});
   const height=Math.sqrt(Math.max(0,radius*radius-(dx-F[0])**2));add('D',point(dx,F[1]-height),ops.length+1);
   circles.push({center:affine(F),radius,stage:ops.length+1,label:mode==='AD'?'Arc centré':'Arc décentré'});op('Tracer l’arc et choisir D en bas','C',null,['D']);
   support=cross(points.A,points.D);op('Joindre A à D','J',support);
  }
  if(mode==='projective'){
   const Z=point(2*(1+(5*p-1)/(2*p*(2*p-1))),4*(1+(p+1)/((2*p-1)*X))),ell=[0,1,-4*(1+(5*p-1)/((p+1)*X))];add('Z',Z,0);fixed.push({line:ell,label:'ℓ'});
   meet('Z','E',ell,'D','ZE coupe ℓ en D');support=cross(points.A,points.D);op('Joindre A à D','J',support);
  }
  const green=cross(points.M,points.E);op('Joindre M à E','J',green);
  const report=parallel(green,points.P);add('T',cross(report,support),ops.length+1);op('Parallèle à ME par P → T','P',report,['T']);
  const finish=parallel([0,1,0],points.T);add('Pnext',cross(finish,right),ops.length+1);op('Horizontale par T → P⁺','P',finish,['Pnext']);
 }else{
  meet('C','P',top,'V','CP donne le centre V');let curr='P',par;
  if(mode==='circle')par=parameters(p,chart);
  for(let i=1;i<p;i++){
   const factor=mode==='circle'?(i===1?par.rho:i===p-1?par.k*X*2**(p-3)/par.rho:.5):.5;
   const h='U'+i;add(h,hub(factor),0);const li=meet(h,curr,left,'L'+i);
   curr=meet('V',li,right,i===p-1?'Q':'Q'+i);
  }
  if(mode==='circle'){
   const {rho,h,j,zx,zy}=par;add('Z',point(zx,zy),0);add('MΓ',point(h,j),0);const radius=Math.hypot(2-h,j);circles.push({center:[h,j],radius,stage:0,label:'Γ fixe'});
   const line=cross(points.Z,points.Q),[a,b,c]=line,norm=Math.hypot(a,b),dist=(a*h+b*j+c)/norm,d2=radius*radius-dist*dist;
   if(d2<=1e-13)throw Error('Tangence ou absence de traversée : sortir de cette configuration.');
   const foot=[h-dist*a/norm,j-dist*b/norm],offset=[-b*Math.sqrt(d2)/norm,a*Math.sqrt(d2)/norm];
   const candidates=[-1,1].map(sign=>{const xy=foot.map((v,i)=>v+sign*offset[i]),dx=xy[0]-2,dy=xy[1],den=4*dx+2*dy,v=rho*4*dx/den;return {xy,v,d:(p*p-4)*(v*v+1)-2*(p*p+2)*v};});
   const good=candidates.filter(c=>Number.isFinite(c.v)&&c.d<0);
   if(good.length!==1)throw Error('Branche non identifiable ou G=B : changer de préparation.');
   add('G',point(...good[0].xy),ops.length+1);add('Gother',point(...candidates.find(c=>c!==good[0]).xy),ops.length+1);op('ZQ traverse Γ : choisir l’arc central','J',line,['G','Gother']);
   meet('B','G',top,'U','BG → centre de lecture U');meet('U','L1',right,'Pnext','UL₁ → P⁺');
  }else{
   const pairs=[];
   if(mode==='halley')pairs.push([(p-1)/(4*p),(p+1)/(4*p),(p+1)/(4*p),(p-1)/(4*p)]);
   else{const a=(p-1)*(2*p-1),b=8*p*p-2,d=Math.sqrt(12*p*p*(4*p*p-1));for(const r of [(b+d)/(2*a),(b-d)/(2*a)])pairs.push([1/(2*(1+r)),r/(2*(1+r)),r/(2*(1+r)),1/(2*(1+r))]);}
   let current='P';pairs.forEach(([af,bf,ag,bg],i)=>{
    for(const [tag,alpha,beta]of [['f',af,bf],['g',ag,bg]]){const z='Z'+tag+i;add(z,point(-2*alpha/(1-alpha),4*(1-beta/(X*2**(p-1)*(1-alpha)))),0);meet(z,'Q',top,tag+i,`Projecteur ${tag} → centre ${tag}`);}
    const l=meet(current,'f'+i,left,'R'+i,'Projection sur la rive gauche');current=meet(l,'g'+i,right,i===pairs.length-1?'Pnext':'Pmid','Projection sur la rive droite');
   });
  }
 }
 const end=affine(points.Pnext);if(!end)throw Error('Lecture finale à l’infini.');const value=1-end[1]/4,discrepancy=Math.abs(value-expected)/Math.max(1,Math.abs(expected));
 if(!(value>0)||!Number.isFinite(value+discrepancy)||discrepancy>2e-7)throw Error('Configuration trop mal conditionnée pour la précision du navigateur. Renormaliser ou changer de carte.');
 const infinite=Object.entries(points).filter(([,v])=>!affine(v)).map(([n])=>n);
 if(infinite.length)warnings.push('Continuation projective : '+infinite.join(', ')+' à l’infini. Le coût du protocole fini ne s’applique pas littéralement.');
 return {mode,p,X,s,t,chart,points,birth,ops,circles,fixed,counts,value,expected,discrepancy,warnings,root:X**(-1/p)};
}
export function renormalize(p,X,s,chart='compact'){if(!Number.isInteger(p)||p<3||p>32||!Number.isFinite(X+s)||!(X>0&&s>0))throw Error('Paramètres invalides.');let n=Math.ceil(1-Math.log2(X)/p),c=2**n,scaled=X*c**p;if(!Number.isFinite(scaled)||scaled===0)scaled=Math.exp(Math.log(X)+p*n*Math.LN2);const par=parameters(p,chart),sigma=par.k*scaled*2**(p-3)/par.rho;if(Math.abs(sigma-1)<1e-12){c*=2;scaled*=2**p;}return {X:scaled,s:s/c,c};}
export function stereo(q){const [x,y,w]=q,u=x-w,v=y-2*w,z=2*w,n=u*u+v*v+z*z;return [2*u*z/n,2*v*z/n,(u*u+v*v-z*z)/n];}
