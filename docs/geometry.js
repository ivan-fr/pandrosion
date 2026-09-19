// Homogeneous incidence engine. Scalar formulas are used only as independent readout checks.
export const methods={AK:'Pandrosion AK',AD:'Pandrosion AD',projective:'Projective AD [2/1]',arc:'Decentered-arc AD',halley:'Pencils · Halley',pade:'Pencils · Padé [2/2]',circle:'Fixed circle · inverse [2/2]'};
export const orders={AK:2,AD:3,projective:4,arc:5,halley:3,pade:5,circle:5};
export const fastModes={AKfast:'AK',ADfast:'AD',projectiveFast:'projective',arcFast:'arc'};
export const dualModes={AKdual:'AK',ADdual:'AD',projectiveDual:'projective',arcDual:'arc'};
export const baseMode=mode=>fastModes[mode]||dualModes[mode]||mode;
for(const [fast,base] of Object.entries(fastModes)){methods[fast]=`Fast exponentiation + ${methods[base]}`;orders[fast]=orders[base];}
for(const [dual,base] of Object.entries(dualModes)){methods[dual]=`Fixed AK + ${base==='AK'?'Newton':base==='AD'?'Halley':base==='projective'?'[2/1]':'decentered-arc'} transport`;orders[dual]=orders[base];}
export function binaryCount(p){if(!Number.isSafeInteger(p)||p<1)throw Error('A positive integer exponent is required.');const bits=p.toString(2);return bits.length-1+[...bits].filter(x=>x==='1').length-1;}
export function cross(a,b){const c=[a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0]],m=Math.max(...c.map(Math.abs));if(!c.every(Number.isFinite))throw Error('Values are too large for browser intersection calculations. Renormalize.');if(m===0)throw Error('Coincident points or nonunique intersection: change the chart or starting point.');return c.map(x=>x/m);}
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
 mode=baseMode(mode);
 if(mode==='AK')return p/(p-1+t);
 if(mode==='AD'||mode==='halley')return (p+1+(p-1)*t)/(p-1+(p+1)*t);
 if(mode==='projective')return 2*p*((2*p-1)*t+p+1)/((p+1)*t*t+2*(2*p-1)*(p+1)*t+(2*p-1)*(p-1));
 if(mode==='arc'){const g=(p-1)*Math.sqrt(((p-2)*(t*t+1)+(10*p+4)*t)/(12*p));return (1+g)/(t+g);}
 if(mode==='pade'){const a=(p-1)*(2*p-1),b=8*p*p-2,c=(p+1)*(2*p+1);return (a*t*t+b*t+c)/(c*t*t+b*t+a);}
 const A=(p+1)*(p+2),B=p*p-4,C=(p-1)*(p-2),disc=(42*p*p-24)*t-3*B*(1+t*t);
 if(disc<=0)throw Error('The residual is outside the transverse real domain of the circle. Choose a closer starting point.');
 return t<=1?(A-t*C)/(B*(1-t)+Math.sqrt(disc)):(Math.sqrt(disc)-B*(1-t))/(t*A-C);
}
export function construct(mode,p,X,s,chart='compact',W=2,H=4,supportLevel=p,binaryPower=false){
 const requestedMode=mode,fast=!!fastModes[mode]||binaryPower,dual=!!dualModes[mode];mode=baseMode(mode);
 if(!methods[requestedMode]||!Number.isSafeInteger(p)||p<3||p>(fast?1_000_000:32)||!(X>0&&s>0)||!Number.isFinite(X+s))throw Error('Choose an integer p from 3 to 32 (1,000,000 in binary mode), with positive X and s.');
 if(!(W>0&&H>0&&Number.isFinite(W+H)))throw Error('Positive finite dimensions are required.');
 if(!['AK','AD','projective','arc'].includes(mode)&&(W!==2||H!==4))throw Error('These dimensions are available only for the four rectangle methods.');
 const logt=Math.log(X)+p*Math.log(s),t=Math.exp(logt),expected=s*correction(mode,p,t);
 if(!(t>0&&expected>0)||!Number.isFinite(t+expected))throw Error('The values exceed browser precision.');
 const points={},birth={},ops=[],circles=[],fixed=[],counts={J:0,P:0,C:0},warnings=[],transversality=[];
 const add=(name,q,at=ops.length)=>{points[name]=q;birth[name]=at;return name;};
 for(const [name,xy]of Object.entries({O:[0,H],A:[W,H],B:[W,0],C:[0,0],P:[W,H*(1-s)]}))add(name,point(...xy),0);
 const top=[0,1,-H],left=[1,0,0],right=[1,0,-W],diagonal=cross(points.O,points.B);
 fixed.push({line:diagonal,label:'OB'});
 const op=(label,kind,line,names=[])=>{counts[kind]++;ops.push({label,kind,line,names});for(const n of names)birth[n]=ops.length;};
 const meet=(a,b,rail,name,label)=>{const l=cross(points[a],points[b]);add(name,cross(l,rail),ops.length+1);op(label||`${a}${b} → ${name}`,'J',l,[name]);return name;};
 const parallel=(l,q)=>[l[0]*q[2],l[1]*q[2],-l[0]*q[0]-l[1]*q[1]];
 if(['AK','AD','projective','arc'].includes(mode)){
  add('M',point(0,H*(1-1/X)),0);
  if(fast){
   add('Ux',point(3*W,H),0);const transfer=cross(points.Ux,points.B);fixed.push({line:transfer,label:'U×B'});
   const copy=(r,name)=>{const l=parallel(transfer,points[r]);add(name,cross(l,top),ops.length+1);op(`Copy ${r} onto the upper rail → ${name}`,'P',l,[name]);return name;};
   let topAccumulator=copy('P','Xs'),accumulator='P',serial=0;
   const multiply=(a,b)=>{serial++;const l=cross(points.Ux,points[b]);op(`Multiplication ${serial}: join U× to ${b}`,'J',l);const m=parallel(l,points[a]),name='Rmul'+serial;add(name,cross(m,right),ops.length+1);op(`Parallel through ${a} → ${name}`,'P',m,[name]);return name;};
   const bits=p.toString(2).slice(1);
   for(let i=0;i<bits.length;i++){
    accumulator=multiply(topAccumulator,accumulator);
    if(bits[i]==='1')accumulator=multiply('Xs',accumulator);
    if(i<bits.length-1)topAccumulator=copy(accumulator,'Xmul'+serial);
   }
   add('E',points[accumulator]);
   const power=Math.exp(p*Math.log(s)),read=1-affine(points.E)[1]/H;
   if(!(power>0)||!Number.isFinite(power)||Math.abs(read/power-1)>2e-7)throw Error('Ill-conditioned geometric power: renormalize.');
  }else{
  let horizontal=[0,1,-H*(1-s)];add('L1',cross(horizontal,left),1);add('B1',cross(horizontal,diagonal),1);op('Horizontal through P: L₁ and B₁','P',horizontal,['L1','B1']);
  const red=cross(points.L1,points.B);op('Join L₁ to B','J',red);let prev='B1';
  for(let i=2;i<=p;i++){
   const l=parallel(red,points[prev]),li='L'+i,bi='B'+i;
   add(li,cross(l,left),ops.length+1);op(`Parallel through ${prev} → ${li}`,'P',l,[li]);
   horizontal=parallel([0,1,0],points[li]);add(bi,cross(horizontal,diagonal),ops.length+1);let names=[bi];
   if(i===p){add('E',cross(horizontal,right),ops.length+1);names.push('E');}
   op(`Horizontal through ${li}`,'P',horizontal,names);prev=bi;
  }
  }
  let support,transportName='E';
  if(dual){
   if(!(supportLevel>0&&Number.isFinite(supportLevel)))throw Error('A positive finite support level is required.');
   // Reuse the last horizontal of the power chain: it already passes through E.
   const ey=affine(points.E)[1],my=affine(points.M)[1],eh=[0,1,-ey],mh=[0,1,-my];
   if(fast&&(mode!=='AK'||supportLevel!==p))op('Horizontal through E for the transport readout','P',eh);
   add('K',point(W*(1-X/supportLevel),0),0);support=cross(points.A,points.K);fixed.push({line:support,label:'Fixed AK'});
   if(mode==='AK'&&supportLevel!==p){
    const rail=[1,0,-W*p/supportLevel];fixed.push({line:rail,label:'Constant transport rail'});
    add('R',cross(eh,rail));ops.at(-1).names.push('R');transportName='R';
   }else if(mode==='AD'){
    // On this fixed oblique rail, x/W = (p+1+(p-1)t)/(2p).
    const rail=[2*supportLevel/W,(p-1)*X/H,-(p+1+(p-1)*X)];
    fixed.push({line:rail,label:'Halley transport rail'});
    add('R',cross(eh,rail));ops.at(-1).names.push('R');transportName='R';
   }else if(mode==='projective'){
    const pv=p+1,u=2*p-1,t0=(supportLevel*(5*p-1)-2*p*pv)/(2*p*u-supportLevel*pv);
    if(!Number.isFinite(t0))throw Error('This support level needs a different projective chart.');
    const rail=[0,1,-H*(1-t0/X)];
    add('Zr',point(2*p*W*u/(supportLevel*pv),H+H*(5*p-1)/(X*pv)),0);
    fixed.push({line:rail,label:'Projection rail'});
    meet('Zr','E',rail,'Qr','ZrE meets the fixed projection rail at Qr');
    const v=parallel([1,0,0],points.Qr);add('R',cross(v,eh),ops.length+1);
    op('Vertical through Qr meets the last chain horizontal at R','P',v,['R']);transportName='R';
   }else if(mode==='arc'){
    const beta=(p-1)*Math.sqrt((p-2)/(12*p)),alpha=(5*p+2)/(p-2),lambda=W*X*beta/(supportLevel*H);
    const gy=H+H*alpha/X,delta=W*beta/supportLevel*Math.sqrt(alpha*alpha-1);
    add('Gr',point(W,gy),0);add('Gscale',point(0,gy),0);
    add('Fr',point(W/supportLevel,my+delta),0);fixed.push({line:mh,label:'Horizontal through M'});
    let radius;
    if(lambda===1){radius=Math.hypot(...affine(points.E).map((v,i)=>v-affine(points.Gr)[i]));}
    else{
     // A fixed projective center scales EG by lambda onto the left vertical.
     add('Zscale',[W*lambda,(lambda-1)*gy,lambda-1],0);
     meet('Zscale','E',left,'Escaled','ZscaleE transfers the scaled radius to Escaled');
     radius=Math.hypot(...affine(points.Escaled).map((v,i)=>v-affine(points.Gscale)[i]));
    }
    const gap=radius-delta;if(!(gap>0)||!Number.isFinite(radius))throw Error('Dual arc is tangent or numerically unresolved. Change the starting point or rectangle.');
    transversality.push(gap/radius);
    const dx=Math.sqrt(gap)*Math.sqrt(radius+delta);
    add('Qr',point(W/supportLevel+dx,my),ops.length+1);add('Qother',point(W/supportLevel-dx,my),ops.length+1);
    circles.push({center:affine(points.Fr),radius,stage:ops.length+1,label:'Transport arc: right branch'});
    op('Arc centered at Fr: select the right intersection Qr','C',null,['Qr','Qother']);
    const v=parallel([1,0,0],points.Qr);add('R',cross(v,eh),ops.length+1);
    op('Vertical through Qr meets the last chain horizontal at R','P',v,['R']);transportName='R';
   }
  }else{
  if(mode==='AK'){add('K',point(W*(1-X/p),0),0);support=cross(points.A,points.K);fixed.push({line:support,label:'AK'});}
  if(mode==='AD'||mode==='arc'){
   let F,radius,dx;
   if(mode==='AD'){F=point(W-2*W/(p-1),H-H*(p+1)/(X*(p-1)));radius=Math.abs(H-affine(points.E)[1]);dx=F[0];}
   else{const beta=(p-1)*Math.sqrt((p-2)/(12*p)),alpha=(5*p+2)/(p-2),d=W/beta,delta=H/X*Math.sqrt(alpha*alpha-1);F=point(W-d+delta,H-H/(X*beta));const G=point(W,H+H*alpha/X);add('G',G,0);radius=Math.hypot(...affine(points.E).map((x,i)=>x-G[i]));dx=W-d;}
   add('F',F,0);fixed.push({line:[1,0,-dx],label:'Vertical through D'});
   const offset=Math.abs(dx-F[0]),gap=radius-offset;if(!(gap>0)||!Number.isFinite(radius))throw Error('Nontransverse circle intersection or insufficient precision: renormalize.');transversality.push(gap/radius);const height=Math.sqrt(gap)*Math.sqrt(radius+offset);add('D',point(dx,F[1]-height),ops.length+1);
   circles.push({center:affine(F),radius,stage:ops.length+1,label:mode==='AD'?'Centered arc':'Decentered arc'});op('Draw the arc and select the lower point D','C',null,['D']);
   support=cross(points.A,points.D);op('Join A to D','J',support);
  }
  if(mode==='projective'){
   const Z=point(W*(1+(5*p-1)/(2*p*(2*p-1))),H*(1+(p+1)/((2*p-1)*X))),ell=[0,1,-H*(1+(5*p-1)/((p+1)*X))];add('Z',Z,0);fixed.push({line:ell,label:'ℓ'});
   meet('Z','E',ell,'D','ZE meets ℓ at D');support=cross(points.A,points.D);op('Join A to D','J',support);
  }
  }
  const green=cross(points.M,points[transportName]);op(`Join M to ${transportName}`,'J',green);
  const report=parallel(green,points.P);add('T',cross(report,support),ops.length+1);op(`Parallel to M${transportName} through P → T`,'P',report,['T']);
  const finish=parallel([0,1,0],points.T);add('Pnext',cross(finish,right),ops.length+1);op('Horizontal through T → P⁺','P',finish,['Pnext']);
 }else{
  meet('C','P',top,'V','CP gives center V');let curr='P',par;
  if(mode==='circle')par=parameters(p,chart);
  for(let i=1;i<p;i++){
   const factor=mode==='circle'?(i===1?par.rho:i===p-1?par.k*X*2**(p-3)/par.rho:.5):.5;
   const h='U'+i;add(h,hub(factor),0);const li=meet(h,curr,left,'L'+i);
   curr=meet('V',li,right,i===p-1?'Q':'Q'+i);
  }
  if(mode==='circle'){
   const {rho,h,j,zx,zy}=par;add('Z',point(zx,zy),0);add('MΓ',point(h,j),0);const radius=Math.hypot(2-h,j);circles.push({center:[h,j],radius,stage:0,label:'Fixed Γ'});
   const line=cross(points.Z,points.Q),[a,b,c]=line,norm=Math.hypot(a,b),dist=(a*h+b*j+c)/norm,d2=radius*radius-dist*dist;
   if(d2<=1e-13)throw Error('Tangency or no crossing: change this configuration.');
   transversality.push(d2/(radius*radius));const foot=[h-dist*a/norm,j-dist*b/norm],offset=[-b*Math.sqrt(d2)/norm,a*Math.sqrt(d2)/norm];
   const candidates=[-1,1].map(sign=>{const xy=foot.map((v,i)=>v+sign*offset[i]),dx=xy[0]-2,dy=xy[1],den=4*dx+2*dy,v=rho*4*dx/den;return {xy,v,d:(p*p-4)*(v*v+1)-2*(p*p+2)*v};});
   const good=candidates.filter(c=>Number.isFinite(c.v)&&c.d<0);
   if(good.length!==1)throw Error('Cannot identify the branch, or G=B: change the setup.');
   add('G',point(...good[0].xy),ops.length+1);add('Gother',point(...candidates.find(c=>c!==good[0]).xy),ops.length+1);op('ZQ crosses Γ: select the central arc','J',line,['G','Gother']);
   meet('B','G',top,'U','BG → readout center U');meet('U','L1',right,'Pnext','UL₁ → P⁺');
  }else{
   const pairs=[];
   if(mode==='halley')pairs.push([(p-1)/(4*p),(p+1)/(4*p),(p+1)/(4*p),(p-1)/(4*p)]);
   else{const a=(p-1)*(2*p-1),b=8*p*p-2,d=Math.sqrt(12*p*p*(4*p*p-1));for(const r of [(b+d)/(2*a),(b-d)/(2*a)])pairs.push([1/(2*(1+r)),r/(2*(1+r)),r/(2*(1+r)),1/(2*(1+r))]);}
   let current='P';pairs.forEach(([af,bf,ag,bg],i)=>{
    for(const [tag,alpha,beta]of [['f',af,bf],['g',ag,bg]]){const z='Z'+tag+i;add(z,point(-2*alpha/(1-alpha),4*(1-beta/(X*2**(p-1)*(1-alpha)))),0);meet(z,'Q',top,tag+i,`Projection center ${tag} → center ${tag}`);}
    const l=meet(current,'f'+i,left,'R'+i,'Projection onto the left rail');current=meet(l,'g'+i,right,i===pairs.length-1?'Pnext':'Pmid','Projection onto the right rail');
   });
  }
 }
 const end=affine(points.Pnext);if(!end)throw Error('Final readout at infinity.');const value=1-end[1]/H,discrepancy=Math.abs(value-expected)/Math.max(1,Math.abs(expected));
 if(!(value>0)||!Number.isFinite(value+discrepancy)||discrepancy>2e-7)throw Error('The configuration is too ill-conditioned for browser precision. Renormalize or change the chart.');
 const infinite=Object.entries(points).filter(([,v])=>!affine(v)).map(([n])=>n);
 if(infinite.length)warnings.push('Projective continuation: '+infinite.join(', ')+' at infinity. The cost of the finite protocol does not apply literally.');
 return {W,H,mode:requestedMode,baseMode:mode,fast,dual,multiplications:fast?binaryCount(p):null,binary:p.toString(2),p,X,s,t,logt,chart,points,birth,ops,circles,fixed,counts,value,expected,discrepancy,warnings,transversality,root:Math.exp(-Math.log(X)/p)};
}
function validInput(p,X,s){return Number.isSafeInteger(p)&&p>=3&&p<=1_000_000&&X>0&&s>0&&Number.isFinite(X)&&Number.isFinite(s);}
function scaledCandidate(p,X,s,k){const c=2**k,lx=Math.log(X)+p*k*Math.LN2,ls=Math.log(s)-k*Math.LN2;const nextX=k===0?X:Math.exp(lx),nextS=k===0?s:Math.exp(ls);if(!(c>0&&Number.isFinite(c)&&validInput(p,nextX,nextS)))return null;return {X:nextX,s:nextS,c,k};}
export function renormalize(p,X,s,chart='compact'){
 if(!validInput(p,X,s))throw Error('Invalid parameters.');let k=Math.ceil(1-Math.log2(X)/p),r=scaledCandidate(p,X,s,k);
 if(!r)throw Error('V20 scale cannot be represented: try adaptive renormalization.');
 const par=parameters(p,chart),sigma=par.k*r.X*2**(p-3)/par.rho;
 if(Math.abs(sigma-1)<1e-12)r=scaledCandidate(p,X,s,++k);
 if(!r)throw Error('Scale cannot be represented.');return r;
}
export function needsStereographicView(g,threshold=1e4){
 const names=Object.entries(g.points).filter(([,q])=>{const a=affine(q);return !a||Math.max(...a.map(Math.abs))>threshold;}).map(([name])=>name);
 if(g.circles.some(c=>Math.max(...c.center.map(Math.abs),c.radius)>threshold))names.push('distant arc');
 return names.length?`Projective continuation: ${names.join(', ')} at infinity or near pole N. Automatic stereographic view.`:null;
}
export function geometryScore(g){
 let score=1e6*g.discrepancy+10*g.warnings.length;
 const finite=Object.values(g.points).map(affine).filter(Boolean);
 for(const a of finite)score+=Math.log1p(Math.max(...a.map(Math.abs)))/finite.length;
 // Small separations matter only for distinct points; named aliases (E, P, ...) are intentional.
 let separation=1;for(let i=0;i<finite.length;i++)for(let j=0;j<i;j++){const d=Math.hypot(finite[i][0]-finite[j][0],finite[i][1]-finite[j][1]);if(d>0)separation=Math.min(separation,d);}
 score+=Math.max(0,-Math.log10(separation)-5);
 const lines=[...g.fixed,...g.ops].map(o=>o.line).filter(Boolean);
 let angle=1;for(let i=0;i<lines.length;i++)for(let j=0;j<i;j++){const a=lines[i],b=lines[j],d=Math.abs(a[0]*b[1]-a[1]*b[0])/(Math.hypot(a[0],a[1])*Math.hypot(b[0],b[1]));if(d>1e-15)angle=Math.min(angle,d);}
 score+=Math.max(0,-Math.log10(angle)-4);
 for(const c of g.circles)score+=Math.log1p(c.radius);
 for(const t of g.transversality)score+=Math.max(0,-Math.log10(t)-3);
 return score;
}
export function renormalizeOptimal(mode,p,X,s,chart='compact',W=2,H=4){
 if(!validInput(p,X,s))throw Error('Invalid parameters.');const ks=new Set([0]);
 for(const center of [Math.ceil(1-Math.log2(X)/p),Math.round(Math.log2(s))])for(let d=-10;d<=10;d++)ks.add(center+d);
 const candidates=[];for(const k of ks){const r=scaledCandidate(p,X,s,k);if(!r)continue;try{const g=construct(mode,p,r.X,r.s,chart,W,H);candidates.push({...r,score:geometryScore(g),discrepancy:g.discrepancy});}catch{/* Invalid real branch or unrepresentable geometry: exclude candidate. */}}
 if(!candidates.length)throw Error('None of the tested dyadic scales allows a reliable construction in double precision.');
 candidates.sort((a,b)=>a.score-b.score||Math.abs(a.k)-Math.abs(b.k));return {...candidates[0],candidateCount:candidates.length,testedCount:ks.size,rawScore:candidates.find(r=>r.k===0)?.score,reason:'Minimum score among the tested dyadic scales.'};
}
export function stereo(q,W=2,H=4){const [x,y,w]=q,u=x-W/2*w,v=y-H/2*w,z=Math.sqrt(W*H/2)*w,n=u*u+v*v+z*z;return [2*u*z/n,2*v*z/n,(u*u+v*v-z*z)/n];}

// Rebuild actual Euclidean geometry for each aspect ratio: circles are not stretched.
export function rectangleLayoutScore(g){
 const xy=Object.values(g.points).map(affine).filter(Boolean),xs=xy.map(a=>a[0]),ys=xy.map(a=>a[1]);
 for(const c of g.circles){xs.push(c.center[0]-c.radius,c.center[0]+c.radius);ys.push(c.center[1]-c.radius,c.center[1]+c.radius);}
 const dx=Math.max(...xs)-Math.min(...xs),dy=Math.max(...ys)-Math.min(...ys);
 return Math.abs(Math.log(dx/dy/1.25));
}
export function adaptRectangle(mode,p,X,s,chart='compact',W=2,H=4){
 const candidates=[];
 for(const w of new Set([W,...[.25,.5,1,2,4,8,16].map(r=>r*H)])){
  try{const g=construct(mode,p,X,s,chart,w,H);candidates.push({W:w,H,score:rectangleLayoutScore(g)});}catch{}
 }
 if(!candidates.length)throw Error('None of the tested rectangles allows a reliable construction.');
 candidates.sort((a,b)=>a.score-b.score||Math.abs(Math.log(a.W/W))-Math.abs(Math.log(b.W/W)));
 return {...candidates[0],tested:candidates.length};
}
