import assert from 'node:assert/strict';
import {construct,methods,renormalize,stereo,correction,binaryCount,affine,renormalizeOptimal,needsStereographicView,cross} from '../docs/geometry.js';
let count=0,max=0;
for(const mode of Object.keys(methods))for(const p of [3,4,5,7,12,17])for(const X of [1.1,2,5])for(const t of [.3,.8,1.2,3]){
 for(const chart of mode==='circle'?['compact','uniform']:['compact']){
 const s=(t/X)**(1/p),g=construct(mode,p,X,s,chart);assert(g.discrepancy<2e-7);max=Math.max(max,g.discrepancy);
 const expected=g.fast?{J:binaryCount(p)+({AKfast:1,ADfast:2,projectiveFast:3,arcFast:2}[mode]),P:binaryCount(p)+p.toString(2).length+1,C:['ADfast','arcFast'].includes(mode)?1:0}:mode==='AK'?{J:2,P:2*p+1,C:0}:mode==='AD'||mode==='arc'?{J:3,P:2*p+1,C:1}:mode==='projective'?{J:4,P:2*p+1,C:0}:{J:2*p+({halley:3,pade:7,circle:2}[mode]),P:0,C:0};
 assert.deepEqual(g.counts,expected);
 for(const q of Object.values(g.points)){const z=stereo(q);assert(Math.abs(z.reduce((a,x)=>a+x*x,0)-1)<1e-12);}
 const r=renormalize(p,X,s);assert(Math.abs(r.X*r.s**p/t-1)<1e-12);assert(Math.abs(r.c*r.s*correction(mode,p,t)-g.expected)<1e-12);count++;
 }}
for(const [p,X,s]of [[3,2,1],[3,2,(7.75/2)**(1/3)],[3,113/10,.75]])assert(construct('circle',p,X,s).warnings.length>0);
assert.throws(()=>construct('circle',3,2,.1));
assert.throws(()=>construct('circle',3,2,(83/85)**(1/3),'uniform'));
assert.throws(()=>construct('arc',3,1e-300,1e100));
const normalizedFixedInfinity=renormalize(3,113/10,.75);
assert.equal(normalizedFixedInfinity.c,2);
assert.equal(construct('circle',3,normalizedFixedInfinity.X,normalizedFixedInfinity.s).warnings.length,0);
console.log(JSON.stringify({status:'PASS',independent_geometric_cases:count,max_relative_readout_discrepancy:max,infinity_cases:3}));

assert.equal(count,864);
for(const p of [3,4,5,7,12,17,32,1024,65536,1000000])for(const mode of ['AKfast','ADfast','projectiveFast','arcFast']){
 const X=2,s=Math.exp(Math.log(.8/X)/p),g=construct(mode,p,X,s);
 assert(Math.abs((1-affine(g.points.E)[1]/4)/Math.exp(p*Math.log(s))-1)<1e-8);
 assert.equal(g.multiplications,p.toString(2).length-1+[...p.toString(2)].filter(x=>x==='1').length-1);
 assert(g.ops.length<6*p.toString(2).length+10);
 if(p<=32)assert(Math.abs(g.value-construct(g.baseMode,p,X,s).value)<2e-7);
}
for(const [p,n] of [[3,2],[5,3],[13,5],[32,5],[1024,10]])assert.equal(binaryCount(p),n);
for(const X of [1e-200,1e-100,1e100,1e200])for(const mode of ['AKfast','ADfast','projectiveFast','arcFast']){
 const p=3,s=Math.exp((Math.log(.8)-Math.log(X))/p),r=renormalizeOptimal(mode,p,X,s);
 assert(Math.abs(Math.log(r.X)+p*Math.log(r.s)-Math.log(X)-p*Math.log(s))<1e-12);
 assert(construct(mode,p,r.X,r.s).discrepancy<2e-7);
 assert(Math.abs(r.X*r.s**p/(X*s**p)-1)<1e-12);
 assert(Math.abs(Math.exp(Math.log(r.X)/p)/r.c/Math.exp(Math.log(X)/p)-1)<1e-12);
 if(r.rawScore!==undefined)assert(r.score<=r.rawScore);
}
const best=renormalizeOptimal('arcFast',3,2,.75);assert(best.score<=best.rawScore);
for(const s of [1,(7.75/2)**(1/3)]){const g=construct('circle',3,2,s);assert(needsStereographicView(g));const infinite=Object.values(g.points).filter(q=>!affine(q));assert(infinite.length);for(const q of infinite)assert(Math.hypot(...stereo(q).map((x,i)=>x-[0,0,1][i]))<1e-9);}
assert.throws(()=>cross([1,2,1],[1,2,1]));assert.equal(cross([1,0,0],[1,0,-2])[2],0);
assert.throws(()=>construct('AKfast',Number.MAX_SAFE_INTEGER+1,2,1));
console.log('PASS: binary powers, extreme-scale normalization, projective continuation and true degeneracy');

assert(needsStereographicView({points:{V:[1e6,0,1]},circles:[]}));

for(const mode of ['AK','AD','projective','arc','AKfast','ADfast','projectiveFast','arcFast'])for(const p of [3,4,17])for(const X of [1,2,p]){
 const g=construct(mode,p,X,1);assert(g.discrepancy<2e-7);
 for(const v of Object.values(g.points))assert(affine(v),'Native rectangle infinity at s=1');
 assert(Math.abs(affine(g.points.E)[1])<1e-10);
}
console.log('PASS: 72 native/fast s=1 and harmless fixed-vertex coincidence cases');

// Parameterized products are computed by incidences, checked independently here.
const {fastMultiply,fastTopPoint,fanRatios,lineAngle}=await import('../docs/geometry.js');
const {findInitialState,residualInterval,inResidualBand}=await import('../docs/initialization.js');
let lambdaCases=0,spreadCases=0;
for(const ratio of [.4,.7,1.2,2,3.5])for(const a of [.2,.5,.8,1,1.2,2,5])for(const b of [.2,.5,.8,1,1.2,2,5])for(const [W,H] of [[2,4],[7,11]]){
 const R=q=>[W,H*(1-q),1],m=fastMultiply(W,H,ratio*H,R(a),R(b));
 assert(Math.abs((1-affine(m.result)[1]/H)-a*b)<2e-12*Math.max(1,a*b));
 assert(Math.hypot(...affine(m.top).map((v,i)=>v-affine(fastTopPoint(W,H,ratio*H,a))[i]))<1e-11);
 lambdaCases++;
}
for(const p of [3,10,13,32,1024,65536,1000000])for(const mode of ['AKfast','ADfast','projectiveFast','arcFast'])for(const t of [.3,.8,1,1.2,3]){
 const s=Math.exp(Math.log(t/2)/p),spread=construct(mode,p,2,s,'compact',2,4,'spread'),classic=construct(mode,p,2,s);
 assert(Math.abs(spread.value-classic.value)<2e-7);assert.equal(spread.t,classic.t);
 assert.equal(spread.multiplications,binaryCount(p));assert.equal(spread.modules.length,binaryCount(p)+1);
 assert.equal(spread.modules.at(-1).kind,'correction');
 assert.equal(spread.counts.P,2*binaryCount(p)+2); // Each independently routed module copies its input.
 for(const m of spread.modules.slice(0,-1)){
  assert.equal(m.end-m.start,3);assert.equal(m.candidates.length,fanRatios(p).length);
  assert(m.candidates.every(c=>m.score<=c.score));
  assert(fanRatios(p).includes(m.bank.ratio));assert(m.bank.lambda>0);
 }
 spreadCases++;
}
assert.equal(binaryCount(1000000),25);
assert.throws(()=>fastMultiply(2,4,0,[2,1,1],[2,2,1]));
assert.throws(()=>construct('AKfast',10,2,1,'compact',2,4,'unknown'));
const demoStart=findInitialState(10,2000,'wide');assert(inResidualBand(residualInterval(10,2000,demoStart.c),'wide'));
const demo=construct('AKfast',10,2000,demoStart.c,'compact',.02,4,'spread');
assert.deepEqual(demo.modules.slice(0,-1).map(m=>m.to),[2,4,5,10]);
assert.equal(demo.binary,'1010');assert.equal(demo.multiplications,4);
assert(Math.abs(1-affine(demo.points.E)[1]/4-demoStart.c**10)<1e-13);
const fanJoins=demo.modules.slice(0,-1).map(m=>demo.ops[m.start+1].line);
assert(lineAngle(fanJoins[0],fanJoins[1])>10,'First two demo squares need distinct directions');
assert(new Set(demo.modules.slice(0,-1).map(m=>m.bank.name)).size>=2);
console.log(JSON.stringify({status:'PASS',lambda_products:lambdaCases,spread_classic_comparisons:spreadCases,paper_demo_start:demoStart.c,million_multiplications:25}));
