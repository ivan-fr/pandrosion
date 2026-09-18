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
