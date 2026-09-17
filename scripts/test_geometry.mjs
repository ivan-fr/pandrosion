import assert from 'node:assert/strict';
import {construct,methods,renormalize,stereo,correction} from '../docs/geometry.js';
let count=0,max=0;
for(const mode of Object.keys(methods))for(const p of [3,4,5,7,12,17])for(const X of [1.1,2,5])for(const t of [.3,.8,1.2,3]){
 for(const chart of mode==='circle'?['compact','uniform']:['compact']){
 const s=(t/X)**(1/p),g=construct(mode,p,X,s,chart);assert(g.discrepancy<2e-7);max=Math.max(max,g.discrepancy);
 const expected=mode==='AK'?{J:2,P:2*p+1,C:0}:mode==='AD'||mode==='arc'?{J:3,P:2*p+1,C:1}:mode==='projective'?{J:4,P:2*p+1,C:0}:{J:2*p+({halley:3,pade:7,circle:2}[mode]),P:0,C:0};
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
