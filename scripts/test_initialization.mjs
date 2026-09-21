import assert from 'node:assert/strict';
import {exactDouble,multiplyIntervals,compareDyadic,residualInterval,inResidualBand,initializeCalibrated,iterationDecision} from '../docs/initialization.js';
import {construct} from '../docs/geometry.js';
// Independent full-integer powers (small degrees), not the bounded interval algorithm.
for(const p of [3,7,17,32])for(const X of [Number.MIN_VALUE,1e-200,.7,2,500000,1e200,Number.MAX_VALUE]){
 const r=initializeCalibrated(p,X),a=exactDouble(X),b=exactDouble(r.c),n=a.lo*b.lo**BigInt(p),e=a.e+p*b.e;
 assert(compareDyadic(r.enclosure.lo,r.enclosure.e,n,e)<=0);
 assert(compareDyadic(n,e,r.enclosure.hi,r.enclosure.e)<=0);
 assert(inResidualBand(r.enclosure));assert(r.X>=1&&r.X<=2);assert(r.comparisons<450);
}
let cases=0,acceptedSteps=0;
for(const p of [3,4,5,7,17,32,1024,65536,1000000])for(const X of [Number.MIN_VALUE,1e-200,1e-100,.1,1,2,500000,1e100,1e200,Number.MAX_VALUE]){
 const r=initializeCalibrated(p,X);assert(inResidualBand(r.enclosure));
 for(const mode of ['AKfast','ADfast','projectiveFast','arcFast',...(p<=32?['AK','AD','projective','arc']:[])]){
  let s=1,stopped=false;
  for(let n=0;n<20;n++){const g=construct(mode,p,r.X,s);assert(g.discrepancy<2e-7);const decision=iterationDecision(p,r.X,s,g.value);if(decision.stop){stopped=true;break;}assert(decision.after<decision.before);s=g.value;acceptedSteps++;}
  assert(stopped,'No precision stop '+mode+' '+p+' '+X);cases++;
 }
}
assert.throws(()=>initializeCalibrated(2,5));assert.throws(()=>initializeCalibrated(3,0));assert.throws(()=>initializeCalibrated(3,Infinity));
// Extreme out-of-band residuals stay represented as intervals without float overflow.
for(const s of [.1,10]){const r=residualInterval(1000000,500000,s);assert(r.lo>0n&&r.hi>=r.lo);}
assert.throws(()=>iterationDecision(1000000,1.5,1,.75));
console.log(JSON.stringify({status:'PASS',calibrated_orbits:cases,acceptedSteps,exact_integer_reference_cases:28,max_degree:1000000}));
for(const p of [10,1024,1000000])for(const X of [2,2000,500000])for(const mode of ['AKfast','ADfast','projectiveFast','arcFast']){
 const r=initializeCalibrated(p,X,'wide');let s=1,stopped=false;
 for(let n=0;n<20;n++){const g=construct(mode,p,r.X,s,'compact',2,4,'spread'),d=iterationDecision(p,r.X,s,g.value,'wide');if(d.stop){stopped=true;break;}s=g.value;}
 assert(stopped,`Spread orbit failed to stop: ${mode}, ${p}, ${X}`);
}
console.log('PASS: 36 initialized spread orbits through degree one million');
