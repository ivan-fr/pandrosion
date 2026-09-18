import assert from 'node:assert/strict';
import {construct,affine,adaptRectangle,rectangleLayoutScore,stereo} from '../docs/geometry.js';
import {initializeCalibrated,inResidualBand,iterationDecision} from '../docs/initialization.js';
let cases=0,orbits=0;
for(const p of [3,7,32,1024,1000000])for(const X of [.25,.5,1,2,4])for(const mode of ['AKfast','ADfast','projectiveFast','arcFast',...(p<=32?['AK','AD','projective','arc']:[])])for(const [W,H] of [[.5,4],[2,4],[32,4],[4,.5],[7,11]]){
 const g=construct(mode,p,X,1,'compact',W,H),baseline=construct(mode,p,X,1);
 assert(Math.abs(g.value-baseline.value)<2e-8);assert.equal(g.W,W);assert.equal(g.H,H);
 assert(Math.abs(affine(g.points.O)[1]-H)<1e-12);assert(Math.abs(affine(g.points.B)[0]-W)<1e-12);
 for(const circle of g.circles){const D=affine(g.points.D);assert(Math.abs(Math.hypot(D[0]-circle.center[0],D[1]-circle.center[1])/circle.radius-1)<2e-10);}
 const z=stereo(g.points.P,W,H);assert(Math.abs(z.reduce((s,a)=>s+a*a,0)-1)<1e-12);cases++;
}
for(const p of [3,4,5,7,17,32,1024,65536,1000000])for(const X of [Number.MIN_VALUE,1e-200,1e-100,.1,1,2,500000,1e100,1e200,Number.MAX_VALUE])for(const mode of ['AKfast','ADfast','projectiveFast','arcFast',...(p<=32?['AK','AD','projective','arc']:[])]){
 const r=initializeCalibrated(p,X,'wide');assert(inResidualBand(r.enclosure,'wide'));assert(r.X>=.25&&r.X<=4);
 const d=adaptRectangle(mode,p,r.X,1);assert(d.score<=rectangleLayoutScore(construct(mode,p,r.X,1))+1e-12);
 let s=1,stop=false;
 for(let n=0;n<20;n++){const g=construct(mode,p,r.X,s,'compact',d.W,d.H);const decision=iterationDecision(p,r.X,s,g.value,'wide');if(decision.stop){stop=true;break;}s=g.value;}
 assert(stop);orbits++;
}
assert.throws(()=>construct('AD',3,2,1,'compact',0,4));
assert.throws(()=>construct('circle',3,2,.75,'compact',3,4));
assert.throws(()=>initializeCalibrated(3,2,'invalid'));
// AK is a concrete witness that [1/4,4] is not invariant.
const g=construct('AKfast',1000000,4,1);assert(g.value**1000000*4<.25);
console.log(JSON.stringify({status:'PASS',rectangle_cases:cases,wide_calibrated_orbits:orbits,euclidean_circles_checked:true}));
