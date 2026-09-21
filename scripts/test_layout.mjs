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

// Paper metrics and frames keep the Euclidean geometry; page size is only a heuristic.
const {paperMetrics}=await import('../docs/geometry.js');
const {moduleScene,paperRecommendation}=await import('../docs/paper-construction.js');
for(const p of [10,1000000])for(const mode of ['AKfast','ADfast','projectiveFast','arcFast']){
 const s=Math.exp(Math.log(.8/2)/p),g=construct(mode,p,2,s,'compact',2,4,'spread'),scaled=construct(mode,p,2,s,'compact',6,12,'spread');
 assert.deepEqual(g.modules.slice(0,-1).map(m=>m.bank.name),scaled.modules.slice(0,-1).map(m=>m.bank.name));
 for(let i=0;i<g.modules.length;i++){
  const a=moduleScene(g,i),b=moduleScene(scaled,i);
  assert(Math.abs(a.metrics.width-b.metrics.width)<1e-8);
  assert(Math.abs(a.metrics.height-b.metrics.height)<1e-8);
  assert(Math.abs(a.metrics.minAngle-b.metrics.minAngle)<1e-6);
  assert(Number.isFinite(a.metrics.score));assert(a.names.has('A')&&a.names.has('B'));
  if(i<g.modules.length-1){assert.equal(a.ops.length,3);assert(!a.names.has('K'));assert.equal(a.circles.length,0);}
  else{assert(a.names.has('E'));assert(a.names.has('Pnext'));}
 }
}
assert.match(paperRecommendation({width:1,height:1,minSeparation:.1,minAngle:20}),/^A4/);
assert.match(paperRecommendation({width:2.5,height:2.5,minSeparation:.1,minAngle:20}),/^A3/);
assert.match(paperRecommendation({width:3.5,height:4.5,minSeparation:.1,minAngle:20}),/^A2/);
assert.match(paperRecommendation({width:100,height:100,minSeparation:.001,minAngle:20}),/Beyond A2/);
assert.match(paperRecommendation({width:1,height:1,minSeparation:.1,minAngle:1}),/angle target is unmet at every scale/);
const aliases=paperMetrics([[0,0,1],[0,0,1],[1,0,1]],[[1,1,0],[1,1,1],[1,0,0]],1);
assert.equal(aliases.aliases,1);assert.equal(aliases.minSeparation,1);assert(Math.abs(aliases.minAngle-45)<1e-10);
console.log('PASS: modular frames, scale-invariant routing and honest paper-size recommendations');

const unresolved=paperMetrics([[0,0,1],[1e-14,0,1],[1,1,1]],[[1,0,0],[0,1,0]],1);
assert.equal(unresolved.unresolvedPairs,1);
assert.match(paperRecommendation(unresolved),/^Undetermined/);
console.log('PASS: sub-resolution gaps never receive a false paper-size recommendation');

const {modulePaperStatus,moduleInstructions}=await import('../docs/paper-construction.js');
for(const mode of ['AKfast','ADfast','projectiveFast','arcFast'])for(const layout of ['classic','spread']){
 const identity=construct(mode,1000000,1.5,1,'compact',2,4,layout);
 for(let i=0;i<25;i++){const scene=moduleScene(identity,i);assert(scene.identity);assert.equal(scene.ops.length,0);assert.equal(modulePaperStatus(identity,scene).kind,'identity');assert(!scene.names.has(scene.m.copy));assert.match(moduleInstructions(identity,scene.m).join(' '),/No new mark or parallel/);}
 assert(!moduleScene(identity,25).identity);
 assert.equal(modulePaperStatus(identity,moduleScene(identity,25)).kind,'shared-state');
 const close=construct(mode,1000000,1.5,1-1e-8,'compact',2,4,layout),scene=moduleScene(close,0);
 assert.equal(modulePaperStatus(close,moduleScene(close,25)),null);
 assert(!scene.identity);assert.equal(modulePaperStatus(close,scene).kind,'too-close');
 const tiny=construct(mode,3,1.5,1-1e-14,'compact',2,4,layout);
 assert.equal(modulePaperStatus(tiny,moduleScene(tiny,0)).kind,'unresolved');
}
console.log('PASS: exact identity reuse is distinguished from small nonzero physical gaps');
