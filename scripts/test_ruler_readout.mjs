import assert from 'node:assert/strict';
import {construct,methods,point} from '../docs/geometry.js';
import {constructRulerSegment,measureWithRuler} from '../docs/ruler-readout.js';

const affine=q=>[q[0]/q[2],q[1]/q[2]];
const near=(a,b)=>assert(Math.abs(a-b)<1e-10*Math.max(1,Math.abs(b)),`${a} != ${b}`);
const incident=(line,q)=>near(line.reduce((s,x,i)=>s+x*q[i],0),0);
let cases=0;
for(const mode of Object.keys(methods))for(const c of [.25,1,2.5])for(const source of ['P','Pnext']){
 const g=construct(mode,3,2,.75),readout=constructRulerSegment(g,c,source),{points:q,lines:l}=readout;
 for(const [line,names] of [[l.DU,['D','U']],[l.BI,['B','I']],[l.PI,['P','I']],[l.BR,['B','R']]])for(const name of names)incident(line,q[name]);
 near(l.DU[0]*l.BI[1]-l.DU[1]*l.BI[0],0);
 near(l.PI[0]*l.BR[1]-l.PI[1]*l.BR[0],0);
 near(affine(q.R)[1],g.H);
 const s=source==='P'?g.s:g.value,reading=measureWithRuler(readout.segment,readout.unit);
 // Independent scalar identity checks the incidence construction only in this test.
 near(reading.lengthCM,g.H/(4*c*s));
 assert(reading.lower<=reading.lengthCM/reading.unitCM&&reading.upper>=reading.lengthCM/reading.unitCM);
 const large=measureWithRuler(readout.segment,readout.unit,10);
 near(large.lengthCM,10*reading.lengthCM);near(large.unitCM,10*reading.unitCM);
 near(large.upper-large.lower,(reading.upper-reading.lower)/10);
 cases++;
}

// Changing the actual mark changes the result even when every scalar field lies.
const g=construct('AKfast',3,2,.75);
for(const key of ['s','value','root','expected','p','X'])Object.defineProperty(g,key,{get(){throw Error(`Readout used scalar ${key}`);}});
const initial=constructRulerSegment(g);
assert.equal(initial.points.B,initial.points.D);assert.equal(initial.points.U,initial.points.I);
g.points.P=point(g.W,g.H/2);
const moved=constructRulerSegment(g);
near(measureWithRuler(initial.segment,initial.unit).lengthCM,4/3);
near(measureWithRuler(moved.segment,moved.unit).lengthCM,2);
// Equivalent homogeneous coordinates must give the same physical result.
for(const name of ['A','B','P'])g.points[name]=g.points[name].map(x=>-7*x);
const homogeneous=constructRulerSegment(g);
near(measureWithRuler(homogeneous.segment,homogeneous.unit).lengthCM,2);

// A ruler measures Euclidean endpoint distance, including translated/rotated segments.
const unit=[point(8,-3),point(9,-3)],segment=[point(8,-3),point(8,-3+Math.cbrt(2))];
const small=measureWithRuler(segment,unit),large=measureWithRuler(segment,unit,10);
assert.equal(small.text,'1.3 cm');assert.equal(small.valueText,'1.3');
assert.equal(large.text,'12.6 cm');assert.equal(large.valueText,'1.26');
for(const [cm,expected] of [[1.249,'1.2 cm'],[1.25,'1.3 cm'],[1.251,'1.3 cm'],[.04,'0.0 cm']]){
 assert.equal(measureWithRuler([point(0,0),point(cm,0)],[point(0,0),point(1,0)]).text,expected);
}
assert.throws(()=>measureWithRuler([point(0,0),[1,0,0]],unit));
assert.throws(()=>measureWithRuler(segment,[point(0,0),point(0,0)]));
assert.throws(()=>measureWithRuler(segment,unit,0));
g.points.P=g.points.A;
assert.throws(()=>{const r=constructRulerSegment(g);measureWithRuler(r.segment,r.unit);});
console.log(JSON.stringify({status:'PASS',incidence_cases:cases,point_only_readout:true,millimetre_rounding:true,physical_scaling:true}));
