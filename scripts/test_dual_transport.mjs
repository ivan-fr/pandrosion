import assert from 'node:assert/strict';
import {construct,dualModes,affine,correction} from '../docs/geometry.js';
import {initializeCalibrated,iterationDecision} from '../docs/initialization.js';
let cases=0,worst=0;
for(const [mode,base] of Object.entries(dualModes))for(const p of [3,4,7,16,32])for(const X of [.25,1,2,4])for(const t of [.125,.25,.8,1,2,4])for(const [W,H] of [[2,4],[8,3]]){
 const s=(t/X)**(1/p),g=construct(mode,p,X,s,'compact',W,H),old=construct(base,p,X,s,'compact',W,H);
 assert(g.discrepancy<2e-7);worst=Math.max(worst,g.discrepancy);
 assert(Math.abs(g.value-old.value)<2e-7);
 const M=affine(g.points.M),R=affine(g.points.R||g.points.E),r=(R[1]-M[1])/(R[0]-M[0])*W*X/H;
 assert(Math.abs(r-p*(1-1/correction(base,p,t)))<1e-7);
 assert(g.fixed.some(f=>f.label==='Fixed AK'));assert(!g.points.D);
 if(base==='AD'){assert.equal(g.counts.C,0);assert.equal(g.counts.J,old.counts.J-1);assert.equal(g.counts.P,old.counts.P);}
 if(base==='arc')assert.equal(g.counts.C,1);
 cases++;
}
// The exact unit-scale branch reuses EG and omits its scaling projection.
{const p=3,X=2,H=4,beta=(p-1)*Math.sqrt((p-2)/(12*p)),W=p*H/(X*beta),g=construct('arcDual',p,X,.75,'compact',W,H);assert(!g.points.Escaled);assert(g.discrepancy<1e-10);}
// No root is used by initialization; test genuine geometric iteration and its precision stop.
for(const mode of Object.keys(dualModes))for(const p of [3,7,32])for(const X of [1e-100,2,500000,1e100]){
 const init=initializeCalibrated(p,X);let s=1,stopped=false;
 for(let i=0;i<30;i++){const g=construct(mode,p,init.X,s);const decision=iterationDecision(p,init.X,s,g.value);if(decision.stop){stopped=true;break;}s=g.value;}
 assert(stopped,`${mode}/${p}/${X} did not stop`);
}
console.log(JSON.stringify({status:'PASS',dual_cases:cases,max_discrepancy:worst,initialized_orbits:48}));
