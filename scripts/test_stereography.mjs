import assert from 'node:assert/strict';
import {stereoLineSamples,stereoCircleSamples} from '../docs/stereography.js';
import {construct,adaptRectangle,stereo,point} from '../docs/geometry.js';
const norm=v=>Math.hypot(...v),sub=(a,b)=>a.map((x,i)=>x-b[i]),dot=(a,b)=>a.reduce((s,x,i)=>s+x*b[i],0);
function distance(q,points){let best=Infinity;for(let i=1;i<points.length;i++){const a=points[i-1],v=sub(points[i],a),d=dot(v,v),t=d?Math.max(0,Math.min(1,dot(sub(q,a),v)/d)):0;best=Math.min(best,norm(sub(q,a.map((x,j)=>x+t*v[j]))));}return best;}
let curves=0,worst=0;
function check(samples,reference){
 assert.equal(samples.length,257);for(const q of samples)assert(Math.abs(norm(q)-1)<1e-10);
 assert(norm(sub(samples[0],samples.at(-1)))<1e-12);
 for(let i=1;i<samples.length;i++)assert(norm(sub(samples[i],samples[i-1]))<=2*Math.sin(Math.PI/256)+1e-10);
 for(const q of reference){const e=distance(q,samples);worst=Math.max(worst,e);assert(e<.00008,`Sphere chord error ${e}`);}curves++;
}
// The reported p=3,X=2 decentered arc, plus different aspects, degrees and iteration states.
for(const p of [3,7,32])for(const X of [.25,2,4])for(const mode of ['arc','AD','projective','AK']){
 const d=adaptRectangle(mode,p,X,1);for(const [W,H]of [[2,4],[d.W,d.H],[7,11]]){
 const g=construct(mode,p,X,1,'compact',W,H);
 for(const line of [...g.fixed,...g.ops].map(o=>o.line).filter(Boolean)){
 const [a,b,c]=line,n=Math.hypot(a,b);if(!n)continue;
 const base=[-c*a/(n*n),-c*b/(n*n)],dir=[-b/n,a/n];
 const refs=Array.from({length:31},(_,i)=>{const t=-Math.PI/2+Math.PI*i/30;return stereo([base[0]*Math.cos(t)+dir[0]*Math.sin(t),base[1]*Math.cos(t)+dir[1]*Math.sin(t),Math.cos(t)],W,H);});
 check(stereoLineSamples(line,W,H),refs);
 }
 for(const c of g.circles){const refs=Array.from({length:101},(_,i)=>{const t=2*Math.PI*i/100;return stereo(point(c.center[0]+c.radius*Math.cos(t),c.center[1]+c.radius*Math.sin(t)),W,H);});check(stereoCircleSamples(c.center,c.radius,W,H),refs);}
 }
}
console.log(JSON.stringify({status:'PASS',curves,max_sphere_chord_error:worst}));
