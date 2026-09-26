import assert from 'node:assert/strict';
import {subdivide} from '../docs/gallery/geometric-subdivision.js';
let cases=0;
for(const X of [1+1e-10,1.1,2,10,1e6,1e12]) for(const p of [1,1.001,Math.SQRT2,2,3,37.5,10000,1e12]) for(const n of [0,1,8,12,20,24]) {
  const q=subdivide(X,p,n), ref=X**(1/p), eps=3e-14*ref;
  assert(q.L<=ref+eps && q.U>=ref-eps,`enclosure ${X}, ${p}, ${n}`);
  assert(q.a<=q.theta && q.theta<=q.b);
  assert.equal(q.b-q.a,2**-n);
  assert(q.width>=0 && q.width<=Math.sinh(Math.log(X)/2**(n+1))**2*(1+1e-6)+1e-25);
  if(n===0) assert.equal(q.history.length,0);
  cases++;
}
for(const args of [[1,2,0],[2,0,0],[Infinity,3,2],[2,NaN,1],[2,3,25],[2,3,1.5]])assert.throws(()=>subdivide(...args),RangeError);
const q=subdivide(2,37.5,12);
assert(Math.abs(q.L-1.0186558074006528)<2e-15);
assert(Math.abs(q.U-1.0186558125140896)<2e-15);
for(const p of [1,2,4,8]) { const q=subdivide(2,p,12); assert(q.width===0); }
console.log(`${cases} numeric cases and edge cases passed (floating-point checks, not formal certificates).`);
