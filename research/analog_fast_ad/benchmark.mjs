// Host-software comparison, not hardware energy or SPICE simulator wall time.
import {performance} from 'node:perf_hooks';
import os from 'node:os';
import fs from 'node:fs';
import {initializeCalibrated} from '../../docs/initialization.js';
let checksum=0;
function refine(p,r){
 let q=0;
 const bits=p.toString(2).slice(1);
 for(let k=0;k<6;k++){
  let n=1,d=q;
  for(const bit of bits){d+=n/(2*p)*d*d;n*=2;
   if(bit==='1'){d+=(q-d)/(n+1)+n/(p*(n+1))*d*q;n++;}}
  const t=r.X*(1+d);q+=2*(1+q/p)*(1-t)/(1+t+(t-1)/p);
 }
 return 1/(r.c*(1+q/p));
}
function measure(fn,batch){
 for(let j=0;j<50;j++)checksum+=fn(j);
 const times=[];
 for(let j=0;j<21;j++){
  const start=performance.now();
  for(let k=0;k<batch;k++)checksum+=fn(j*batch+k);
  times.push((performance.now()-start)*1000/batch);
 }
 times.sort((a,b)=>a-b);
 return {median_us:times[10],p10_us:times[2],p90_us:times[18],batch,repeats:21};
}
const rows=[];
for(const p of [3,32,983039,1000000])for(const X of [1e-300,500000,1e300]){
 // Vary input on every call to prevent timing a constant-folded library result.
 const inputs=Array.from({length:256},(_,i)=>X*(1+i/1024));
 const prepare=i=>initializeCalibrated(p,inputs[i%inputs.length],'compact');
 const prepared=inputs.map((_,i)=>prepare(i));const r=prepared[0];
 const stages=Math.floor(Math.log2(p))+p.toString(2).replaceAll('0','').length-1;
 rows.push({p,X,comparisons:r.comparisons,stages,
  prepared_root:1/r.c,centered_root:refine(p,r),standard_root:Math.exp(Math.log(X)/p),
  preparation:measure(i=>prepare(i).c,10),
  centered_six_steps_only:measure(i=>refine(p,prepared[i%prepared.length]),200),
  full_centered_digital:measure(i=>refine(p,prepare(i)),10),
  standard_library:measure(i=>Math.exp(Math.log(inputs[i%inputs.length])/p),2000),
  analog_core_nominal_us:2905,analog_core_slow_us:87150,
  note:'Analog schedule excludes programming, ADC and final digital decoding; energy unmeasured.'});
}
if(!Number.isFinite(checksum))throw Error('Non-finite benchmark sink');
fs.writeFileSync(new URL('benchmark_results.json',import.meta.url),JSON.stringify({
 scope:'Host JS timings, non-portable; no speed or energy advantage claimed',
 input_variation:'256 inputs X*(1+i/1024); varying calls to prevent constant folding',
 node:process.version,platform:process.platform,arch:process.arch,cpu:os.cpus()[0]?.model,
 rows},null,2)+'\n');
console.log(rows.filter(x=>x.X===500000).map(x=>({p:x.p,prepare_us:x.preparation.median_us,
 full_us:x.full_centered_digital.median_us,library_us:x.standard_library.median_us,analog_us:x.analog_core_nominal_us})));
