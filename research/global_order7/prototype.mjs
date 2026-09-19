import assert from 'node:assert/strict';
import {cross,point,affine,construct} from '../../docs/geometry.js';
// Coordinates (x,y), scalar q=1-y. Rails L:x=0, R:x=1, H:y=1.
export function order7(p,t,s,X=1,powerPoint=point(1,1-t/X)){
 if(!(p>=3&&X>0&&s>0&&t>0))throw Error("Positive data and p>=3 are required.");
 const L=[1,0,0],R=[1,0,-1],H=[0,1,-1],ops=[],points={Input:powerPoint,P:point(1,1-s)};
 const put=(n,q)=>(points[n]=q,n),fix=(n,x,y)=>put(n,point(x,y));
 const meet=(a,b,rail,n)=>{const line=cross(points[a],points[b]);put(n,cross(line,rail));ops.push({a,b,n,line});return n;};
 // Any nonconstant F(u)=(n1*u+n0)/(d1*u+d0), from L(u) to top x=F(u).
 const mobiusTop=(input,n1,n0,d1,d0,tag)=>{
  const a=n1/d1,b=2*(a*d0-n0)/(d1*(1-a)),beta=b+2*d0/d1;
  fix(tag+'Z1',-1,1+beta);fix(tag+'Z2',a,1-b);
  meet(input,tag+'Z1',R,tag+'Y');return meet(tag+'Y',tag+'Z2',H,tag+'V');
 };
 fix('Zc',-2,1+2/X);fix('Yc',4,-2);
 meet('Input','Zc',H,'Ztop');meet('Ztop','Yc',L,'Z');
 fix('R2',1,-1);fix('U2',-1,1);
 meet('Z','R2',H,'SquareCenter');meet('Z','U2',R,'TwiceZ');meet('TwiceZ','SquareCenter',L,'Square');
 const a=(3*p*p-2)/(5*p*p),b=(4*p*p-1)/(15*p*p);
 const v=mobiusTop('Square',-b,1,2*p*a-b,1-2*p,'D');
 // TwiceZ is REUSED: multiplication z/D needs only one further join.
 meet('TwiceZ',v,L,'Ratio');
 const c=mobiusTop('Ratio',8,8,9,7,'C');
 fix('U8',8/7,1);meet('P','U8',L,'EightS');meet('EightS',c,R,'Output');
 const value=1-affine(points.Output)[1];
 return {value,ops,points,p,t,s};
}
// Reuse the existing engine's power-stage incidences, not a numerical s^p placement.
export function fromPower(p,X,s,binary=false){
 const base=construct(binary?'AKfast':'AK',p,X,s);
 const E=base.points.E, input=[E[0]/base.W,E[1]/base.H,E[2]];
 const g=order7(p,base.t,s,X,input),power=base.ops.slice(0,-3);
 return {...g,power,counts:{J:power.filter(o=>o.kind==='J').length+g.ops.length,P:power.filter(o=>o.kind==='P').length,C:0}};
}
if(import.meta.url===`file://${process.argv[1]}`){
 let worst=0,total=0,nonfinite=0;
 for(const p of [3,4,5,7,10,32,100,1000])for(const t of [.000001,.001,.125,.5,1,2,8,1000,1e6])for(const s of [.125,1,8]){
  const g=order7(p,t,s),z=(t-1)/(t+1),u=z*z,D=p*(1-(3*p*p-2)/(5*p*p)*u)/(1-(4*p*p-1)/(15*p*p)*u),expected=s*(D-z)/(D+z);
  worst=Math.max(worst,Math.abs(g.value-expected)/Math.max(1,Math.abs(expected)));
  nonfinite+=Object.values(g.points).filter(q=>!affine(q)).length;
  assert.equal(g.ops.length,12);assert(Math.abs(g.value-expected)<1e-9*Math.max(1,Math.abs(expected)));total++;
 }
 console.log({total,worst,nonfinite,joins:12});
}

if(import.meta.url===`file://${process.argv[1]}`){
 let integrated=0;
 for(const p of [3,4,7,16,32,100,1000])for(const X of [.25,2,4])for(const t of [.125,.5,1,2,4])for(const binary of [false,true]){
  if(!binary&&p>32)continue;
  const s=Math.exp(Math.log(t/X)/p),g=fromPower(p,X,s,binary),z=(t-1)/(t+1),D=p*(1-(3*p*p-2)/(5*p*p)*z*z)/(1-(4*p*p-1)/(15*p*p)*z*z);
  assert(Math.abs(g.value-s*(D-z)/(D+z))<1e-9);
  if(!binary)assert.deepEqual(g.counts,{J:13,P:2*p-1,C:0});
  assert(Object.values(g.points).every(affine));integrated++;
 }
 console.log({integrated,power:'native and binary; power point obtained from incidences'});
}
