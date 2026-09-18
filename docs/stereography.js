// Sample the image circle uniformly ON THE SPHERE. Uniform planar samples can
// concentrate near the pole and leave long straight chords elsewhere.
const dot=(a,b)=>a.reduce((s,x,i)=>s+x*b[i],0);
function sphereCircle(normal,offset,radius,segments){
 const length=Math.hypot(...normal),n=normal.map(x=>x/length);
 const center=n.map(x=>x*offset/length);
 const axis=Math.abs(n[0])<.8?[1,0,0]:[0,1,0];
 const projection=dot(axis,n),v=axis.map((x,i)=>x-projection*n[i]),vl=Math.hypot(...v),u=v.map(x=>x/vl);
 const w=[n[1]*u[2]-n[2]*u[1],n[2]*u[0]-n[0]*u[2],n[0]*u[1]-n[1]*u[0]];
 return Array.from({length:segments+1},(_,i)=>{const t=2*Math.PI*i/segments;return center.map((x,j)=>x+radius*(Math.cos(t)*u[j]+Math.sin(t)*w[j]));});
}
export function stereoLineSamples(line,W=2,H=4,segments=256){
 const scale=Math.max(...line.map(Math.abs));if(!scale)return [];
 const [a,b,c]=line.map(x=>x/scale),r=Math.sqrt(W*H/2),A=a*r,B=b*r,D=a*W/2+b*H/2+c;
 const length=Math.hypot(A,B,D);if(!length)return [];
 return sphereCircle([A,B,-D],-D,Math.hypot(A,B)/length,segments);
}
export function stereoCircleSamples(center,radius,W=2,H=4,segments=256){
 const r=Math.sqrt(W*H/2),h=(center[0]-W/2)/r,k=(center[1]-H/2)/r,rho=radius/r;
 // x²+y²+z²=1 and (-2h,-2k,1-K)·(x,y,z)=-(1+K).
 const K=h*h+k*k-rho*rho,normal=[-2*h,-2*k,1-K],length=Math.hypot(...normal);
 return sphereCircle(normal,-(1+K),2*rho/length,segments);
}
