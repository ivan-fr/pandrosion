import fs from 'node:fs';
import {construct,affine,point,cross,baseMode,orders} from '../../docs/geometry.js';
const dir=new URL('./',import.meta.url),rows=[];
function metrics(g){
 const xy=Object.values(g.points).map(affine).filter(Boolean),scale=Math.max(...xy.flat().map(Math.abs));let sep=Infinity;
 for(let i=0;i<xy.length;i++)for(let j=0;j<i;j++){const d=Math.hypot(xy[i][0]-xy[j][0],xy[i][1]-xy[j][1]);if(d>1e-10*Math.max(1,scale))sep=Math.min(sep,d);}
 const transport=g.ops.find(o=>o.label.startsWith('Join M to ')).line,support=cross(g.points.A,g.points.D||g.points.K);
 const angle=Math.abs(support[0]*transport[1]-support[1]*transport[0])/(Math.hypot(...support.slice(0,2))*Math.hypot(...transport.slice(0,2)));
 const report=[transport[0],transport[1],-transport[0]*affine(g.points.P)[0]-transport[1]*affine(g.points.P)[1]];
 const normalized=l=>l.map(x=>x/Math.hypot(...l.slice(0,2))),ls=[normalized(support),normalized(report)],eps=1e-7;let sensitivity=0;
 // Final line-line readout only: does not certify conditioning of earlier operations.
 for(let side=0;side<2;side++)for(let j=0;j<3;j++){
  let vals=[];for(const sign of [-1,1]){const a=ls.map(l=>[...l]);a[side][j]+=sign*eps;const q=affine(cross(...a));vals.push(q?1-q[1]/g.H:NaN);}
  sensitivity=Math.max(sensitivity,Math.abs(vals[1]-vals[0])/(2*eps));
 }
 return {J:g.counts.J,P:g.counts.P,C:g.counts.C,circle_line_intersections:g.counts.C,auxiliary_radicals:g.counts.C,
  fixed_named_points:Object.keys(g.points).filter(n=>g.birth[n]===0&&!['O','A','B','C','P'].includes(n)).length,
  fixed_lines:4+g.fixed.length,fixed_circles:g.circles.filter(c=>c.stage===0).length,
  max_affine_coordinate:scale,max_prepared_center_distance:Math.max(0,...Object.entries(g.points).filter(([n])=>/^(F|Gscale|Z|U)/.test(n)).map(([,q])=>affine(q)).filter(Boolean).map(q=>Math.hypot(...q))),
  min_resolved_separation:sep,readout_sine_angle:angle,circle_margin:Math.min(1,...g.transversality),final_intersection_sensitivity:sensitivity,discrepancy:g.discrepancy};
}
for(const p of [3,4,5,7,10,32,100,1000])for(const X of [.25,2,4])for(const t of [.125,.5,1,2,4])for(const power of ['native','binary']){
 if(power==='native'&&p>32)continue;
 const s=(t/X)**(1/p);
 for(const mode of ['AK','AD','projective','arc','AKdual','ADdual','projectiveDual','arcDual'])for(const q of mode==='arcDual'?[1,p,2*p]:[p]){
  const row={p,X,t,power,mode,order:orders[mode],supportLevel:q};try{Object.assign(row,metrics(construct(mode,p,X,s,'compact',2,4,q,power==='binary')));}catch(e){row.error=e.message;}rows.push(row);
 }
}
const example=rows.filter(r=>r.p===3&&r.X===2&&r.t===.5&&r.power==='native');
// Pareto comparison on a fixed scenario; heterogeneous scenarios are never pooled.
for(const r of example){const fields=['J','P','C','fixed_named_points','fixed_lines','max_affine_coordinate','final_intersection_sensitivity'];r.dominated=example.some(o=>o!==r&&!o.error&&o.order>=r.order&&o.readout_sine_angle>=r.readout_sine_angle-1e-10&&o.circle_margin>=r.circle_margin-1e-10&&fields.every(k=>o[k]<=r[k])&&fields.some(k=>o[k]<r[k]));}
const notes='binary64 proxies; separation floor = 1e-10 times max(1,coordinate scale); sensitivity covers final intersection only; fixed preparation counts objects, not minimal ruler-compass construction cost';
fs.writeFileSync(new URL('geometry_results.json',dir),'{\n"notes":'+JSON.stringify(notes)+',\n"rows":[\n'+rows.map(r=>JSON.stringify(r)).join(',\n')+'\n],\n"example":'+JSON.stringify(example,null,2)+'\n}\n');
if(rows.some(r=>r.error || !Number.isFinite(r.discrepancy) || r.discrepancy>1e-7))throw new Error('Geometric benchmark regression');
console.log(JSON.stringify({cases:rows.length,failures:rows.filter(r=>r.error).length,example}));
