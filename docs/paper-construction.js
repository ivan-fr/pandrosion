// Presentation of existing incidences; never changes mathematical coordinates.
import {paperMetrics} from './geometry.js';
export const fanDashes=[[],[8,4],[9,3,2,3],[2,4],[12,3,2,3,2,3]];
export const powerLabel=n=>n===1?'s':`s^${n}`;
export function moduleTitle(g,m){
 if(m.kind==='correction')return `${g.baseMode==='arc'?'Decentered arc':g.baseMode==='projective'?'Projective AD':g.baseMode} correction · E → P+`;
 return `${m.kind==='square'?'Square':'Multiply by s'} · ${powerLabel(m.from)} → ${powerLabel(m.to)}`;
}
export function moduleScene(g,index){
 const m=g.modules[index];
 if(!m)return null;
 const correction=m.kind==='correction';
 const names=new Set(correction?['O','A','B','C','P','E','M','K','F','G','D','Z','T','Pnext']:
  ['O','A','B','C',m.input,m.other,m.copy,m.result,m.bank.unit]);
 const points=Object.fromEntries(Object.entries(g.points).filter(([n])=>names.has(n)));
 const ops=g.ops.slice(m.start,m.end),circles=correction?g.circles:[];
 const fixed=m.fixed;
 const labels=correction?{E:'Power result E',Pnext:'Next state P+',P:'Stored s'}:{
  [m.bank.unit]:`Fan ${m.bank.name}`, [m.copy]:'Upper copy',
  [m.input]:`Accumulator ${powerLabel(m.from)}`, [m.result]:m.to===g.p?'Power result E':`R(${powerLabel(m.to)})`
 };
 if(!correction&&m.kind==='multiply')labels[m.other]='Stored s';
 const metrics=paperMetrics(Object.values(points),[...fixed,...ops].map(o=>o.line).concat([[1,0,-g.W],[0,1,-g.H]]),g.H,
  correction?['K','F','G','Z'].filter(n=>points[n]).map(n=>points[n]):[points[m.bank.unit]],circles);
 return {m,names,points,ops,circles,fixed,labels,metrics};
}
export function moduleInstructions(g,m){
 if(m.kind==='correction')return g.ops.slice(m.start,m.end).map(o=>o.label.replace('P⁺','next state P+'));
 const fan=`Fan ${m.bank.name}`,other=m.kind==='square'?`the accumulator R(${powerLabel(m.from)})`:'R(s), the stored starting state';
 if(g.powerLayout==='classic'&&m.kind==='multiply')return [
  'Use the stored upper copy X(s) from the first module.',
  `Join U× to the accumulator R(${powerLabel(m.from)}).`,
  'Draw its parallel through X(s).',`Mark the right-rail intersection as R(${powerLabel(m.to)}).`
 ];
 return [
  `Copy the accumulator to the upper rail using ${fan}: draw the parallel to B U_${m.bank.name}.`,
  `Join U_${m.bank.name} to ${other}.`,
  'Draw the parallel through the copied accumulator.',
  `Mark its intersection with the right rail as R(${powerLabel(m.to)})${m.to===g.p?', the power result E':''}.`
 ];
}
// Heuristic targets: 10 mm between distinct points, 10 degrees between nonparallel lines.
// No sheet size can fix an angular shortfall by uniformly magnifying the drawing.
export function paperRecommendation(metrics){
 const {width,height,minSeparation,minAngle}=metrics;
 const mmPerUnit=Number.isFinite(minSeparation)?10/minSeparation:40;
 const sizes=[['A4',190,277],['A3',277,400],['A2',400,574]]; // 10 mm margins
 const fits=sizes.find(([,w,h])=>(width*mmPerUnit<=w&&height*mmPerUnit<=h)||(height*mmPerUnit<=w&&width*mmPerUnit<=h));
 if(!fits)return 'Beyond A2 at the 10 mm separation target; use separate modules or accept closer marks.';
 if(minAngle<10)return `${fits[0]} fits the separation target; the 10° angle target is unmet at every scale.`;
 return `${fits[0]} at about ${Math.ceil(mmPerUnit)} mm per H; heuristic targets met.`;
}
