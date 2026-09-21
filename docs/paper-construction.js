// Presentation of existing incidences; never changes mathematical coordinates.
import {affine,paperMetrics} from './geometry.js';
export const fanDashes=[[],[8,4],[9,3,2,3],[2,4],[12,3,2,3,2,3]];
export const powerLabel=n=>n===1?'s':`s^${n}`;
export function moduleTitle(g,m){
 if(m.kind==='correction')return `${g.baseMode==='arc'?'Decentered arc':g.baseMode==='projective'?'Projective AD':g.baseMode} correction · E → P+`;
 return `${m.kind==='square'?'Square':'Multiply by s'} · ${powerLabel(m.from)} → ${powerLabel(m.to)}`;
}
export function moduleScene(g,index){
 const m=g.modules[index];
 if(!m)return null;
 const correction=m.kind==='correction',identity=!correction&&g.s===1;
 // Algebraic equality, not a proximity test: every positive power of exactly 1 is 1.
 const names=new Set(identity?['O','A','B','C',m.bank.unit]:correction?['O','A','B','C','P','E','M','K','F','G','D','Z','T','Pnext']:
  ['O','A','B','C',m.input,m.other,m.copy,m.result,m.bank.unit]);
 const points=Object.fromEntries(Object.entries(g.points).filter(([n])=>names.has(n)));
 const ops=identity?[]:g.ops.slice(m.start,m.end),circles=correction?g.circles:[];
 const fixed=m.fixed;
 const labels=identity?{B:m.to===g.p?'B = P = accumulator = E':'B = P = input = result',
  [m.bank.unit]:`Fan ${m.bank.name} = upper copy`}:correction?{E:`E · s^${g.p}`,Pnext:'Next state P+',P:'P · s'}:{
  [m.bank.unit]:`Fan ${m.bank.name}`, [m.copy]:'Upper copy',
  [m.input]:m.input==='P'?'P · s':`Accumulator ${powerLabel(m.from)}`, [m.result]:m.to===g.p?`E · s^${g.p}`:`R(${powerLabel(m.to)})`
 };
 if(!correction&&!identity&&m.kind==='multiply')labels[m.other]='P · s';
 const metrics=paperMetrics(Object.values(points),[...fixed,...ops].map(o=>o.line).concat([[1,0,-g.W],[0,1,-g.H]]),g.H,
  correction?['K','F','G','Z'].filter(n=>points[n]).map(n=>points[n]):[points[m.bank.unit]],circles);
 return {m,names,points,ops,circles,fixed,labels,metrics,identity};
}
export function moduleInstructions(g,m){
 if(m.kind==='correction')return g.ops.slice(m.start,m.end).map(o=>o.label.replace('P⁺','next state P+'));
 if(g.s===1)return [
  'The prepared state is exactly s = 1, so every power in this chain equals 1.',
  `Reuse the existing points: R(1) = P = B and the upper copy = Fan ${m.bank.name}. No new mark or parallel is needed.`,
  'Reuse B as the power result E and go directly to the correction module. The correction can still change the state.'
 ];
 const fan=`Fan ${m.bank.name}`,other=m.kind==='square'?`the accumulator R(${powerLabel(m.from)})`:'P = R(s), the stored starting state';
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
export function modulePaperStatus(g,scene){
 if(scene.m.kind==='correction')return g.s===1?{kind:'shared-state',text:'B = P = E: one geometric point, because s = 1 and s^p = 1. P names the input state; E names its power. The correction constructs the next state P+.'}:null;
 if(scene.identity)return {kind:'identity',text:'Exact coincidence, not a tiny gap: s = 1. Fan and upper copy are one point; accumulator and result are B. Reuse the marks, then continue to the correction.'};
 const unit=affine(g.points[scene.m.bank.unit]),copy=affine(g.points[scene.m.copy]);
 const gap=Math.hypot(unit[0]-copy[0],unit[1]-copy[1])/g.H;
 if(gap<=1e-12)return {kind:'unresolved',gap,text:'The fan and upper copy are distinct in exact arithmetic (s ≠ 1), but this display cannot resolve their gap. Do not merge these marks or treat this module as a reliable hand construction.'};
 const {width,height}=scene.metrics;
 const largestScale=Math.max(Math.min(400/width,574/height),Math.min(574/width,400/height));
 const gapMM=gap*largestScale;
 if(gapMM<10)return {kind:'too-close',gap,gapMM,text:`Hand-construction limit: fan/copy gap = ${gap.toExponential(3)} H, at most ${gapMM<.01?gapMM.toExponential(2):gapMM.toFixed(2)} mm when this module fits A2. Below the 10 mm readability target. Separating labels or changing the fan cannot guarantee a usable gap near 1; a different geometric encoding would be needed.`};
 return null;
}
// Heuristic targets: 10 mm between distinct points, 10 degrees between nonparallel lines.
// No sheet size can fix an angular shortfall by uniformly magnifying the drawing.
export function paperRecommendation(metrics){
 // An almost coincident pair may be a real tiny gap or roundoff at an exact alias.
 if(metrics.unresolvedPairs>0)return 'Undetermined: some marks differ by less than 10⁻¹² H. Verify exact coincidences before choosing a sheet.';
 const {width,height,minSeparation,minAngle}=metrics;
 const mmPerUnit=Number.isFinite(minSeparation)?10/minSeparation:40;
 const sizes=[['A4',190,277],['A3',277,400],['A2',400,574]]; // 10 mm margins
 const fits=sizes.find(([,w,h])=>(width*mmPerUnit<=w&&height*mmPerUnit<=h)||(height*mmPerUnit<=w&&width*mmPerUnit<=h));
 if(!fits)return 'Beyond A2 at the 10 mm separation target; use separate modules or accept closer marks.';
 if(minAngle<10)return `${fits[0]} fits the separation target; the 10° angle target is unmet at every scale.`;
 return `${fits[0]} at about ${Math.ceil(mmPerUnit)} mm per H; heuristic targets met.`;
}
