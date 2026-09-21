import {bindSphereDrag} from './sphere-drag.js';
import {stereoLineSamples,stereoCircleSamples} from './stereography.js';
import {construct,methods,orders,affine,point,stereo,renormalize,renormalizeOptimal,needsStereographicView,adaptRectangle,baseMode,paperMetrics} from './geometry.js';
import {initializeCalibrated,findInitialState,iterationDecision,initializationBands} from './initialization.js';
import {moduleScene,moduleTitle,moduleInstructions,paperRecommendation,fanDashes} from './paper-construction.js';
const $=id=>document.getElementById(id);let g=null,timer=null,scale=1,adaptive=null,manualView=false,automaticSphere=false,initialization=null,layout=null,moduleIndex=0;
const fmt=x=>Number.isFinite(x)?(Math.abs(x)>1e6||Math.abs(x)<1e-5&&x!==0?x.toExponential(8):x.toPrecision(12)):'—';
const colors=()=>Object.fromEntries(['bg','fg','muted','line','blue','orange','green'].map(k=>[k,getComputedStyle(document.documentElement).getPropertyValue('--'+k).trim()]));
// Resolve light-dark() via a real element so canvas gets a concrete color.
const colorProbe=document.createElement('span');colorProbe.hidden=true;document.body.append(colorProbe);
function palette(){const c={};for(const k of ['bg','fg','muted','line','blue','orange','green']){colorProbe.style.color=`var(--${k})`;c[k]=getComputedStyle(colorProbe).color;}return c;}
function setup(canvas){const r=canvas.getBoundingClientRect(),d=devicePixelRatio||1;canvas.width=Math.round(r.width*d);canvas.height=Math.round(r.height*d);const c=canvas.getContext('2d');c.scale(d,d);c.clearRect(0,0,r.width,r.height);c.font='12px system-ui';return [c,r.width,r.height];}
const key=new Set(['O','A','B','C','P','Pnext','Q','V','U','G','Gother','MΓ','F','D','Z','K','M','L1','T','E','Ux','Xs']);
const label=n=>({Pnext:'P⁺',Gother:'G′',L1:'L₁'}[n]||n);
function plane(canvas,detail=false){const [c,w,h]=setup(canvas),co=palette();if(!g||w<80||h<80)return;const stage=+$('stage').value;
 const scene=g.fast&&$('power-display').value!=='full'?moduleScene(g,moduleIndex):null;
 const visiblePoints=scene?.points||g.points,visibleFixed=scene?.fixed||g.fixed,visibleCircles=scene?.circles||g.circles;
 const W=g.W,H=g.H;let xs=[-.25*W,1.25*W],ys=[-.15*H,1.15*H];if(!detail){for(const q of Object.values(visiblePoints)){const a=affine(q);if(a&&a.every(x=>Math.abs(x)<1e7)){xs.push(a[0]);ys.push(a[1]);}}for(const a of visibleCircles){xs.push(a.center[0]-a.radius,a.center[0]+a.radius);ys.push(a.center[1]-a.radius,a.center[1]+a.radius);}}
 if(detail&&$('detail-frame').value==='auto'){
 const P=affine(g.points[scene?.m.input||'P']),Q=affine(g.points[scene?.m.result||'Pnext']),delta=Math.abs(P[1]-Q[1]);
 if(delta>0&&delta<H*.08){const span=Math.max(delta*6,H*1e-8),y=(P[1]+Q[1])/2;xs=[W-span/2,W+span/2];ys=[y-span/2,y+span/2];}
 }
 let lo=Math.min(...xs),hi=Math.max(...xs),bot=Math.min(...ys),top=Math.max(...ys),k=Math.min((w-70)/(hi-lo),(h-60)/(top-bot));
 const cx=(lo+hi)/2,cy=(top+bot)/2,to=(x,y)=>[w/2+(x-cx)*k,h/2-(y-cy)*k];lo=cx-(w/2-18)/k;hi=cx+(w/2-18)/k;bot=cy-(h/2-18)/k;top=cy+(h/2-18)/k;
 function line(l,color,width=1,dash=[]){if(!l)return;const [a,b,d]=l,ends=[];if(Math.abs(b)>1e-13)for(const x of [lo,hi]){const y=-(a*x+d)/b;if(y>=bot-1e-9&&y<=top+1e-9)ends.push([x,y]);}if(Math.abs(a)>1e-13)for(const y of [bot,top]){const x=-(b*y+d)/a;if(x>=lo-1e-9&&x<=hi+1e-9)ends.push([x,y]);}if(ends.length<2)return;c.strokeStyle=color;c.lineWidth=width;c.setLineDash(dash);c.beginPath();c.moveTo(...to(...ends[0]));c.lineTo(...to(...ends.at(-1)));c.stroke();c.setLineDash([]);}
 for(const l of [[1,0,0],[1,0,-g.W],[0,1,0],[0,1,-g.H]])line(l,co.line,1.2);
 for(const o of visibleFixed)line(o.line,co.line,1,[4,4]);
 c.save();c.beginPath();c.rect(12,12,w-24,h-24);c.clip();for(const a of visibleCircles)if(a.stage<=stage){c.strokeStyle=co.orange;c.lineWidth=1.5;c.beginPath();c.arc(...to(...a.center),a.radius*k,0,2*Math.PI);c.stroke();}
 for(let i=scene?scene.m.start:0;i<Math.min(stage,scene?.m.end??stage);i++){const op=g.ops[i];line(op.line,i===stage-1?co.blue:co.muted,i===stage-1?2.2:1.3,op.bank===undefined?(i===stage-1?[]:[2,3]):fanDashes[op.bank]);}c.restore();
 const occupied=[];for(const [n,q]of Object.entries(visiblePoints)){if(g.birth[n]>stage)continue;const a=affine(q);if(!a)continue;const [x,y]=to(...a);if(x<12||x>w-12||y<12||y>h-12)continue;c.fillStyle=n==='Pnext'?co.green:n==='G'||n==='Gother'?co.orange:co.fg;c.beginPath();c.arc(x,y,n==='Pnext'?4.5:2.5,0,Math.PI*2);c.fill();if(!key.has(n)&&!scene?.labels[n]&&!g.banks?.some(b=>b.unit===n)&&!g.ops[stage-1]?.names.includes(n))continue;
 const text=scene?.labels[n]||(g.banks?.find(b=>b.unit===n)?'Fan '+g.banks.find(b=>b.unit===n).name:label(n)),tw=c.measureText(text).width;let place=null;for(const [dx,dy]of [[7,-8],[7,16],[-tw-7,-8],[-tw-7,16],[7,-24]]){const xx=Math.max(4,Math.min(w-tw-4,x+dx)),yy=Math.max(14,Math.min(h-5,y+dy));const box=[xx,yy-12,tw+4,15];if(!occupied.some(b=>box[0]<b[0]+b[2]&&box[0]+box[2]>b[0]&&box[1]<b[1]+b[3]&&box[1]+box[3]>b[1])){place=[xx,yy];occupied.push(box);break;}}
 if(place){c.fillStyle=co.fg;c.fillText(text,...place);}}
 c.fillStyle=co.muted;c.fillText(detail?'Equal x/y scale · independent local frame':'Equal scale on both axes',14,h-6);
}
function sphere(canvas){const [c,w,h]=setup(canvas),co=palette();if(!g||w<80||h<80)return;const stage=+$('stage').value,R=Math.min(w-65,h-65)/2,cx=w/2,cy=h/2,ya=+$('yaw').value*Math.PI/180,pi=+$('pitch').value*Math.PI/180;
 const scene=g.fast&&$('power-display').value!=='full'?moduleScene(g,moduleIndex):null;
 const visiblePoints=scene?.points||g.points;
 const rotate=([x,y,z])=>{const u=x*Math.cos(ya)+z*Math.sin(ya),v=-x*Math.sin(ya)+z*Math.cos(ya);return [u,y*Math.cos(pi)-v*Math.sin(pi),y*Math.sin(pi)+v*Math.cos(pi)];};
 const screen=z=>[cx+R*z[0],cy-R*z[1]];
 c.strokeStyle=co.line;c.beginPath();c.arc(cx,cy,R,0,2*Math.PI);c.stroke();
 function curve(samples,color,width=1){
 const pts=samples.map(rotate);let back=null;c.strokeStyle=color;c.lineWidth=width;
 for(let i=1;i<pts.length;i++){const nextBack=(pts[i][2]+pts[i-1][2])<0;
  if(nextBack!==back){if(back!==null)c.stroke();back=nextBack;c.globalAlpha=back?.3:1;c.setLineDash(back?[3,4]:[]);c.beginPath();c.moveTo(...screen(pts[i-1]));}
  c.lineTo(...screen(pts[i]));
 }
 if(back!==null)c.stroke();c.globalAlpha=1;c.setLineDash([]);
 }
 for(const lat of [-Math.PI/4,0,Math.PI/4])curve(Array.from({length:121},(_,i)=>{const a=2*Math.PI*i/120;return [Math.cos(lat)*Math.cos(a),Math.sin(lat),Math.cos(lat)*Math.sin(a)];}),co.line);
 function line(l,color,width=1){if(l)curve(stereoLineSamples(l,g.W,g.H),color,width);}
 for(const l of [[1,0,0],[1,0,-g.W],[0,1,0],[0,1,-g.H]])line(l,co.line);for(const f of scene?.fixed||g.fixed)line(f.line,co.line);
 for(const a of scene?.circles||g.circles)if(a.stage<=stage)curve(stereoCircleSamples(a.center,a.radius,g.W,g.H),co.orange,1.7);
 for(let i=scene?scene.m.start:0;i<Math.min(stage,scene?.m.end??stage);i++)line(g.ops[i].line,i===stage-1?co.blue:co.muted,i===stage-1?2:1);
 // Reserve the readout points before placing secondary labels. Labels move; points never do.
 const readouts=['P','Pnext'].filter(n=>visiblePoints[n]&&g.birth[n]<=stage).map(n=>{const z=rotate(stereo(g.points[n],g.W,g.H));return {n,z,xy:screen(z)};});
 const occupied=[];for(const [n,q]of Object.entries(visiblePoints)){if(g.birth[n]>stage||(!key.has(n)&&!scene?.labels[n])||['P','Pnext'].includes(n))continue;const z=rotate(stereo(q,g.W,g.H)),[x,y]=screen(z);c.globalAlpha=z[2]<0?.45:1;c.fillStyle=n.startsWith('G')?co.orange:co.fg;c.beginPath();c.arc(x,y,3,0,2*Math.PI);c.fill();if(affine(q)&&!occupied.some(a=>Math.hypot(x-a[0],y-a[1])<24)&&!readouts.some(a=>Math.hypot(x-a.xy[0],y-a.xy[1])<40)){c.fillText(scene?.labels[n]||label(n),Math.min(w-35,x+7),Math.max(14,y-7));occupied.push([x,y]);}}
 c.globalAlpha=1;const N=screen(rotate([0,0,1]));c.fillStyle=co.blue;c.beginPath();c.arc(...N,4,0,2*Math.PI);c.fill();c.fillText('N',N[0]+8,N[1]+17);
 for(const {n,z,xy:[x,y]} of readouts){
  const color=n==='P'?co.blue:co.green,text=label(n),tw=c.measureText(text).width;
  const tx=Math.max(8,Math.min(w-tw-8,x+(x>cx?-45:24))),ty=Math.max(18,Math.min(h-26,y+(n==='P'?-25:33)));
  c.globalAlpha=z[2]<0?.6:1;c.strokeStyle=color;c.fillStyle=color;c.lineWidth=2;
  c.beginPath();c.arc(x,y,n==='P'?6:3.5,0,2*Math.PI);if(n==='P')c.stroke();else c.fill();
  c.globalAlpha=1;c.lineWidth=1;c.setLineDash(z[2]<0?[3,3]:[]);c.beginPath();c.moveTo(x,y);c.lineTo(tx+tw/2,ty-5);c.stroke();c.setLineDash([]);
  c.fillStyle=co.bg;c.fillRect(tx-3,ty-13,tw+6,17);c.fillStyle=color;c.fillText(text,tx,ty);
 }
 c.fillStyle=co.muted;c.fillText('Dashed lines: rear hemisphere',14,h-6);
}
function draw(){$('overview').classList.toggle('sphere-interactive',$('view').value==='sphere'&&!!g);if($('view').value==='sphere')sphere($('overview'));else plane($('overview'));plane($('detail'),true);}
function stage(){if(!g)return;const n=+$('stage').value;
 if(g.fast&&$('power-display').value!=='full'){moduleIndex=Math.max(0,g.modules.findIndex(m=>n<=m.end));updatePaper();}$('stage-number').textContent=`${n} / ${g.ops.length}`;$('step-text').textContent=n?`${g.ops[n-1].kind} · ${g.ops[n-1].label}`:'Fixed setup: rectangle, centers and supports.';$('back').disabled=n===0;$('forward').disabled=n===g.ops.length;draw();}
function stop(){clearInterval(timer);timer=null;$('play').textContent='Play steps';}
function dimensions(){return ['AK','AD','projective','arc'].includes(baseMode($('method').value))?[+$('rect-width').value,+$('rect-height').value]:[2,4];}
function chooseLayout(X=+$('working-target').value,s=+$('state').value){const [W,H]=dimensions();layout=adaptRectangle($('method').value,+$('degree').value,X,s,$('chart').value,W,H,$('power-layout').value);$('rect-width').value=layout.W;$('rect-height').value=layout.H;}
function rebuild(){stop();$('degree').max=['AKfast','ADfast','projectiveFast','arcFast'].includes($('method').value)?1000000:32;
 const adjustable=['AK','AD','projective','arc'].includes(baseMode($('method').value));for(const id of ['rect-width','rect-height','adapt-rectangle','init-band'])$(id).disabled=!adjustable;
 const [W,H]=dimensions();$('layout-status').textContent=`Rectangle: ${fmt(W)} × ${fmt(H)}. `+(layout?`Proportions chosen from ${layout.tested} tested rectangles to balance the overview. `:'')+'Circles are reconstructed, never stretched. Coincident points remain coincident.';
$('initialize').disabled=!['AK','AD','projective','arc','AKfast','ADfast','projectiveFast','arcFast'].includes($('method').value);$('error').hidden=true;$('warning').hidden=true;$('chart-label').hidden=$('method').value!=='circle';try{try{g=construct($('method').value,+$('degree').value,+$('working-target').value,+$('state').value,$('chart').value,W,H,$('power-layout').value);}catch(original){
 if(initialization)throw Error(original.message+' Calibration is preserved; this numerical limit is not an exact geometric degeneracy.');
 let r;try{r=renormalizeOptimal($('method').value,+$('degree').value,+$('working-target').value,+$('state').value,$('chart').value,W,H,$('power-layout').value);}catch(conditioning){throw Error(original.message+' '+conditioning.message);}adaptive=r;scale*=r.c;$('working-target').value=r.X;$('state').value=r.s;g=construct($('method').value,+$('degree').value,r.X,r.s,$('chart').value,W,H,$('power-layout').value);
 }const fallback=needsStereographicView(g);if(fallback&&!manualView){if($('power-display').value==='paper')$('power-display').value='current';$('view').value='sphere';automaticSphere=true;$('rotation').hidden=false;$('drawing-title').textContent='Stereographic image';g.warnings.push(fallback);}
 $('fast-status').textContent=g.fast?`Post-V20 · p = ${g.p}, binary ${g.binary} · ${g.multiplications} multiplications versus ${g.p-1} in the native chain. Automatic sphere: ${automaticSphere?'yes':'no'}.`:'';
 $('stage').max=g.ops.length;moduleIndex=Math.max(0,Math.min(moduleIndex,g.modules.length-1));$('stage').value=g.fast&&$('power-display').value!=='full'?g.modules[Math.max(0,moduleIndex)].end:g.ops.length;updatePaper();
 $('root-value').textContent=fmt(g.root);$('next-value').textContent=fmt(g.value);$('error-value').textContent=(g.value/g.root-1).toExponential(5);
 $('answer').textContent=fmt(1/(scale*($('exploration').checked?g.value:g.s)));$('answer-label').textContent=$('exploration').checked?'Root · next readout in the original units':`Approximation to the degree-${g.p} root of ${document.getElementById('target').value} · step ${initialization?.iterations||0}`;$('answer-note').textContent='Numerical approximation. '+($('exploration').checked?'Manual exploration.':(initialization?.stopped?'The available precision can no longer certify an improvement.':'Automatic setup; each click performs one geometric iteration.'));
 $('protocol').textContent=`${methods[g.mode]} · order ${orders[g.mode]} · ${g.counts.J} joins, ${g.counts.P} parallels, ${g.counts.C} moving arcs. Setup excluded; one parallel here costs 2 joins + 3 arcs.`;
 $('scope').textContent=g.mode==='circle'?'Transverse real branch, selected by R′(v)<0. Proven convergence is local; error decrease over the entire domain remains conjectural. Exclusions and renormalization are described in the paper.':'The scalar map converges globally for positive states. The geometric representation may nevertheless encounter centers at infinity or ill-conditioned configurations.';
 $('check').textContent=`Normalized discrepancy between geometric readout and independent formula: ${g.discrepancy.toExponential(3)}. Residual t = ${fmt(g.t)}.`;
 if(g.warnings.length){$('warning').hidden=false;$('warning').textContent=g.warnings.join(' ');}
 $('iterate').disabled=!!initialization?.stopped;$('play').disabled=false;stage();
 }catch(e){g=null;updatePaper();$('answer').textContent='—';$('answer-note').textContent='';$('fast-status').textContent='';$('error').hidden=false;$('error').textContent=e.message+(!initialization&&!$('initialize').disabled?' Use “Initialize and calibrate” to choose a fresh start.':'');$('iterate').disabled=true;$('play').disabled=true;for(const id of ['root-value','next-value','error-value'])$(id).textContent='—';$('step-text').textContent='Construction unavailable for these parameters.';$('protocol').textContent='';draw();}
 $('scaling').textContent=scale===1?'':`original s = ${fmt(scale)} × normalized s (reciprocal root). Original direct root = normalized direct root / ${fmt(scale)}.`;
 $('initialization-status').hidden=!initialization;
 if(initialization)$('initialization-status').textContent=initialization.paperDemo?`Certified paper start: X = 2000, s = ${initialization.c}; 1/4 ≤ Xs^p ≤ 4 verified by dyadic intervals. Original coordinates retained. Setup excluded from iteration costs.`:`Certified initialization for the requested X ${fmt(initialization.originalX)} : c = ${fmt(initialization.c)} ; ${initializationBands[initialization.band].lower} ≤ Xcᵖ ≤ ${initializationBands[initialization.band].upper} verified by intervals; working X = ${fmt(initialization.X)}, start at 1. ${initialization.comparisons} comparisons, ${initialization.halvings} bisections. Absolute calibration error ≤ 2⁻⁴⁸. Setup excluded from the per-iteration cost. ${initialization.stopped?'Iteration stopped: no certifiable numerical progress; this is not a proof of zero error.':''}`;
 $('adaptive-status').textContent=adaptive?`Adaptive normalization active: c = 2^${adaptive.k} = ${fmt(adaptive.c)} ; ${adaptive.candidateCount}/${adaptive.testedCount} valid candidates ; score at selection ${fmt(adaptive.score)} ; discrepancy ${adaptive.discrepancy.toExponential(3)}. ${adaptive.reason}`:'';
}
for(const id of ['method','degree','working-target','state','chart'])$(id).addEventListener('change',()=>{if(!$('exploration').checked){autoSolve();return;}layout=null;adaptive=null;initialization=null;if(['degree','working-target','state'].includes(id))scale=1;rebuild();});
for(const id of ['rect-width','rect-height'])$(id).onchange=()=>{layout=null;if(initialization)initialization.stopped=false;rebuild();};
$('adapt-rectangle').onclick=()=>{try{chooseLayout();if(initialization)initialization.stopped=false;rebuild();}catch(e){$('error').hidden=false;$('error').textContent=e.message;}};
$('detail-frame').onchange=draw;
$('stage').addEventListener('input',()=>{stop();stage();});$('back').onclick=()=>{stop();$('stage').value=+$('stage').value-1;stage();};$('forward').onclick=()=>{stop();$('stage').value=+$('stage').value+1;stage();};
$('play').onclick=()=>{if(timer){stop();return;}if(+$('stage').value===g.ops.length)$('stage').value=0;$('play').textContent='Pause';stage();timer=setInterval(()=>{if(+$('stage').value>=g.ops.length){stop();return;}$('stage').value=+$('stage').value+1;stage();},650);};
$('iterate').onclick=()=>{if(!g)return;try{if(initialization){const d=iterationDecision(g.p,g.X,g.s,g.value,initialization.band);if(d.stop){initialization.stopped=true;rebuild();return;}}if(initialization)initialization.iterations=(initialization.iterations||0)+1;$('state').value=g.value;rebuild();}catch(e){$('error').hidden=false;$('error').textContent=e.message+(!initialization&&!$('initialize').disabled?' Use “Initialize and calibrate” to choose a fresh start.':'');$('iterate').disabled=true;}};
$('initialize').onclick=()=>{try{const p=+$('degree').value,r=initializeCalibrated(p,+$('working-target').value,$('init-band').value);construct($('method').value,p,r.X,1,$('chart').value,...dimensions(),$('power-layout').value);chooseLayout(r.X,1);initialization=r;adaptive=null;scale*=r.c;$('working-target').value=r.X;$('state').value=1;rebuild();}catch(e){$('error').hidden=false;$('error').textContent=e.message;}};
$('normalize').onclick=()=>{try{const p=+$('degree').value,X=+$('working-target').value,s=+$('state').value;if(!Number.isInteger(p)||p<3||p>1000000||!(X>0&&s>0))throw Error('Invalid parameters.');initialization=null;adaptive=null;const r=renormalize(p,X,s,$('chart').value);scale*=r.c;$('working-target').value=r.X;$('state').value=r.s;rebuild();}catch(e){$('error').hidden=false;$('error').textContent=e.message;}};
$('normalize-optimal').onclick=()=>{try{initialization=null;const r=renormalizeOptimal($('method').value,+$('degree').value,+$('working-target').value,+$('state').value,$('chart').value,...dimensions(),$('power-layout').value);adaptive=r;scale*=r.c;$('working-target').value=r.X;$('state').value=r.s;rebuild();}catch(e){$('error').hidden=false;$('error').textContent=e.message;}};
function example(){moduleIndex=0;layout=null;$('rect-width').value=2;$('rect-height').value=4;scale=1;adaptive=null;initialization=null;manualView=false;automaticSphere=false;$('degree').value=3;$('working-target').value=2;$('state').value=.75;$('chart').value='compact';const ex=$('example').value;if(ex==='near'){$('working-target').value=1.1;$('state').value=.97;}if(['initial','final','outside'].includes(ex)){$('method').value='circle';$('state').value=ex==='initial'?1:ex==='final'?(7.75/2)**(1/3):.1;}rebuild();}
$('example').onchange=example;$('reset').onclick=()=>{$('example').value='base';scale=1;example();};$('view').onchange=()=>{manualView=true;automaticSphere=false;$('rotation').hidden=$('view').value!=='sphere';$('drawing-title').textContent=$('view').value==='sphere'?'Stereographic image':'Overview';draw();};for(const id of ['yaw','pitch'])$(id).oninput=draw;
const cancelSphereDrag=bindSphereDrag($('overview'),$('yaw'),$('pitch'),()=>!!g&&$('view').value==='sphere',draw);
$('view').addEventListener('change',()=>cancelSphereDrag());
new ResizeObserver(draw).observe($('overview'));matchMedia('(prefers-color-scheme: dark)').addEventListener('change',draw);
// Keep preparation controls and internal values inside a closed advanced panel.
for(const el of document.querySelectorAll('.internal-input'))$('internal-controls').append(el);
for(const selector of ['#layout-controls','#layout-status','.toolbar','#research-notice','#initialization-status','#adaptive-status','#fast-status','.readouts','#protocol','details:not(#advanced):not(#paper-metrics)']){
 const el=document.querySelector(selector);if(el)$('advanced').append(el);
}
$('iteration-controls').append($('iterate'));
const preparedModes=['AK','AD','projective','arc','halley','pade','AKfast','ADfast','projectiveFast','arcFast'];
function automaticUI(){
 const manual=$('exploration').checked;document.body.dataset.manual=String(manual);
 for(const option of $('method').options)option.hidden=!manual&&!preparedModes.includes(option.value);
 if(!manual&&!preparedModes.includes($('method').value))$('method').value='AKfast';
}
function autoSolve(){
 if($('exploration').checked){rebuild();return;}
 stop();automaticUI();
 try{
  const p=+$('degree').value,X=+document.getElementById('target').value;
  const limit=['AKfast','ADfast','projectiveFast','arcFast'].includes($('method').value)?1000000:32;$('degree').max=limit;
  if(p>limit)throw Error(`This construction supports p ≤ ${limit}. Choose a smaller degree or a “Fast exponentiation” variant.`);
  if(limit===1000000&&p>32&&$('power-display').value==='full')$('power-display').value='current';
  const r=initializeCalibrated(p,X,'wide');
  // A new original problem always starts with the reference height, avoiding scale drift.
  $('rect-width').value=2;$('rect-height').value=4;layout=null;moduleIndex=0;
  if(['AK','AD','projective','arc'].includes(baseMode($('method').value)))chooseLayout(r.X,1);
  const u=1;
  scale=r.c;initialization={...r,stopped:false,iterations:0};adaptive=null;
  $('working-target').value=r.X;$('state').value=u;rebuild();
 }catch(e){g=null;stop();updatePaper();$('answer').textContent='—';$('answer-note').textContent='';$('error').hidden=false;$('error').textContent=e.message;$('iterate').disabled=true;$('play').disabled=true;for(const canvas of [$('overview'),$('detail')])setup(canvas);}
}
$('calculate').onclick=autoSolve;
document.getElementById('target').onchange=autoSolve;
$('exploration').onchange=()=>{automaticUI();if($('exploration').checked)rebuild();else autoSolve();};
function updatePaper(){
 const fast=!!g?.fast,display=$('power-display').value,modular=fast&&display!=='full';
 $('paper-controls').hidden=!fast;$('paper-metrics').hidden=!fast;$('paper-guide').hidden=!modular;$('module-nav').hidden=!modular;
 document.body.dataset.powerDisplay=fast?display:'full';
 if(!fast)return;
 $('routing-status').textContent=g.powerLayout==='spread'?`Spread routing: best among ${g.banks.length} prepared fan banks.`:'Classic routing: historical single fan.';
 $('power-count').textContent=`${g.multiplications} geometric multiplications instead of ${g.p-1} linear stages. p = ${g.p} = (${g.binary})₂.`;
 const options=g.modules.map((m,i)=>new Option(`${i+1}. ${moduleTitle(g,m)}`,String(i)));
 $('module-select').replaceChildren(...options);$('module-select').value=String(moduleIndex);
 $('module-prev').disabled=moduleIndex<=0;$('module-next').disabled=moduleIndex>=g.modules.length-1;
 const scene=moduleScene(g,moduleIndex),m=scene?.m;
 $('module-heading').textContent=modular?`Module ${moduleIndex+1} of ${g.modules.length} — ${moduleTitle(g,m)}`:'';
 $('overview').dataset.module=modular?String(moduleIndex):'all';
 $('overview').dataset.visibleOperations=String(modular?scene.ops.length:g.ops.length);
 if(modular){
  $('module-instructions').replaceChildren(...moduleInstructions(g,m).map(text=>{const li=document.createElement('li');li.textContent=text;return li;}));
  $('module-coordinates').textContent=`Keep the same coordinates: W/H = ${fmt(g.W/g.H)}. `+(m.bank?`Fan ${m.bank.name}: λ/H = ${fmt(m.bank.ratio)}. `:'')+
   [m.input,m.copy,m.result].filter(Boolean).map(n=>{const xy=affine(g.points[n]);return `${scene.labels[n]||n}: (${xy.map(v=>fmt(v/g.H)).join(', ')}) H`;}).join(' · ');
  $('module-aliases').textContent=scene.metrics.aliases?'Some named points coincide (for example when s = 1); one mark can carry several roles. Tiny distinct gaps are reported below.':'Carry the result on the right rail into the next module. Each page keeps equal x/y scale.';
 }
 const metrics=modular?scene.metrics:paperMetrics(Object.values(g.points),[...g.fixed,...g.ops].map(o=>o.line).concat([[1,0,-g.W],[0,1,-g.H]]),g.H,g.banks.map(b=>g.points[b.unit]).concat(['K','F','G','Z'].filter(n=>g.points[n]).map(n=>g.points[n])),g.circles);
 const metric=(n,u='')=>Number.isFinite(n)?`${n<.01?n.toExponential(2):n.toFixed(2)}${u}`:'No distinct pair';
 const entries=[['Minimum line angle',metric(metrics.minAngle,'°')],['Minimum point separation',metric(metrics.minSeparation,' H')],['Required normalized width',metric(metrics.width,' H')],['Required normalized height',metric(metrics.height,' H')],['Maximum center distance',metric(metrics.maxCenterDistance,' H')],['Near-coincidence / small-angle pairs',String(metrics.quasiCoincidences)]];
 $('paper-measurements').replaceChildren(...entries.flatMap(([name,value])=>{const dt=document.createElement('dt'),dd=document.createElement('dd');dt.textContent=name;dd.textContent=value;return [dt,dd];}));
 $('paper-size').textContent='Suggested paper size: '+paperRecommendation(metrics);
}
function selectModule(index){
 if(!g?.fast)return;stop();moduleIndex=Math.max(0,Math.min(g.modules.length-1,index));$('stage').value=g.modules[moduleIndex].end;stage();
}
$('module-prev').onclick=()=>selectModule(moduleIndex-1);
$('module-next').onclick=()=>selectModule(moduleIndex+1);
$('module-select').onchange=()=>selectModule(+$('module-select').value);
$('power-display').onchange=()=>{
 stop();$('drawing-title').textContent=$('view').value==='sphere'?'Stereographic image':'Overview';if($('power-display').value==='paper'){$('view').value='plane';$('rotation').hidden=true;$('drawing-title').textContent='Paper construction';}if(g?.fast){$('stage').value=$('power-display').value==='full'?g.ops.length:g.modules[Math.max(0,moduleIndex)].end;}
 updatePaper();stage();
};
$('power-layout').onchange=()=>{layout=null;rebuild();};
$('paper-demo').onclick=()=>{
 stop();$('exploration').checked=false;automaticUI();$('advanced').open=false;
 $('method').value='AKfast';$('degree').value=10;$('target').value=2000;$('working-target').value=2000;
 const r=findInitialState(10,2000,'wide');$('state').value=r.c;
 initialization={...r,X:2000,originalX:2000,paperDemo:true,iterations:0,stopped:false};scale=1;adaptive=null;moduleIndex=0;
 $('power-layout').value='spread';$('power-display').value='full';$('rect-width').value=2;$('rect-height').value=4;
 $('view').value='plane';manualView=false;automaticSphere=false;$('rotation').hidden=true;$('drawing-title').textContent='Overview';
 chooseLayout(2000,r.c);rebuild();
};

const methodFromURL=new URLSearchParams(location.search).get('method');
if(methods[methodFromURL]){$('method').value=methodFromURL;if(!preparedModes.includes(methodFromURL)){$('exploration').checked=true;$('advanced').open=true;}}
automaticUI();if($('exploration').checked)rebuild();else autoSolve();
