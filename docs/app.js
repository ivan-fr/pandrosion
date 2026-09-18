import {construct,methods,orders,affine,point,stereo,renormalize,renormalizeOptimal,needsStereographicView,adaptRectangle,baseMode} from './geometry.js';
import {initializeCalibrated,iterationDecision,initializationBands} from './initialization.js';
const $=id=>document.getElementById(id);let g=null,timer=null,scale=1,adaptive=null,manualView=false,automaticSphere=false,initialization=null,layout=null;
const fmt=x=>Number.isFinite(x)?(Math.abs(x)>1e6||Math.abs(x)<1e-5&&x!==0?x.toExponential(8):x.toPrecision(12)):'—';
const colors=()=>Object.fromEntries(['bg','fg','muted','line','blue','orange','green'].map(k=>[k,getComputedStyle(document.documentElement).getPropertyValue('--'+k).trim()]));
// Resolve light-dark() via a real element so canvas gets a concrete color.
const colorProbe=document.createElement('span');colorProbe.hidden=true;document.body.append(colorProbe);
function palette(){const c={};for(const k of ['bg','fg','muted','line','blue','orange','green']){colorProbe.style.color=`var(--${k})`;c[k]=getComputedStyle(colorProbe).color;}return c;}
function setup(canvas){const r=canvas.getBoundingClientRect(),d=devicePixelRatio||1;canvas.width=Math.round(r.width*d);canvas.height=Math.round(r.height*d);const c=canvas.getContext('2d');c.scale(d,d);c.clearRect(0,0,r.width,r.height);c.font='12px system-ui';return [c,r.width,r.height];}
const key=new Set(['O','A','B','C','P','Pnext','Q','V','U','G','Gother','MΓ','F','D','Z','K','M','L1','T','E','Ux','Xs']);
const label=n=>({Pnext:'P⁺',Gother:'G′',L1:'L₁'}[n]||n);
function plane(canvas,detail=false){const [c,w,h]=setup(canvas),co=palette();if(!g||w<80||h<80)return;const stage=+$('stage').value;
 const W=g.W,H=g.H;let xs=[-.25*W,1.25*W],ys=[-.15*H,1.15*H];if(!detail){for(const q of Object.values(g.points)){const a=affine(q);if(a&&a.every(x=>Math.abs(x)<1e7)){xs.push(a[0]);ys.push(a[1]);}}for(const a of g.circles){xs.push(a.center[0]-a.radius,a.center[0]+a.radius);ys.push(a.center[1]-a.radius,a.center[1]+a.radius);}}
 if(detail&&$('detail-frame').value==='auto'){
 const P=affine(g.points.P),Q=affine(g.points.Pnext),delta=Math.abs(P[1]-Q[1]);
 if(delta>0&&delta<H*.08){const span=Math.max(delta*6,H*1e-8),y=(P[1]+Q[1])/2;xs=[W-span/2,W+span/2];ys=[y-span/2,y+span/2];}
 }
 let lo=Math.min(...xs),hi=Math.max(...xs),bot=Math.min(...ys),top=Math.max(...ys),k=Math.min((w-70)/(hi-lo),(h-60)/(top-bot));
 const cx=(lo+hi)/2,cy=(top+bot)/2,to=(x,y)=>[w/2+(x-cx)*k,h/2-(y-cy)*k];lo=cx-(w/2-18)/k;hi=cx+(w/2-18)/k;bot=cy-(h/2-18)/k;top=cy+(h/2-18)/k;
 function line(l,color,width=1,dash=[]){if(!l)return;const [a,b,d]=l,ends=[];if(Math.abs(b)>1e-13)for(const x of [lo,hi]){const y=-(a*x+d)/b;if(y>=bot-1e-9&&y<=top+1e-9)ends.push([x,y]);}if(Math.abs(a)>1e-13)for(const y of [bot,top]){const x=-(b*y+d)/a;if(x>=lo-1e-9&&x<=hi+1e-9)ends.push([x,y]);}if(ends.length<2)return;c.strokeStyle=color;c.lineWidth=width;c.setLineDash(dash);c.beginPath();c.moveTo(...to(...ends[0]));c.lineTo(...to(...ends.at(-1)));c.stroke();c.setLineDash([]);}
 for(const l of [[1,0,0],[1,0,-g.W],[0,1,0],[0,1,-g.H]])line(l,co.line,1.2);
 for(const o of g.fixed)line(o.line,co.line,1,[4,4]);
 c.save();c.beginPath();c.rect(12,12,w-24,h-24);c.clip();for(const a of g.circles)if(a.stage<=stage){c.strokeStyle=co.orange;c.lineWidth=1.5;c.beginPath();c.arc(...to(...a.center),a.radius*k,0,2*Math.PI);c.stroke();}
 for(let i=0;i<stage;i++)line(g.ops[i].line,i===stage-1?co.blue:co.muted,i===stage-1?2.2:1,i===stage-1?[]:[2,3]);c.restore();
 const occupied=[];for(const [n,q]of Object.entries(g.points)){if(g.birth[n]>stage)continue;const a=affine(q);if(!a)continue;const [x,y]=to(...a);if(x<12||x>w-12||y<12||y>h-12)continue;c.fillStyle=n==='Pnext'?co.green:n==='G'||n==='Gother'?co.orange:co.fg;c.beginPath();c.arc(x,y,n==='Pnext'?4.5:2.5,0,Math.PI*2);c.fill();if(!key.has(n)&&!g.ops[stage-1]?.names.includes(n))continue;
 const text=label(n),tw=c.measureText(text).width;let place=null;for(const [dx,dy]of [[7,-8],[7,16],[-tw-7,-8],[-tw-7,16],[7,-24]]){const xx=Math.max(4,Math.min(w-tw-4,x+dx)),yy=Math.max(14,Math.min(h-5,y+dy));const box=[xx,yy-12,tw+4,15];if(!occupied.some(b=>box[0]<b[0]+b[2]&&box[0]+box[2]>b[0]&&box[1]<b[1]+b[3]&&box[1]+box[3]>b[1])){place=[xx,yy];occupied.push(box);break;}}
 if(place){c.fillStyle=co.fg;c.fillText(text,...place);}}
 c.fillStyle=co.muted;c.fillText(detail?'Même échelle x/y · cadre local indépendant':'Échelle identique sur les deux axes',14,h-6);
}
function sphere(canvas){const [c,w,h]=setup(canvas),co=palette();if(!g||w<80||h<80)return;const stage=+$('stage').value,R=Math.min(w-65,h-65)/2,cx=w/2,cy=h/2,ya=+$('yaw').value*Math.PI/180,pi=+$('pitch').value*Math.PI/180;
 const rotate=([x,y,z])=>{const u=x*Math.cos(ya)+z*Math.sin(ya),v=-x*Math.sin(ya)+z*Math.cos(ya);return [u,y*Math.cos(pi)-v*Math.sin(pi),y*Math.sin(pi)+v*Math.cos(pi)];};
 const screen=z=>[cx+R*z[0],cy-R*z[1]];
 c.strokeStyle=co.line;c.beginPath();c.arc(cx,cy,R,0,2*Math.PI);c.stroke();
 function curve(samples,color,width=1){const pts=samples.map(rotate);for(let i=1;i<pts.length;i++){const back=(pts[i][2]+pts[i-1][2])<0;c.globalAlpha=back?.3:1;c.strokeStyle=color;c.lineWidth=width;c.setLineDash(back?[3,4]:[]);c.beginPath();c.moveTo(...screen(pts[i-1]));c.lineTo(...screen(pts[i]));c.stroke();}c.globalAlpha=1;c.setLineDash([]);}
 for(const lat of [-Math.PI/4,0,Math.PI/4])curve(Array.from({length:121},(_,i)=>{const a=2*Math.PI*i/120;return [Math.cos(lat)*Math.cos(a),Math.sin(lat),Math.cos(lat)*Math.sin(a)];}),co.line);
 function line(l,color,width=1){if(!l)return;const [a,b,d]=l,n=Math.hypot(a,b);if(n<1e-14)return;const base=[-d*a/(n*n),-d*b/(n*n)],dir=[-b/n,a/n];curve(Array.from({length:241},(_,i)=>{const theta=-Math.PI/2+Math.PI*i/240,cs=Math.cos(theta),sn=Math.sin(theta);return stereo([base[0]*cs+dir[0]*sn,base[1]*cs+dir[1]*sn,cs],g.W,g.H);}),color,width);}
 for(const l of [[1,0,0],[1,0,-g.W],[0,1,0],[0,1,-g.H]])line(l,co.line);for(const f of g.fixed)line(f.line,co.line);
 for(const a of g.circles)if(a.stage<=stage)curve(Array.from({length:241},(_,i)=>{const t=2*Math.PI*i/240;return stereo(point(a.center[0]+a.radius*Math.cos(t),a.center[1]+a.radius*Math.sin(t)),g.W,g.H);}),co.orange,1.7);
 for(let i=0;i<stage;i++)line(g.ops[i].line,i===stage-1?co.blue:co.muted,i===stage-1?2:1);
 const occupied=[];for(const [n,q]of Object.entries(g.points)){if(g.birth[n]>stage||!key.has(n))continue;const z=rotate(stereo(q,g.W,g.H)),[x,y]=screen(z);c.globalAlpha=z[2]<0?.45:1;c.fillStyle=n==='Pnext'?co.green:n.startsWith('G')?co.orange:co.fg;c.beginPath();c.arc(x,y,3,0,2*Math.PI);c.fill();if(affine(q)&&!occupied.some(a=>Math.hypot(x-a[0],y-a[1])<24)){c.fillText(label(n),Math.min(w-35,x+7),Math.max(14,y-7));occupied.push([x,y]);}}
 c.globalAlpha=1;const N=screen(rotate([0,0,1]));c.fillStyle=co.blue;c.beginPath();c.arc(...N,4,0,Math.PI*2);c.fill();c.fillText('N',N[0]+8,N[1]+17);
 c.fillStyle=co.muted;c.fillText('Pointillés : hémisphère arrière',14,h-6);
}
function draw(){if($('view').value==='sphere')sphere($('overview'));else plane($('overview'));plane($('detail'),true);}
function stage(){if(!g)return;const n=+$('stage').value;$('stage-number').textContent=`${n} / ${g.ops.length}`;$('step-text').textContent=n?`${g.ops[n-1].kind} · ${g.ops[n-1].label}`:'Préparation fixe : rectangle, centres et supports.';$('back').disabled=n===0;$('forward').disabled=n===g.ops.length;draw();}
function stop(){clearInterval(timer);timer=null;$('play').textContent='Parcourir';}
function dimensions(){return ['AK','AD','projective','arc'].includes(baseMode($('method').value))?[+$('rect-width').value,+$('rect-height').value]:[2,4];}
function chooseLayout(X=+$('working-target').value,s=+$('state').value){const [W,H]=dimensions();layout=adaptRectangle($('method').value,+$('degree').value,X,s,$('chart').value,W,H);$('rect-width').value=layout.W;$('rect-height').value=layout.H;}
function rebuild(){stop();$('degree').max=['AKfast','ADfast','projectiveFast','arcFast'].includes($('method').value)?1000000:32;
 const adjustable=['AK','AD','projective','arc'].includes(baseMode($('method').value));for(const id of ['rect-width','rect-height','adapt-rectangle','init-band'])$(id).disabled=!adjustable;
 const [W,H]=dimensions();$('layout-status').textContent=`Rectangle : ${fmt(W)} × ${fmt(H)}. `+(layout?`Proportions choisies parmi ${layout.tested} rectangles testés pour équilibrer la vue d’ensemble. `:'')+'Les cercles sont reconstruits, jamais étirés. Les points confondus restent confondus.';
$('initialize').disabled=!['AK','AD','projective','arc','AKfast','ADfast','projectiveFast','arcFast'].includes($('method').value);$('error').hidden=true;$('warning').hidden=true;$('chart-label').hidden=$('method').value!=='circle';try{try{g=construct($('method').value,+$('degree').value,+$('working-target').value,+$('state').value,$('chart').value,W,H);}catch(original){
 if(initialization)throw Error(original.message+' La calibration est conservée ; la limite numérique ne constitue pas une dégénérescence exacte.');
 let r;try{r=renormalizeOptimal($('method').value,+$('degree').value,+$('working-target').value,+$('state').value,$('chart').value,W,H);}catch(conditioning){throw Error(original.message+' '+conditioning.message);}adaptive=r;scale*=r.c;$('working-target').value=r.X;$('state').value=r.s;g=construct($('method').value,+$('degree').value,r.X,r.s,$('chart').value,W,H);
 }const fallback=needsStereographicView(g);if(fallback&&!manualView){$('view').value='sphere';automaticSphere=true;$('rotation').hidden=false;$('drawing-title').textContent='Image stéréographique';g.warnings.push(fallback);}
 $('fast-status').textContent=g.fast?`Post-V20 · p = ${g.p}, binaire ${g.binary} · ${g.multiplications} multiplications contre ${g.p-1} dans la chaîne native. Sphère automatique : ${automaticSphere?'oui':'non'}.`:'';
 $('stage').max=g.ops.length;$('stage').value=g.ops.length;
 $('root-value').textContent=fmt(g.root);$('next-value').textContent=fmt(g.value);$('error-value').textContent=(g.value/g.root-1).toExponential(5);
 $('answer').textContent=fmt(1/(scale*($('exploration').checked?g.value:g.s)));$('answer-label').textContent=$('exploration').checked?'Racine · lecture suivante dans les unités d’origine':`Approximation de la racine ${g.p}-ième de ${document.getElementById('target').value} · étape ${initialization?.iterations||0}`;$('answer-note').textContent='Approximation numérique. '+($('exploration').checked?'Exploration manuelle.':(initialization?.stopped?'La précision disponible ne permet plus de certifier une amélioration.':'Préparation automatique ; chaque clic effectue une seule itération géométrique.'));
 $('protocol').textContent=`${methods[g.mode]} · ordre ${orders[g.mode]} · ${g.counts.J} joins, ${g.counts.P} parallèles, ${g.counts.C} arc mobile. Préparation exclue ; une parallèle vaut ici 2 joins + 3 arcs.`;
 $('scope').textContent=g.mode==='circle'?'Branche réelle transverse, choisie par R′(v)<0. La convergence prouvée est locale ; la diminution de l’erreur sur tout le domaine reste conjecturale. Les exclusions et la renormalisation sont données dans le papier.':'La carte scalaire converge globalement sur les états positifs. La représentation géométrique peut néanmoins rencontrer des centres à l’infini ou des configurations mal conditionnées.';
 $('check').textContent=`Écart normalisé entre lecture géométrique et formule indépendante : ${g.discrepancy.toExponential(3)}. Résidu t = ${fmt(g.t)}.`;
 if(g.warnings.length){$('warning').hidden=false;$('warning').textContent=g.warnings.join(' ');}
 $('iterate').disabled=!!initialization?.stopped;$('play').disabled=false;stage();
 }catch(e){g=null;$('answer').textContent='—';$('answer-note').textContent='';$('fast-status').textContent='';$('error').hidden=false;$('error').textContent=e.message+(!initialization&&!$('initialize').disabled?' Utiliser « Initialiser et calibrer » pour choisir un nouveau départ.':'');$('iterate').disabled=true;$('play').disabled=true;for(const id of ['root-value','next-value','error-value'])$(id).textContent='—';$('step-text').textContent='Construction indisponible pour ces paramètres.';$('protocol').textContent='';draw();}
 $('scaling').textContent=scale===1?'':`s original = ${fmt(scale)} × s normalisé (racine réciproque). Racine directe originale = racine directe normalisée / ${fmt(scale)}.`;
 $('initialization-status').hidden=!initialization;
 if(initialization)$('initialization-status').textContent=`Initialisation certifiée du X demandé ${fmt(initialization.originalX)} : c = ${fmt(initialization.c)} ; ${initializationBands[initialization.band].lower} ≤ Xcᵖ ≤ ${initializationBands[initialization.band].upper} vérifié par intervalles ; X de travail = ${fmt(initialization.X)}, départ 1. ${initialization.comparisons} comparaisons, ${initialization.halvings} bissections. Erreur absolue de calibration ≤ 2⁻⁴⁸. Préparation exclue du coût mobile. ${initialization.stopped?'Itération arrêtée : aucun progrès numérique certifiable ; ce n’est pas une preuve d’erreur nulle.':''}`;
 $('adaptive-status').textContent=adaptive?`Adaptative active : c = 2^${adaptive.k} = ${fmt(adaptive.c)} ; ${adaptive.candidateCount}/${adaptive.testedCount} candidats valides ; score à la sélection ${fmt(adaptive.score)} ; écart ${adaptive.discrepancy.toExponential(3)}. ${adaptive.reason}`:'';
}
for(const id of ['method','degree','working-target','state','chart'])$(id).addEventListener('change',()=>{if(!$('exploration').checked){autoSolve();return;}layout=null;adaptive=null;initialization=null;if(['degree','working-target','state'].includes(id))scale=1;rebuild();});
for(const id of ['rect-width','rect-height'])$(id).onchange=()=>{layout=null;if(initialization)initialization.stopped=false;rebuild();};
$('adapt-rectangle').onclick=()=>{try{chooseLayout();if(initialization)initialization.stopped=false;rebuild();}catch(e){$('error').hidden=false;$('error').textContent=e.message;}};
$('detail-frame').onchange=draw;
$('stage').addEventListener('input',()=>{stop();stage();});$('back').onclick=()=>{stop();$('stage').value=+$('stage').value-1;stage();};$('forward').onclick=()=>{stop();$('stage').value=+$('stage').value+1;stage();};
$('play').onclick=()=>{if(timer){stop();return;}if(+$('stage').value===g.ops.length)$('stage').value=0;$('play').textContent='Pause';stage();timer=setInterval(()=>{if(+$('stage').value>=g.ops.length){stop();return;}$('stage').value=+$('stage').value+1;stage();},650);};
$('iterate').onclick=()=>{if(!g)return;try{if(initialization){const d=iterationDecision(g.p,g.X,g.s,g.value,initialization.band);if(d.stop){initialization.stopped=true;rebuild();return;}}if(initialization)initialization.iterations=(initialization.iterations||0)+1;$('state').value=g.value;rebuild();}catch(e){$('error').hidden=false;$('error').textContent=e.message+(!initialization&&!$('initialize').disabled?' Utiliser « Initialiser et calibrer » pour choisir un nouveau départ.':'');$('iterate').disabled=true;}};
$('initialize').onclick=()=>{try{const p=+$('degree').value,r=initializeCalibrated(p,+$('working-target').value,$('init-band').value);construct($('method').value,p,r.X,1,$('chart').value,...dimensions());chooseLayout(r.X,1);initialization=r;adaptive=null;scale*=r.c;$('working-target').value=r.X;$('state').value=1;rebuild();}catch(e){$('error').hidden=false;$('error').textContent=e.message;}};
$('normalize').onclick=()=>{try{const p=+$('degree').value,X=+$('working-target').value,s=+$('state').value;if(!Number.isInteger(p)||p<3||p>1000000||!(X>0&&s>0))throw Error('Paramètres invalides.');initialization=null;adaptive=null;const r=renormalize(p,X,s,$('chart').value);scale*=r.c;$('working-target').value=r.X;$('state').value=r.s;rebuild();}catch(e){$('error').hidden=false;$('error').textContent=e.message;}};
$('normalize-optimal').onclick=()=>{try{initialization=null;const r=renormalizeOptimal($('method').value,+$('degree').value,+$('working-target').value,+$('state').value,$('chart').value,...dimensions());adaptive=r;scale*=r.c;$('working-target').value=r.X;$('state').value=r.s;rebuild();}catch(e){$('error').hidden=false;$('error').textContent=e.message;}};
function example(){layout=null;$('rect-width').value=2;$('rect-height').value=4;scale=1;adaptive=null;initialization=null;manualView=false;automaticSphere=false;$('degree').value=3;$('working-target').value=2;$('state').value=.75;$('chart').value='compact';const ex=$('example').value;if(ex==='near'){$('working-target').value=1.1;$('state').value=.97;}if(['initial','final','outside'].includes(ex)){$('method').value='circle';$('state').value=ex==='initial'?1:ex==='final'?(7.75/2)**(1/3):.1;}rebuild();}
$('example').onchange=example;$('reset').onclick=()=>{$('example').value='base';scale=1;example();};$('view').onchange=()=>{manualView=true;automaticSphere=false;$('rotation').hidden=$('view').value!=='sphere';$('drawing-title').textContent=$('view').value==='sphere'?'Image stéréographique':'Vue d’ensemble';draw();};for(const id of ['yaw','pitch'])$(id).oninput=draw;
new ResizeObserver(draw).observe($('overview'));matchMedia('(prefers-color-scheme: dark)').addEventListener('change',draw);
// Keep preparation controls and internal values inside a closed advanced panel.
for(const el of document.querySelectorAll('.internal-input'))$('internal-controls').append(el);
for(const selector of ['#layout-controls','#layout-status','.toolbar','#research-notice','#initialization-status','#adaptive-status','#fast-status','.readouts','#protocol','details:not(#advanced)']){
 const el=document.querySelector(selector);if(el)$('advanced').append(el);
}
$('iteration-controls').append($('iterate'));
const preparedModes=['AK','AD','projective','arc','AKfast','ADfast','projectiveFast','arcFast'];
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
  if(p>limit)throw Error(`Cette construction accepte p ≤ ${limit}. Choisir un degré plus petit ou une variante « Expo rapide ».`);
  const r=initializeCalibrated(p,X,'wide');
  // A new original problem always starts with the reference height, avoiding scale drift.
  $('rect-width').value=2;$('rect-height').value=4;chooseLayout(r.X,1);
  const u=1;
  scale=r.c;initialization={...r,stopped:false,iterations:0};adaptive=null;
  $('working-target').value=r.X;$('state').value=u;rebuild();
 }catch(e){g=null;stop();$('answer').textContent='—';$('answer-note').textContent='';$('error').hidden=false;$('error').textContent=e.message;$('iterate').disabled=true;$('play').disabled=true;for(const canvas of [$('overview'),$('detail')])setup(canvas);}
}
$('calculate').onclick=autoSolve;
document.getElementById('target').onchange=autoSolve;
$('exploration').onchange=()=>{automaticUI();if($('exploration').checked)rebuild();else autoSolve();};
const methodFromURL=new URLSearchParams(location.search).get('method');
if(methods[methodFromURL]){$('method').value=methodFromURL;if(!preparedModes.includes(methodFromURL)){$('exploration').checked=true;$('advanced').open=true;}}
automaticUI();if($('exploration').checked)rebuild();else autoSolve();
