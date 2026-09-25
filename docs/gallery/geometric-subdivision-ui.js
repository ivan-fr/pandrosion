import {subdivide} from './geometric-subdivision.js';
const $ = id => document.getElementById(id), NS = 'http://www.w3.org/2000/svg';
const fmt = v => Number(v.toPrecision(12)).toString();
function node(svg, tag, attrs, text) { const e = document.createElementNS(NS, tag); for (const [k,v] of Object.entries(attrs)) e.setAttribute(k,v); if(text !== undefined)e.textContent=text; svg.append(e); }
function line(svg,x1,y1,x2,y2,color='var(--blue)'){node(svg,'line',{x1,y1,x2,y2,stroke:color});}
function label(svg,x,y,text){node(svg,'text',{x,y,'text-anchor':'middle'},text);}
function dot(svg,x,y){node(svg,'circle',{cx:x,cy:y,r:4});}
function draw(q) {
  const svg=$('circle'); svg.replaceChildren();
  // Show the inputs to the last completed bisection, or the first available one.
  const t=q.history.at(-1) || {A:q.A,B:q.B,a:q.a,b:q.b,m:.5,M:Math.sqrt(q.X),left:q.theta<=.5};
  const scale=440/(t.A+t.B), split=60+scale*t.A, height=scale*t.M;
  node(svg,'path',{d:'M 60 270 A 220 220 0 0 1 500 270',stroke:'var(--orange)'});
  line(svg,60,270,split,270);line(svg,split,270,500,270,'var(--green)');line(svg,split,270,split,270-height,'var(--orange)');
  for(const [x,y] of [[60,270],[500,270],[split,270],[split,270-height]])dot(svg,x,y);
  label(svg,140,302,`A = ${fmt(t.A)}`);label(svg,420,302,`B = ${fmt(t.B)}`);
  label(svg,280,330,`Height √(AB) = ${fmt(t.M)}`);
  $('step').textContent=q.n ? `Subdivision ${q.n}: midpoint ${fmt(t.m)}. Keep the ${t.left?'left':'right'} half because θ ${t.left?'≤':'>'} ${fmt(t.m)}.` : 'Initial interval [0, 1]. The semicircle shows the first mean, ready to construct.';
  const w=$('weighted');w.replaceChildren();
  line(w,60,55,500,55,'var(--muted)');
  const xt=60+440*q.lambda;dot(w,60,55);dot(w,500,55);dot(w,xt,55);
  label(w,60,30,'a');label(w,500,30,'b');label(w,Math.max(100,Math.min(460,xt)),87,`θ · λ = ${fmt(q.lambda)}`);
  // The vertical rails are proportionate to A and B; their horizontal spacing is auxiliary.
  const lower=$('bound-view').value==='lower';
  const vA=lower?1/q.A:q.A, vB=lower?1/q.B:q.B, vU=(1-q.lambda)*vA+q.lambda*vB;
  const s=150/Math.max(vA,vB), y=285, topA=y-s*vA, topB=y-s*vB, topU=y-s*vU;
  line(w,60,y,500,y,'var(--muted)');line(w,60,y,60,topA);line(w,500,y,500,topB);line(w,60,topA,500,topB,'var(--muted)');line(w,xt,y,xt,topU,'var(--green)');
  label(w,60,topA-14,lower?'1/A':'A');label(w,500,topB-14,lower?'1/B':'B');label(w,280,110,lower?'1/L at fraction λ · then invert':'U at fraction λ');label(w,280,322,'Parallel rails · common length scale');
  $('lengths').textContent=`After ${q.n} subdivisions: A ≈ ${fmt(q.A)}, B ≈ ${fmt(q.B)}. The exponent interval above is magnified to show λ.`;
}
function render(message='') {
  try {
    const q=subdivide(Number($('x').value),Number($('p').value),Number($('n').value));
    $('error').hidden=true;$('depth').value=q.n;$('answer').textContent=`L ≈ ${fmt(q.L)} · U ≈ ${fmt(q.U)}`;
    $('width').textContent=q.width.toExponential(5);$('weight').textContent=fmt(q.lambda);$('interval').textContent=`[${fmt(q.a)}, ${fmt(q.b)}]`;
    $('previous').disabled=q.n===0;$('next').disabled=q.n===24;
    $('status').textContent=message || (q.width<1e-12 ? 'The theoretical gap is approaching browser precision. Displayed endpoints may coincide after rounding.' : `${q.n} geometric means; weighted bounds follow from one fixed set of arithmetic constructions.`);
    draw(q);return q;
  } catch(e) { $('error').textContent=e.message;$('error').hidden=false;$('answer').textContent='—';$('width').textContent='—';$('weight').textContent='—';$('interval').textContent='—';$('circle').replaceChildren();$('weighted').replaceChildren();$('step').textContent='';$('lengths').textContent='';$('status').textContent='Correct the parameters to construct an enclosure.';return null; }
}
for(const id of ['x','p','n','bound-view'])$(id).addEventListener('input',()=>render());
$('previous').onclick=()=>{$('n').value=Math.max(0,Number($('n').value)-1);render();};
$('next').onclick=()=>{$('n').value=Math.min(24,Number($('n').value)+1);render();};
$('reset').onclick=()=>{$('n').value=0;render();};
$('example').onclick=()=>{$('x').value=2;$('p').value=37.5;$('n').value=12;render();};
$('irrational').onclick=()=>{$('p').value=Math.SQRT2;render();};
$('until').onclick=()=>{
  const tolerance=Number($('tolerance').value);
  if(!Number.isFinite(tolerance)||tolerance<1e-12||tolerance>1){$('error').textContent='Use a relative tolerance between 10⁻¹² and 1.';$('error').hidden=false;return;}
  let q=render();if(!q)return;
  while(q.width>tolerance&&q.n<24){q=subdivide(q.X,q.p,q.n+1);}
  $('n').value=q.n;
  render(q.width<=tolerance ? `Computed relative width meets the tolerance after ${q.n} subdivisions. This numerical stopping check is not an interval-arithmetic certificate.` : 'Reached 24 subdivisions. The requested tolerance has not been met.');
};
render();
