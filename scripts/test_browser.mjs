import { chromium } from 'playwright';
import fs from 'node:fs';
const output=process.env.PREVIEW_OUTPUT || '.ci/browser';
fs.mkdirSync(output,{recursive:true});
(async()=>{const b=await chromium.launch({...(process.env.PLAYWRIGHT_CHANNEL ? {channel:process.env.PLAYWRIGHT_CHANNEL}:{}),headless:true});const page=await b.newPage({viewport:{width:1280,height:1000}});const errors=[];page.on('pageerror',e=>errors.push(page.url()+': '+e.message));await page.addInitScript(()=>{
 const proto=CanvasRenderingContext2D.prototype,fill=proto.fillText,clear=proto.clearRect,stroke=proto.stroke,paths=new WeakMap();
 proto.clearRect=function(...args){if(this.canvas.id==='overview'){this.canvas.dataset.drawnLabels='[]';this.canvas.dataset.strokeCount='0';this.canvas.drawing={strokes:[],boxes:[],marks:[],texts:[]};}return clear.apply(this,args);};
 for(const name of ['beginPath','moveTo','lineTo','arc']){const original=proto[name];proto[name]=function(...args){if(name==='beginPath')paths.set(this,[]);else paths.get(this)?.push([name,...args]);return original.apply(this,args);};}
 proto.stroke=function(...args){if(this.canvas.id==='overview'){this.canvas.dataset.strokeCount=String(Number(this.canvas.dataset.strokeCount||0)+1);this.canvas.drawing?.strokes.push([...(paths.get(this)||[])]);}return stroke.apply(this,args);};
 const fillPath=proto.fill,fillRect=proto.fillRect;
 proto.fill=function(...args){if(this.canvas.id==='overview')for(const p of paths.get(this)||[])if(p[0]==='arc')this.canvas.drawing?.marks.push(p.slice(1,3));return fillPath.apply(this,args);};
 proto.fillRect=function(...args){if(this.canvas.id==='overview')this.canvas.drawing?.boxes.push(args);return fillRect.apply(this,args);};
 proto.fillText=function(text,...args){if(this.canvas.id==='overview'){const labels=JSON.parse(this.canvas.dataset.drawnLabels||'[]');labels.push(text);this.canvas.dataset.drawnLabels=JSON.stringify(labels);this.canvas.drawing?.texts.push({text,x:args[0],y:args[1],width:this.measureText(text).width});}return fill.call(this,text,...args);};
});await page.goto(process.env.PREVIEW_URL || 'http://127.0.0.1:8765/');await page.waitForFunction(()=>document.getElementById('next-value').textContent!=='—');
// Check the actual canvas strokes, not a count reported by the application.
async function checkPointLeaders(required){
 await page.waitForFunction(()=>{const c=document.getElementById('overview'),r=c.getBoundingClientRect();return c.width===Math.round(r.width*devicePixelRatio)&&c.height===Math.round(r.height*devicePixelRatio);});
 const result=await page.locator('#overview').evaluate(canvas=>{
  const {texts,boxes,strokes,marks}=canvas.drawing,near=(a,b)=>Math.abs(a-b)<1e-6;
  const labels=texts.filter(t=>!t.text.startsWith('Equal ')).map(t=>{
   const box=boxes.find(([x,y,w,h])=>t.x>=x&&t.x+t.width<=x+w&&t.y>=y&&t.y<=y+h);
   if(!box)throw Error('Label has no readable background: '+t.text);
   const [x,y,w,h]=box;
   const leaders=strokes.filter(p=>p.length===2&&p[0][0]==='moveTo'&&p[1][0]==='lineTo'&&
    marks.some(m=>near(m[0],p[0][1])&&near(m[1],p[0][2]))&&
    p[1][1]>=x-1e-6&&p[1][1]<=x+w+1e-6&&p[1][2]>=y-1e-6&&p[1][2]<=y+h+1e-6&&
    (near(p[1][1],x)||near(p[1][1],x+w)||near(p[1][2],y)||near(p[1][2],y+h)));
   if(leaders.length!==1)throw Error('Ambiguous or missing leader: '+t.text);
   return {...t,box,anchor:leaders[0][0].slice(1)};
  });
  const {width,height}=canvas.getBoundingClientRect();
  for(let i=0;i<labels.length;i++){
   const [x,y,w,h]=labels[i].box;
   if(x<0||x+w>width||y<0||y+h>height-20)throw Error('Clipped annotation: '+labels[i].text);
   for(const p of labels.slice(i+1)){const [xx,yy,ww,hh]=p.box;if(x<xx+ww&&x+w>xx&&y<yy+hh&&y+h>yy)throw Error('Overlapping annotations');}
  }
  return {labels,constructionStrokes:strokes.length-labels.length};
 });
 for(const text of required)if(!result.labels.some(p=>p.text===text))throw Error('Missing point callout: '+text);
 return result;
}
// Regression: the decentered arc must render smoothly with automatically selected proportions.
await page.selectOption('#method','arc');await page.selectOption('#view','sphere');
let drawn=JSON.parse(await page.locator('#overview').getAttribute('data-drawn-labels'));if(!drawn.includes('P')||!drawn.includes('P⁺'))throw Error('Missing priority readout labels');
await page.locator('#stage').fill('0');await page.locator('#stage').dispatchEvent('input');drawn=JSON.parse(await page.locator('#overview').getAttribute('data-drawn-labels'));if(!drawn.includes('P')||drawn.includes('P⁺'))throw Error('Readout labels ignore construction stage');
await page.locator('#stage').fill(await page.locator('#stage').getAttribute('max'));await page.locator('#stage').dispatchEvent('input');
await page.screenshot({path:`${output}/decentered-sphere.png`,fullPage:true});
await page.locator('#yaw').fill('65');await page.locator('#yaw').dispatchEvent('input');await page.locator('#pitch').fill('-35');await page.locator('#pitch').dispatchEvent('input');
await page.screenshot({path:`${output}/decentered-sphere-rotated.png`,fullPage:true});
await page.selectOption('#method','AKfast');await page.selectOption('#view','plane');
// Automatic preparation only: no hidden iteration, unchanged original input, one click = one step.
await page.locator('#degree').fill('1000000');await page.locator('#target').fill('500000');await page.locator('#target').dispatchEvent('change');
if(await page.locator('#error').isVisible())throw Error('Automatic preparation failed');
if(await page.locator('#power-display').inputValue()!=='current')throw Error('Large degree should default to one module');
if(await page.locator('#advanced').getAttribute('open')!==null)throw Error('Advanced controls exposed');
if(await page.locator('#state').inputValue()!=='1')throw Error('Unexpected automatic iteration');
await page.waitForTimeout(300);if(await page.locator('#state').inputValue()!=='1')throw Error('Background solver must not run');
for(const mode of ['AKfast','ADfast','projectiveFast','arcFast']){
 await page.selectOption('#method',mode);if(await page.locator('#state').inputValue()!=='1')throw Error('New method did not prepare step zero');
 await page.click('#iterate');if(!(await page.locator('#answer-label').innerText()).includes('step 1'))throw Error('One click must be one iteration');
 if(await page.locator('#target').inputValue()!=='500000')throw Error('Original target mutated');
 for(let i=0;i<15&&!await page.locator('#iterate').isDisabled();i++)await page.click('#iterate');
 if(await page.locator('#error').isVisible())throw Error('Automatic orbit failed');
 const answer=Number(await page.locator('#answer').textContent());if(Math.abs(answer/Math.exp(Math.log(500000)/1000000)-1)>2e-11)throw Error('Wrong original-unit root');
}
await page.selectOption('#method','AKfast');await page.click('#iterate');await page.screenshot({path:`${output}/simple-wide.png`,fullPage:true});
await page.setViewportSize({width:360,height:900});await page.screenshot({path:`${output}/simple-mobile.png`,fullPage:true});if(await page.evaluate(()=>document.documentElement.scrollWidth>innerWidth+1))throw Error('Simple mobile overflow');await page.setViewportSize({width:1280,height:1000});
// Original constructions are available with automatic preparation and their native degree limit.
for(const mode of ['AK','AD','projective','arc']){
 await page.locator('#degree').fill('32');await page.selectOption('#method',mode);
 if(await page.locator('#method').inputValue()!==mode)throw Error('Original method replaced');
 if(await page.locator('#error').isVisible())throw Error('Original preparation failed: '+mode);
 if(await page.locator('#degree').getAttribute('max')!=='32')throw Error('Missing native degree limit');
 if(await page.locator('#advanced').getAttribute('open')!==null)throw Error('Original requires advanced mode');
 if(await page.locator('#state').inputValue()!=='1')throw Error('Original auto-iterated');
 await page.click('#iterate');if(!(await page.locator('#answer-label').innerText()).includes('step 1'))throw Error('Original iteration failed');
 if(await page.locator('#target').inputValue()!=='500000')throw Error('Original target changed');
 await page.locator('#degree').fill('33');await page.locator('#degree').dispatchEvent('change');
 if(!await page.locator('#error').isVisible()||!await page.locator('#iterate').isDisabled())throw Error('Native degree limit not enforced');
}
await page.locator('#degree').fill('1000000');await page.selectOption('#method','AKfast');
if(await page.locator('#degree').getAttribute('max')!=='1000000'||await page.locator('#error').isVisible())throw Error('Fast degree limit not restored');
// Restored pencil methods use automatic calibration and keep the original pencil geometry.
for(const mode of ['halley','pade'])for(const p of [3,7,16]){
 await page.locator('#degree').fill(String(p));await page.selectOption('#method',mode);await page.locator('#degree').dispatchEvent('change');
 if(await page.locator('#method').inputValue()!==mode||await page.locator('#error').isVisible())throw Error('Pencil preparation failed: '+mode+' '+p);
 if(await page.locator('#state').inputValue()!=='1'||await page.locator('#advanced').getAttribute('open')!==null)throw Error('Pencil workflow is not simple preparation');
 if(await page.locator('#degree').getAttribute('max')!=='32')throw Error('Pencil degree limit missing');
 await page.click('#iterate');if(!(await page.locator('#answer-label').innerText()).includes('step 1'))throw Error('Pencil manual step failed');
 if(await page.locator('#target').inputValue()!=='500000')throw Error('Pencil changed original X');
 await page.locator('#degree').fill('33');await page.locator('#degree').dispatchEvent('change');if(!await page.locator('#error').isVisible())throw Error('Pencil degree limit ignored');
}
await page.locator('#degree').fill('3');await page.selectOption('#method','AKfast');
await page.locator('#advanced > summary').click();await page.locator('#exploration').check();await page.click('#reset');
for(const mode of ['AK','AD','projective','arc','halley','pade','circle','AKfast','ADfast','projectiveFast','arcFast']){await page.selectOption('#method',mode);if(await page.locator('#error').isVisible())throw Error(mode+': '+await page.locator('#error').innerText());await page.locator('#stage').fill('0');await page.locator('#stage').dispatchEvent('input');await page.click('#forward');await page.click('#iterate');await page.click('#reset');}
await page.selectOption('#method','circle');await page.selectOption('#chart','uniform');await page.screenshot({path:`${output}/gallery-uniform.png`,fullPage:true});await page.selectOption('#chart','compact');await page.selectOption('#view','sphere');await page.locator('#yaw').fill('50');await page.locator('#yaw').dispatchEvent('input');await page.screenshot({path:`${output}/gallery-sphere.png`,fullPage:true});
await page.selectOption('#example','initial');if(!await page.locator('#warning').isVisible())throw Error('Missing infinity warning');if(await page.locator('#view').inputValue()!=='sphere')throw Error('No automatic sphere');await page.selectOption('#view','plane');await page.click('#iterate');if(await page.locator('#view').inputValue()!=='plane')throw Error('Manual view overridden');await page.selectOption('#example','outside');if(!await page.locator('#error').isVisible())throw Error('Missing domain error');await page.click('#reset');await page.click('#normalize');if(await page.locator('#error').isVisible())throw Error('Normalization failed');
await page.selectOption('#method','AKfast');await page.locator('#degree').fill('1024');await page.locator('#state').fill(String(Math.exp(Math.log(.4)/1024)));await page.locator('#state').dispatchEvent('change');if(await page.locator('#error').isVisible())throw Error('Large degree failed');if(!(await page.locator('#fast-status').innerText()).includes('10 multiplications versus 1023'))throw Error('Wrong binary count');await page.click('#normalize-optimal');if(await page.locator('#error').isVisible())throw Error('Adaptive failed');if(!(await page.locator('#adaptive-status').innerText()).includes('score'))throw Error('Missing metadata');
await page.emulateMedia({colorScheme:'dark'});await page.screenshot({path:`${output}/binary-dark.png`,fullPage:true});await page.emulateMedia({colorScheme:'light'});await page.screenshot({path:`${output}/binary-light.png`,fullPage:true});
// Recover an arbitrary unusable state through explicit initialization (not a silent restart).
await page.selectOption('#method','AKfast');await page.locator('#degree').fill('1000000');await page.locator('#working-target').fill('500000');await page.locator('#state').fill('.75');await page.locator('#state').dispatchEvent('change');if(!await page.locator('#error').isVisible())throw Error('Expected unusable starting state');
await page.click('#initialize');if(await page.locator('#error').isVisible())throw Error('Initialization failed');if(!await page.locator('#initialization-status').isVisible())throw Error('Missing initialization certificate');
const calibrated=Number(await page.locator('#working-target').inputValue());if(calibrated<.25||calibrated>4)throw Error('Unbounded calibrated X');
for(let i=0;i<12&&!await page.locator('#iterate').isDisabled();i++)await page.click('#iterate');
if(await page.locator('#error').isVisible())throw Error('Initialized iteration failed');if(!await page.locator('#iterate').isDisabled())throw Error('Missing precision stop');
await page.screenshot({path:`${output}/initialized-million.png`,fullPage:true});
await page.locator('#rect-width').fill('8');await page.locator('#rect-width').dispatchEvent('change');if(await page.locator('#error').isVisible())throw Error('Manual rectangle failed');await page.click('#adapt-rectangle');if(await page.locator('#error').isVisible())throw Error('Rectangle adaptation failed');
await page.setViewportSize({width:360,height:900});await page.screenshot({path:`${output}/gallery-mobile.png`,fullPage:true});const overflow=await page.evaluate(()=>document.documentElement.scrollWidth>innerWidth+1);if(overflow)throw Error('Mobile overflow');
// Prepared fans and paginated paper construction are available without advanced controls.
await page.setViewportSize({width:1280,height:1100});
await page.click('#paper-demo');
if(await page.locator('#error').isVisible())throw Error('Paper demo failed');
if(await page.locator('#exploration').isChecked()||await page.locator('#advanced').getAttribute('open')!==null)throw Error('Paper demo is not in the simple gallery');
if(await page.locator('#target').inputValue()!=='2000'||await page.locator('#working-target').inputValue()!=='2000'||await page.locator('#degree').inputValue()!=='10')throw Error('Paper demo parameters changed');
if(await page.locator('#state').inputValue()!=='0.4375')throw Error('Paper demo must use certified initialization');
if(await page.locator('#view').inputValue()!=='plane')throw Error('Spread demo incorrectly switched to sphere');
if(!(await page.locator('#routing-status').textContent()).includes('best among 3 prepared fan banks'))throw Error('Missing routing scope');
const headings=await page.locator('#module-select option').allTextContents();
if(headings.length!==5||!headings[2].includes('s^4 → s^5')||!headings[4].includes('AK correction'))throw Error('Wrong paper schedule');
const shot=async name=>{await page.locator('#paper-controls').evaluate(el=>el.scrollIntoView({block:'start'}));await page.screenshot({path:`${output}/${name}.png`});};
await shot('paper-p10-x2000-full');
const originalNext=await page.locator('#next-value').textContent();
await page.selectOption('#power-display','current');await page.selectOption('#module-select','2');
if(await page.locator('#overview').getAttribute('data-visible-operations')!=='3')throw Error('Current module contains prior strokes');
if((await checkPointLeaders(['P · s','Fan B'])).constructionStrokes>8)throw Error('Prior lines actually rendered in module');
drawn=JSON.parse(await page.locator('#overview').getAttribute('data-drawn-labels'));
if(!drawn.includes('P · s')||!drawn.includes('Fan B')||drawn.includes('K'))throw Error('Wrong module inputs/center');
await shot('paper-p10-x2000-module');
await page.click('#module-next');if(!(await page.locator('#module-heading').textContent()).includes('s^5 → s^10'))throw Error('Next module failed');
await page.click('#module-next');if(!(await page.locator('#module-heading').textContent()).includes('AK correction')||!await page.locator('#module-next').isDisabled())throw Error('Missing final correction');
await page.click('#module-prev');await page.click('#module-prev');
await page.selectOption('#power-display','paper');
if(await page.locator('.detail').isVisible())throw Error('Paper module not isolated');
if((await page.locator('#module-instructions li').count())!==4)throw Error('Missing paper instructions');
await shot('paper-p10-x2000-paper');
if(await page.locator('#next-value').textContent()!==originalNext)throw Error('Display change mutated readout');
await page.selectOption('#power-layout','classic');
if(await page.locator('#error').isVisible()||Math.abs(Number(await page.locator('#next-value').textContent())-Number(originalNext))>2e-7)throw Error('Classic layout regression');
await page.selectOption('#power-layout','spread');
// Exact module pages stay interactive for every support at the largest supported degree.
await page.locator('#degree').fill('1000000');await page.locator('#target').fill('500000');await page.locator('#target').dispatchEvent('change');
await page.locator('#target').blur();await page.selectOption('#power-display','current');
for(const mode of ['AKfast','ADfast','projectiveFast','arcFast']){
 await page.selectOption('#method',mode);
 if(await page.locator('#error').isVisible()||await page.locator('#view').inputValue()!=='plane')throw Error('Million-degree spread construction failed: '+mode);
 if(!(await page.locator('#power-count').textContent()).includes('25 geometric multiplications instead of 999999 linear stages.'))throw Error('Wrong million count');
 if(await page.locator('#module-select option').count()!==26)throw Error('Missing million modules');
 await page.selectOption('#module-select','24');await page.click('#module-next');
 if(!(await page.locator('#module-heading').textContent()).includes('correction'))throw Error('Million correction inaccessible');
 await checkPointLeaders(['B = P = E · s = 1','Next state P+']);
 await page.click('#module-prev');await page.click('#iterate');
 if(await page.locator('#error').isVisible())throw Error('Million interaction failed');
}
await page.selectOption('#method','AKfast');await page.selectOption('#module-select','12');
await shot('paper-million-current-module');
if(await page.locator('#module-status').getAttribute('data-kind')!=='identity')throw Error('Exact s=1 must be identified algebraically');
if(await page.locator('#overview').getAttribute('data-visible-operations')!=='0')throw Error('Identity must not ask for redundant operations');
drawn=JSON.parse(await page.locator('#overview').getAttribute('data-drawn-labels'));
if(!drawn.some(label=>label.includes('= upper copy')))throw Error('Exact fan alias is not merged');
await page.click('#skip-power');
if(!(await page.locator('#module-heading').textContent()).includes('correction'))throw Error('Identity shortcut did not reach correction');
await page.click('#iterate');await page.selectOption('#module-select','0');
if(await page.locator('#module-status').getAttribute('data-kind')==='identity'||!await page.locator('#skip-power').isHidden())throw Error('Near 1 must never be classified as exactly 1');
if(!['too-close','unresolved'].includes(await page.locator('#module-status').getAttribute('data-kind')))throw Error('Tiny distinct paper gap not explained');
await shot('paper-million-small-gap');
for(const display of ['full','current','paper']){
 await page.selectOption('#power-display',display);await page.setViewportSize({width:360,height:900});
 if(await page.evaluate(()=>document.documentElement.scrollWidth>innerWidth+1))throw Error('Paper mobile overflow: '+display);
 if(display!=='full'){await page.click('#module-next');await page.click('#module-prev');}
}
await page.screenshot({path:`${output}/paper-mobile.png`,fullPage:true});
// Regression from the reported screenshot: K, B, E and s share a very small area.
await page.setViewportSize({width:1280,height:1100});
await page.locator('#degree').fill('10');await page.locator('#target').fill('2000');await page.click('#calculate');
await page.selectOption('#power-display','current');await page.selectOption('#module-select','4');
const correctionReadout=await page.locator('#next-value').textContent();
const expected=['K','B = P = E · s = 1','Next state P+'];
const callouts=await checkPointLeaders(expected),byName=name=>callouts.labels.find(p=>p.text===name).anchor;
const shared=byName('B = P = E · s = 1');
if(!(byName('K')[0]<shared[0]&&byName('Next state P+')[1]>shared[1]))throw Error('Correction callouts point to the wrong location');
if(callouts.labels.some(p=>['B','P · s','E · s^10'].includes(p.text)))throw Error('Exact aliases have redundant labels');
if(await page.locator('#module-status').getAttribute('data-kind')!=='shared-state')throw Error('Missing explanation of B = P = E');
await page.locator('#overview').screenshot({path:`${output}/correction-label-leaders.png`});
await page.emulateMedia({colorScheme:'dark'});await checkPointLeaders(expected);
await page.locator('#overview').screenshot({path:`${output}/correction-label-leaders-dark.png`});await page.emulateMedia({colorScheme:'light'});
await page.setViewportSize({width:360,height:900});await checkPointLeaders(expected);
await page.locator('#overview').screenshot({path:`${output}/correction-label-leaders-mobile.png`});
await page.locator('#stage').fill('0');await page.locator('#stage').dispatchEvent('input');
drawn=JSON.parse(await page.locator('#overview').getAttribute('data-drawn-labels'));
if(drawn.some(t=>t.includes('= E')||t.startsWith('E ·'))||drawn.includes('Next state P+'))throw Error('Planar callout revealed a future point');
await page.selectOption('#module-select','4');
if(await page.locator('#next-value').textContent()!==correctionReadout)throw Error('Annotations changed the construction');
await page.selectOption('#power-display','full');
await checkPointLeaders(['B = P = E · s = 1']);
await page.locator('#stage').fill('0');await page.locator('#stage').dispatchEvent('input');
await checkPointLeaders(['B = P · s = 1']);
drawn=JSON.parse(await page.locator('#overview').getAttribute('data-drawn-labels'));
if(drawn.some(t=>t.includes('= E')))throw Error('Full construction reveals E before its birth');
await page.selectOption('#power-display','current');await page.selectOption('#module-select','4');await page.click('#iterate');
await checkPointLeaders(['B','P · s','E · s^10','Next state P+']);
if(await page.locator('#module-status').getAttribute('data-kind')==='shared-state')throw Error('Distinct states still shown as shared');
// Returning via a native method must not leave a stale module index.
await page.locator('#degree').fill('10');await page.selectOption('#method','AK');await page.selectOption('#method','AKfast');
if(await page.locator('#error').isVisible())throw Error('Stale module after native mode');
await page.selectOption('#power-display','full');
await page.locator('#advanced > summary').click();await page.locator('#exploration').check();

const links=await page.locator('.gallery-links a').evaluateAll(a=>a.map(x=>x.href));for(const url of links){await page.goto(url);await page.waitForTimeout(150);if((await page.locator('body').innerText()).includes('Error response'))throw Error('Missing '+url);}
if(errors.length)throw Error(errors.join('\n'));console.log(JSON.stringify({status:'PASS',methods:11,archive_previews:links.length,mobile_width:360,paper_views:3,million_modules:26,infinity_and_domain_checked:true}));await b.close();})().catch(e=>{console.error(e);process.exit(1)});
