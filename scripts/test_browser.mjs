import { chromium } from 'playwright';
import fs from 'node:fs';
const output=process.env.PREVIEW_OUTPUT || '.ci/browser';
fs.mkdirSync(output,{recursive:true});
(async()=>{const b=await chromium.launch({...(process.env.PLAYWRIGHT_CHANNEL ? {channel:process.env.PLAYWRIGHT_CHANNEL}:{}),headless:true});const page=await b.newPage({viewport:{width:1280,height:1000}});const errors=[];page.on('pageerror',e=>errors.push(page.url()+': '+e.message));await page.goto(process.env.PREVIEW_URL || 'http://127.0.0.1:8765/');await page.waitForFunction(()=>document.getElementById('next-value').textContent!=='—');
// Regression: the decentered arc must render smoothly with automatically selected proportions.
await page.selectOption('#method','arc');await page.selectOption('#view','sphere');
await page.screenshot({path:`${output}/decentered-sphere.png`,fullPage:true});
await page.locator('#yaw').fill('65');await page.locator('#yaw').dispatchEvent('input');await page.locator('#pitch').fill('-35');await page.locator('#pitch').dispatchEvent('input');
await page.screenshot({path:`${output}/decentered-sphere-rotated.png`,fullPage:true});
await page.selectOption('#method','AKfast');await page.selectOption('#view','plane');
// Automatic preparation only: no hidden iteration, unchanged original input, one click = one step.
await page.locator('#degree').fill('1000000');await page.locator('#target').fill('500000');await page.locator('#target').dispatchEvent('change');
if(await page.locator('#error').isVisible())throw Error('Automatic preparation failed');
if(await page.locator('#advanced').getAttribute('open')!==null)throw Error('Advanced controls exposed');
if(await page.locator('#state').inputValue()!=='1')throw Error('Unexpected automatic iteration');
await page.waitForTimeout(300);if(await page.locator('#state').inputValue()!=='1')throw Error('Background solver must not run');
for(const mode of ['AKfast','ADfast','projectiveFast','arcFast']){
 await page.selectOption('#method',mode);if(await page.locator('#state').inputValue()!=='1')throw Error('New method did not prepare step zero');
 await page.click('#iterate');if(!(await page.locator('#answer-label').innerText()).includes('étape 1'))throw Error('One click must be one iteration');
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
 await page.click('#iterate');if(!(await page.locator('#answer-label').innerText()).includes('étape 1'))throw Error('Original iteration failed');
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
 await page.click('#iterate');if(!(await page.locator('#answer-label').innerText()).includes('étape 1'))throw Error('Pencil manual step failed');
 if(await page.locator('#target').inputValue()!=='500000')throw Error('Pencil changed original X');
 await page.locator('#degree').fill('33');await page.locator('#degree').dispatchEvent('change');if(!await page.locator('#error').isVisible())throw Error('Pencil degree limit ignored');
}
await page.locator('#degree').fill('3');await page.selectOption('#method','AKfast');
await page.locator('#advanced > summary').click();await page.locator('#exploration').check();await page.click('#reset');
for(const mode of ['AK','AD','projective','arc','halley','pade','circle','AKfast','ADfast','projectiveFast','arcFast']){await page.selectOption('#method',mode);if(await page.locator('#error').isVisible())throw Error(mode+': '+await page.locator('#error').innerText());await page.locator('#stage').fill('0');await page.locator('#stage').dispatchEvent('input');await page.click('#forward');await page.click('#iterate');await page.click('#reset');}
await page.selectOption('#method','circle');await page.selectOption('#chart','uniform');await page.screenshot({path:`${output}/gallery-uniform.png`,fullPage:true});await page.selectOption('#chart','compact');await page.selectOption('#view','sphere');await page.locator('#yaw').fill('50');await page.locator('#yaw').dispatchEvent('input');await page.screenshot({path:`${output}/gallery-sphere.png`,fullPage:true});
await page.selectOption('#example','initial');if(!await page.locator('#warning').isVisible())throw Error('Missing infinity warning');if(await page.locator('#view').inputValue()!=='sphere')throw Error('No automatic sphere');await page.selectOption('#view','plane');await page.click('#iterate');if(await page.locator('#view').inputValue()!=='plane')throw Error('Manual view overridden');await page.selectOption('#example','outside');if(!await page.locator('#error').isVisible())throw Error('Missing domain error');await page.click('#reset');await page.click('#normalize');if(await page.locator('#error').isVisible())throw Error('Normalization failed');
await page.selectOption('#method','AKfast');await page.locator('#degree').fill('1024');await page.locator('#state').fill(String(Math.exp(Math.log(.4)/1024)));await page.locator('#state').dispatchEvent('change');if(await page.locator('#error').isVisible())throw Error('Large degree failed');if(!(await page.locator('#fast-status').innerText()).includes('10 multiplications contre 1023'))throw Error('Wrong binary count');await page.click('#normalize-optimal');if(await page.locator('#error').isVisible())throw Error('Adaptive failed');if(!(await page.locator('#adaptive-status').innerText()).includes('score'))throw Error('Missing metadata');
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
const links=await page.locator('.gallery-links a').evaluateAll(a=>a.map(x=>x.href));for(const url of links){await page.goto(url);await page.waitForTimeout(150);if((await page.locator('body').innerText()).includes('Error response'))throw Error('Missing '+url);}
if(errors.length)throw Error(errors.join('\n'));console.log(JSON.stringify({status:'PASS',methods:11,archive_previews:links.length,mobile_width:360,infinity_and_domain_checked:true}));await b.close();})().catch(e=>{console.error(e);process.exit(1)});
