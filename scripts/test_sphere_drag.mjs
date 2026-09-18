import assert from 'node:assert/strict';
import {chromium} from 'playwright';
const browser=await chromium.launch({...(process.env.PLAYWRIGHT_CHANNEL?{channel:process.env.PLAYWRIGHT_CHANNEL}:{}),headless:true});
try{
 for(const mobile of [false,true]){
  const context=await browser.newContext({viewport:mobile?{width:390,height:844}:{width:1280,height:1000},hasTouch:mobile,isMobile:mobile});
  const page=await context.newPage(),errors=[];page.on('pageerror',e=>errors.push(e.message));
  await page.goto(process.env.PREVIEW_URL||'http://127.0.0.1:8765/');
  await page.selectOption('#method','arc');await page.selectOption('#view','sphere');
  const canvas=page.locator('#overview');await canvas.scrollIntoViewIfNeeded();
  const box=await canvas.boundingBox(),x=box.x+box.width/2,y=box.y+box.height/2;
  const angles=async()=>[Number(await page.locator('#yaw').inputValue()),Number(await page.locator('#pitch').inputValue())];
  const original=await angles(),answer=await page.locator('#answer-label').innerText();
  assert.equal(await canvas.evaluate(e=>getComputedStyle(e).touchAction),'none');
  let cdp;
  if(mobile){
   cdp=await context.newCDPSession(page);const scroll=await page.evaluate(()=>scrollY);
   await cdp.send('Input.dispatchTouchEvent',{type:'touchStart',touchPoints:[{x,y,id:1}]});
   for(let i=1;i<=5;i++)await cdp.send('Input.dispatchTouchEvent',{type:'touchMove',touchPoints:[{x:x+12*i,y:y-8*i,id:1}]});
   await cdp.send('Input.dispatchTouchEvent',{type:'touchEnd',touchPoints:[]});
   assert.equal(await page.evaluate(()=>scrollY),scroll,'Sphere drag must not scroll the page');
  }else{
   await page.mouse.move(x,y);await page.mouse.down();await page.mouse.move(x+70,y-40,{steps:5});await page.mouse.up();
  }
  const changed=await angles();assert(changed[0]>original[0]&&changed[1]>original[1]);
  assert.equal(await page.locator('#answer-label').innerText(),answer,'Dragging must not iterate');
  assert(!(await canvas.getAttribute('class')||'').includes('dragging'));
  if(mobile){
   await cdp.send('Input.dispatchTouchEvent',{type:'touchStart',touchPoints:[{x,y,id:1}]});
   await cdp.send('Input.dispatchTouchEvent',{type:'touchCancel',touchPoints:[]});
   assert(!(await canvas.getAttribute('class')||'').includes('dragging'));
  }else{
   // Captured mouse drag can leave the canvas; tilt remains bounded and releases cleanly.
   await page.mouse.move(x,y);await page.mouse.down();await page.mouse.move(x,0,{steps:10});await page.mouse.up();
   assert.equal((await angles())[1],80);const released=await angles();await page.mouse.move(x,y);assert.deepEqual(await angles(),released);
  }
  await page.selectOption('#view','plane');await canvas.scrollIntoViewIfNeeded();
  assert.equal(await canvas.evaluate(e=>getComputedStyle(e).touchAction),'auto');
  const fixed=await angles(),b=await canvas.boundingBox(),px=b.x+b.width/2,py=b.y+b.height/2;
  if(mobile){
   const scroll=await page.evaluate(()=>scrollY);
   await cdp.send('Input.dispatchTouchEvent',{type:'touchStart',touchPoints:[{x:px,y:py,id:1}]});
   for(let i=1;i<=6;i++)await cdp.send('Input.dispatchTouchEvent',{type:'touchMove',touchPoints:[{x:px,y:py-20*i,id:1}]});
   await cdp.send('Input.dispatchTouchEvent',{type:'touchEnd',touchPoints:[]});
   assert((await page.evaluate(()=>scrollY))>scroll,'Plan must retain touch scrolling');
  }else{await page.mouse.move(px,py);await page.mouse.down();await page.mouse.move(px+50,py+30);await page.mouse.up();}
  assert.deepEqual(await angles(),fixed);assert.deepEqual(errors,[]);await context.close();
 }
 console.log(JSON.stringify({status:'PASS',mouse_drag:true,touch_drag:true,cancel_and_capture:true,plan_scroll_preserved:true}));
}finally{await browser.close();}
