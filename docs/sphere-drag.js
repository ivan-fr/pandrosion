// Pointer events unify mouse, touch and pen without changing the construction state.
export function bindSphereDrag(canvas,yaw,pitch,enabled,redraw){
 let drag=null;
 function end(event){
  if(!drag||(event&&event.pointerId!==drag.id))return;
  const id=drag.id;drag=null;canvas.classList.remove('dragging');
  if(canvas.hasPointerCapture(id))canvas.releasePointerCapture(id);
 }
 canvas.addEventListener('pointerdown',event=>{
  if(!enabled()||drag||!event.isPrimary||event.button!==0)return;
  drag={id:event.pointerId,x:event.clientX,y:event.clientY};
  canvas.setPointerCapture(event.pointerId);canvas.classList.add('dragging');event.preventDefault();
 });
 canvas.addEventListener('pointermove',event=>{
  if(!drag||event.pointerId!==drag.id)return;
  if(!enabled()){end(event);return;}
  const dx=event.clientX-drag.x,dy=event.clientY-drag.y;
  drag.x=event.clientX;drag.y=event.clientY;
  const sensitivity=180/Math.max(180,Math.min(canvas.clientWidth,canvas.clientHeight));
  yaw.value=String(((Number(yaw.value)+dx*sensitivity+180)%360+360)%360-180);
  pitch.value=String(Math.max(-80,Math.min(80,Number(pitch.value)-dy*sensitivity)));
  event.preventDefault();redraw();
 });
 for(const type of ['pointerup','pointercancel','lostpointercapture'])canvas.addEventListener(type,end);
 return end;
}
