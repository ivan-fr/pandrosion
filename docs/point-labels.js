// Screen-space annotations only: construction coordinates and point identities stay intact.
const clamp=(v,lo,hi)=>Math.max(lo,Math.min(hi,v));
const overlaps=(a,b,gap=0)=>a.x<b.x+b.w+gap&&a.x+a.w+gap>b.x&&a.y<b.y+b.h+gap&&a.y+a.h+gap>b.y;
const cross=(a,b,c)=>(b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0]);
function crosses(a,b,c,d){return cross(a,b,c)*cross(a,b,d)<0&&cross(c,d,a)*cross(c,d,b)<0;}
function cutsBox(a,b,r){
 const corners=[[r.x,r.y],[r.x+r.w,r.y],[r.x+r.w,r.y+r.h],[r.x,r.y+r.h]];
 return corners.some((c,i)=>crosses(a,b,c,corners[(i+1)%4]));
}

export function placePointLabels(marks,width,height,measure){
 const placed=[],bounds={left:8,right:width-8,top:8,bottom:height-28};
 const labels=marks.filter(p=>p.text).sort((a,b)=>(b.priority||0)-(a.priority||0)||a.y-b.y||a.x-b.x);
 for(const mark of labels){
  const bw=measure(mark.text)+12,bh=22,[sx,sy]=mark.prefer||[1,-1],anchor=[mark.x,mark.y];
  const directions=[[sx,sy],[-sx,sy],[sx,-sy],[-sx,-sy],[sx,0],[-sx,0],[0,sy],[0,-sy]];
  let best=null;
  const consider=(x,y,preference)=>{
   const box={x:clamp(x,bounds.left,bounds.right-bw),y:clamp(y,bounds.top,bounds.bottom-bh),w:bw,h:bh};
   if(placed.some(p=>overlaps(box,p.box,5)))return;
   // A label must not cover any point, even a point that has no label of its own.
   if(marks.some(p=>overlaps(box,{x:p.x-6,y:p.y-6,w:12,h:12})))return;
   const end=[clamp(mark.x,box.x,box.x+bw),clamp(mark.y,box.y,box.y+bh)];
   const distance=Math.hypot(end[0]-mark.x,end[1]-mark.y);
   const obstructed=placed.filter(p=>cutsBox(anchor,end,p.box)||cutsBox(p.anchor,p.end,box)).length;
   const crossings=placed.filter(p=>crosses(anchor,end,p.anchor,p.end)).length;
   const throughPoint=marks.some(p=>{
    const dx=end[0]-mark.x,dy=end[1]-mark.y,t=((p.x-mark.x)*dx+(p.y-mark.y)*dy)/(distance*distance);
    return t>1e-6&&t<1&&Math.hypot(p.x-mark.x-t*dx,p.y-mark.y-t*dy)<3;
   });
   const score=distance+preference+obstructed*1000+crossings*120+(throughPoint?400:0);
   if(!best||score<best.score)best={...mark,anchor,end,box,score};
  };
  for(const gap of [24,42,66,96,136,192])for(let i=0;i<directions.length;i++){
   const [dx,dy]=directions[i];
   consider(mark.x+(dx>0?gap:dx<0?-gap-bw:-bw/2),mark.y+(dy>0?gap*.65:dy<0?-gap*.65-bh:-bh/2),i*7);
  }
  // Crowded full constructions may need labels farther away than a local callout.
  if(!best)for(let y=bounds.top;y+bh<=bounds.bottom;y+=bh+6)for(const x of [bounds.left,bounds.right-bw])consider(x,y,100);
  if(best)placed.push(best);
 }
 return placed;
}

export function drawPointLabels(c,marks,width,height,colors){
 const labels=placePointLabels(marks,width,height,text=>c.measureText(text).width);
 c.save();c.setLineDash([]);c.lineWidth=1;
 // Leaders first, then opaque label backgrounds, then the exact point marks on top.
 for(const p of labels){c.strokeStyle=p.color||colors.muted;c.beginPath();c.moveTo(...p.anchor);c.lineTo(...p.end);c.stroke();}
 for(const p of labels){c.fillStyle=colors.bg;c.fillRect(p.box.x,p.box.y,p.box.w,p.box.h);c.fillStyle=p.color||colors.fg;c.fillText(p.text,p.box.x+6,p.box.y+15);}
 for(const p of marks){c.fillStyle=p.color||colors.fg;c.beginPath();c.arc(p.x,p.y,p.radius||2.5,0,2*Math.PI);c.fill();}
 c.restore();
}
