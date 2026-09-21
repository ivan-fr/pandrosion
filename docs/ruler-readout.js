import {cross,point} from './geometry.js';

const parallel=(l,q)=>[l[0]*q[2],l[1]*q[2],-l[0]*q[0]-l[1]*q[1]];
const xy=q=>{
 if(!q||q[2]===0)throw Error('The readout point is at infinity.');
 const a=[q[0]/q[2],q[1]/q[2]];
 if(!a.every(Number.isFinite))throw Error('The readout cannot be measured at this scale.');
 return a;
};

// The only variable input is a constructed point. No root, iteration formula or
// scalar readout is used to place R. Calibration is undone by a first triangle.
export function constructRulerSegment({W,H,points},calibration=1,source='P'){
 if(!(H>0&&W>0&&calibration>0&&Number.isFinite(H+W+calibration)))throw Error('Invalid readout setup.');
 const A=points.A,B=points.B,input=xy(points[source]),base=xy(B);
 const P=input.every((v,i)=>v===base[i])?B:points[source];
 const U=point(W+H/4,H),D=calibration===1?B:point(W,H*(1-calibration)),top=[0,1,-H];
 // Reuse exact identity marks, so their labels describe the same physical point.
 const DU=cross(D,U),BI=parallel(DU,B),I=calibration===1?U:cross(BI,top);
 const PI=cross(P,I),BR=parallel(PI,B),R=P===B?I:cross(BR,top);
 return {source,calibration,points:{A,B,D,U,I,P,R},lines:{DU,BI,PI,BR},segment:[A,R],unit:[A,U]};
}

export function measureWithRuler(segment,unit,paperScale=1){
 if(!(paperScale>0&&Number.isFinite(paperScale)))throw Error('Choose a positive paper scale.');
 const distance=([a,b])=>{const x=xy(a),y=xy(b);return Math.hypot(x[0]-y[0],x[1]-y[1])*paperScale;};
 const lengthCM=distance(segment),unitCM=distance(unit),tickCM=.1;
 const millimeters=Math.round(lengthCM/tickCM);
 if(!(unitCM>0&&Number.isFinite(unitCM))||!Number.isSafeInteger(millimeters))throw Error('This length is outside the ruler readout range.');
 const measuredCM=millimeters/10,rootStep=tickCM/unitCM;
 const digits=Math.min(12,Math.max(0,Math.ceil(-Math.log10(rootStep))));
 return {lengthCM,unitCM,tickCM,millimeters,measuredCM,
  text:measuredCM.toFixed(1)+' cm',valueText:(measuredCM/unitCM).toFixed(digits),
  // This interval describes final rounding only, not construction/instrument errors.
  lower:Math.max(0,(measuredCM-tickCM/2)/unitCM),upper:(measuredCM+tickCM/2)/unitCM};
}

export function drawRuler(c,w,h,reading,colors){
 if(!reading||w<80)return;
 const {lengthCM,unitCM}=reading,margin=28,span=Math.max(.5,lengthCM,unitCM)*1.15,k=(w-2*margin)/span,x=v=>margin+v*k;
 const baseline=114;
 c.font='12px system-ui';c.lineWidth=1;c.strokeStyle=colors.muted;c.fillStyle=colors.muted;
 c.beginPath();c.moveTo(margin,baseline);c.lineTo(w-margin,baseline);c.stroke();
 // Every small tick is one millimetre; for long rulers omit ticks too dense to draw.
 const stride=Math.max(1,Math.ceil(3/(k*.1))),labelStride=Math.max(10,10*Math.ceil(55/k));
 for(let mm=0;mm*.1<=span;mm+=stride){
  const major=mm%10===0;c.beginPath();c.moveTo(x(mm/10),baseline);c.lineTo(x(mm/10),baseline+(major?15:7));c.stroke();
 }
 for(let mm=0;mm*.1<=span;mm+=labelStride)c.fillText(String(mm/10),x(mm/10)-3,baseline+31);
 c.fillText('cm',w-margin-16,baseline+48);
 c.strokeStyle=colors.green;c.fillStyle=colors.green;c.lineWidth=3;
 c.beginPath();c.moveTo(x(0),42);c.lineTo(x(lengthCM),42);c.stroke();
 for(const [name,value] of [['A',0],['R',lengthCM]]){c.beginPath();c.arc(x(value),42,4,0,2*Math.PI);c.fill();c.fillText(name,x(value)-4,name==='A'?26:24);}
 c.setLineDash([3,3]);c.lineWidth=1;c.beginPath();c.moveTo(x(lengthCM),48);c.lineTo(x(lengthCM),baseline+16);c.stroke();c.setLineDash([]);
 c.strokeStyle=colors.blue;c.fillStyle=colors.blue;c.lineWidth=2;
 c.beginPath();c.moveTo(x(0),78);c.lineTo(x(unitCM),78);c.stroke();
 c.fillText('AU · 1 unit',Math.min(w-100,x(unitCM)+8),82);
}

export function drawReadoutConstruction(c,w,h,readout,colors){
 if(!readout||w<80)return;
 const groups=new Map();
 for(const [name,q] of Object.entries(readout.points)){if(!groups.has(q))groups.set(q,[]);groups.get(q).push(name);}
 const entries=[...groups].map(([q,names])=>({name:names.join(' = '),result:names.includes('R'),p:xy(q)}));
 const xs=entries.map(e=>e.p[0]),ys=entries.map(e=>e.p[1]),xmin=Math.min(...xs),xmax=Math.max(...xs),ymin=Math.min(...ys),ymax=Math.max(...ys);
 const k=Math.min((w-160)/Math.max(xmax-xmin,1e-9),(h-80)/Math.max(ymax-ymin,1e-9));
 const screen=p=>[w/2+(p[0]-(xmin+xmax)/2)*k,h/2-(p[1]-(ymin+ymax)/2)*k];
 for(const [a,b] of [['A','B'],['D','U'],['B','I'],['P','I'],['B','R'],['A','R']]){
  c.strokeStyle=a==='A'&&b==='R'?colors.green:a==='P'||b==='R'?colors.blue:a==='A'?colors.line:colors.muted;c.lineWidth=b==='R'?2:1;
  c.beginPath();c.moveTo(...screen(xy(readout.points[a])));c.lineTo(...screen(xy(readout.points[b])));c.stroke();
 }
 const labels=[];c.font='12px system-ui';
 for(const {name,result,p} of entries){
  const [x,y]=screen(p);c.fillStyle=result?colors.green:colors.fg;c.beginPath();c.arc(x,y,3,0,2*Math.PI);c.fill();
  const width=c.measureText(name).width;let tx=x+12,ty=y-12;
  tx=Math.max(5,Math.min(w-width-5,tx));
  while(labels.some(q=>tx<q[0]+q[2]+8&&tx+width+8>q[0]&&Math.abs(q[1]-ty)<19))ty+=22;
  ty=Math.max(16,Math.min(h-10,ty));labels.push([tx,ty,width]);
  c.strokeStyle=colors.muted;c.lineWidth=1;c.beginPath();c.moveTo(x,y);c.lineTo(tx,ty-4);c.stroke();
  c.fillStyle=colors.bg;c.fillRect(tx-3,ty-13,width+6,17);c.fillStyle=colors.fg;c.fillText(name,tx,ty);
 }
}
