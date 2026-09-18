// Post-V20 preparation. Exact binary64 inputs, outward-rounded dyadic intervals.
// No root/log/exp oracle is used to select the initial state.
const PRECISION=128;
const bitLength=n=>n===0n?0:n.toString(2).length;
function normalize(lo,hi,e){const shift=Math.max(0,bitLength(hi)-PRECISION);if(!shift)return {lo,hi,e};const d=1n<<BigInt(shift);return {lo:lo/d,hi:(hi+d-1n)/d,e:e+shift};}
export function exactDouble(x){
 if(!(x>0&&Number.isFinite(x)))throw Error('Un nombre fini strictement positif est requis.');
 const v=new DataView(new ArrayBuffer(8));v.setFloat64(0,x,false);const b=v.getBigUint64(0,false),f=b&((1n<<52n)-1n),e=Number((b>>52n)&2047n);
 const n=e?f+(1n<<52n):f;return {lo:n,hi:n,e:e?e-1023-52:-1074};
}
export function multiplyIntervals(a,b){return normalize(a.lo*b.lo,a.hi*b.hi,a.e+b.e);}
export function compareDyadic(n,e,m,f){
 if(n===0n||m===0n)return n===m?0:n===0n?-1:1;
 const an=bitLength(n)+e,bn=bitLength(m)+f;if(an!==bn)return an<bn?-1:1;
 const base=Math.min(e,f),a=n<<BigInt(e-base),b=m<<BigInt(f-base);return a===b?0:a<b?-1:1;
}
export function residualInterval(p,X,s){
 if(!Number.isSafeInteger(p)||p<1||p>1_000_000)throw Error('Degré entier entre 1 et 1 000 000 requis.');
 let result={lo:1n,hi:1n,e:0},base=exactDouble(s),n=p;
 while(n){if(n%2)result=multiplyIntervals(result,base);n=Math.floor(n/2);if(n)base=multiplyIntervals(base,base);}
 return multiplyIntervals(exactDouble(X),result);
}
export const inResidualBand=r=>compareDyadic(r.lo,r.e,1n,0)>=0&&compareDyadic(r.hi,r.e,2n,0)<=0;
function toNumber(n,e){const shift=Math.max(0,bitLength(n)-53);return Number(n>>BigInt(shift))*2**(e+shift);}
export function findInitialState(p,X){
 if(!Number.isSafeInteger(p)||p<3||p>1_000_000||!(X>0&&Number.isFinite(X)))throw Error('Choisir p entier entre 3 et 1 000 000 et X fini positif.');
 let lower=0,upper=1,comparisons=0,halvings=0;
 const check=s=>{comparisons++;const enclosure=residualInterval(p,X,s);return {s,enclosure};};
 const accept=r=>({c:r.s,enclosure:r.enclosure,comparisons,halvings,precision:PRECISION});
 let r=check(upper);
 // Bracket the interior target 3/2 by powers of two. Accept whenever [1,2] is certified.
 if(inResidualBand(r.enclosure))return accept(r);
 if(compareDyadic(r.enclosure.hi,r.enclosure.e,3n,-1)<0){
  do{lower=upper;upper*=2;r=check(upper);if(inResidualBand(r.enclosure))return accept(r);}while(compareDyadic(r.enclosure.hi,r.enclosure.e,3n,-1)<0);
 }else{
  lower=upper/2;r=check(lower);
  while(compareDyadic(r.enclosure.lo,r.enclosure.e,3n,-1)>0){upper=lower;lower/=2;r=check(lower);if(inResidualBand(r.enclosure))return accept(r);}
  if(inResidualBand(r.enclosure))return accept(r);
 }
 for(let i=0;i<80;i++){
  const middle=lower+(upper-lower)/2;if(middle===lower||middle===upper)break;
  r=check(middle);halvings++;if(inResidualBand(r.enclosure))return accept(r);
  if(compareDyadic(r.enclosure.hi,r.enclosure.e,3n,-1)<0)lower=middle;
  else if(compareDyadic(r.enclosure.lo,r.enclosure.e,3n,-1)>0)upper=middle;
  else throw Error('Comparaison indécidable à la précision de certification disponible.');
 }
 throw Error('Aucun départ certifié trouvé à la précision disponible.');
}
export function initializeCalibrated(p,X){
 const r=findInitialState(p,X),bound=r.enclosure;
 const calibratedX=toNumber((bound.lo+bound.hi)/2n,bound.e);
 // This is a rounded input parameter, never falsely advertised as exact X*c^p.
 const represented=exactDouble(calibratedX);
 const tolerance={lo:1n,hi:1n,e:-48}; // absolute <= 2^-48, independently checked below
 const add=(a,b)=>{const e=Math.min(a.e,b.e);return {lo:(a.lo<<BigInt(a.e-e))+(b.lo<<BigInt(b.e-e)),hi:(a.hi<<BigInt(a.e-e))+(b.hi<<BigInt(b.e-e)),e};};
 const high=add(represented,tolerance),low=add(bound,tolerance);
 if(compareDyadic(bound.hi,bound.e,high.lo,high.e)>0||compareDyadic(represented.hi,represented.e,low.lo,low.e)>0)throw Error('Erreur de calibration supérieure à la borne certifiée.');
 return {...r,X:calibratedX,s:1,originalX:X,residualLower:toNumber(bound.lo,bound.e),residualUpper:Math.min(2,toNumber(bound.hi,bound.e)+Number.EPSILON*2),calibrationErrorBound:2**-48};
}

// A numerical guard for the iterative UI, not a global conditioning theorem.
export function iterationDecision(p,X,current,next){
 const before=residualInterval(p,X,current),after=residualInterval(p,X,next);
 if(compareDyadic(before.lo,before.e,1n,-2)<0||compareDyadic(before.hi,before.e,2n,0)>0)throw Error('Le départ courant est hors de la bande numérique contrôlée. Initialiser à nouveau.');
 if(compareDyadic(after.lo,after.e,1n,-2)<0||compareDyadic(after.hi,after.e,2n,0)>0)throw Error('Le pas sort de la bande numérique contrôlée [1/4, 2]. Départ conservé.');
 const error=r=>{const e=Math.min(r.e,0),lo=r.lo<<BigInt(r.e-e),hi=r.hi<<BigInt(r.e-e),one=1n<<BigInt(-e),abs=x=>x<0n?-x:x;return {lo:lo>one?lo-one:hi<one?one-hi:0n,hi:abs(lo-one)>abs(hi-one)?abs(lo-one):abs(hi-one),e};};
 const a=error(before),b=error(after);
 return {stop:next===current||compareDyadic(b.hi,b.e,a.lo,a.e)>=0,before:toNumber(a.hi,a.e),after:toNumber(b.hi,b.e)};
}
