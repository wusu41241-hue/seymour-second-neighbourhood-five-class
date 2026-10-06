'use strict';
/* A local-obstruction control, not an SNC counterexample. */
const fs=require('fs'), path=require('path');
const out=[540,541,96,96,96,1,3,28,128,256], n=out.length, all=(1<<n)-1;
const pop=x=>{let k=0;while(x){x&=x-1;k++;}return k;};
const vertices=x=>Array.from({length:n},(_,i)=>i).filter(i=>(x>>>i)&1);
const inn=Array(n).fill(0);
for(let x=0;x<n;x++)for(let y=0;y<n;y++)if((out[x]>>>y)&1){
  if(x===y || ((out[y]>>>x)&1))throw Error('Not oriented');
  inn[y]|=1<<x;
}
function two(a,x){let q=0;for(let y=0;y<n;y++)if((a[x]>>>y)&1)q|=a[y];return q&~a[x]&~(1<<x);}
const sec=out.map((_,x)=>two(out,x)), qin=out.map((_,x)=>two(inn,x));
const far=out.map((_,x)=>all&~((1<<x)|out[x]|sec[x]));
const protect=(h,f)=>Boolean((out[h]>>>f)&1)&&!(inn[h]&~(inn[f]&~(1<<h)));
const miss=out.map((_,x)=>all&~((1<<x)|out[x]|inn[x]));
const eta=out.map((_,x)=>pop(miss[x])-1+pop(qin[x])-pop(sec[x]));
const gap=out.map((_,x)=>pop(out[x])-pop(sec[x]));
const t=out.map((_,x)=>vertices(far[x]).filter(h=>!protect(h,x)).length);
const P=out.map((_,x)=>out.reduce((m,_,p)=>m|((((far[p]>>>x)&1)?1:0)<<p),0));
const C=P.map(p=>{let c=0;for(let x=0;x<n;x++)if((p>>>x)&1)c|=out[x];return c&~p;});
const fail=(a,b)=>vertices(inn[a]).filter(x=>(far[x]>>>b)&1);
if(gap[0]!==1 || eta[0]!==1 || t[0]!==1 || C[0]!==qin[0])throw Error('Unit packet control changed');
if(gap[1]!==2 || eta[1]!==2 || t[1]!==1 || !protect(1,0))throw Error('Heavy protection changed');
if(JSON.stringify(fail(9,7))!=='[0,1]' || JSON.stringify(fail(7,9))!=='[8]')throw Error('BAD witnesses changed');
const result={status:'PASS',outMasks:out,
  unit:{vertex:0,out:vertices(out[0]),second:vertices(sec[0]),far:vertices(far[0]),
    residual:eta[0],gap:gap[0],unprotectedCount:t[0],farIn:vertices(P[0]),boundary:vertices(C[0]),secondIn:vertices(qin[0])},
  heavy:{vertex:1,out:vertices(out[1]),second:vertices(sec[1]),far:vertices(far[1]),
    residual:eta[1],gap:gap[1],unprotectedCount:t[1],incoming:vertices(inn[1])},
  unitIncoming:vertices(inn[0]),protection:'1 triangleleft 0',
  badPair:{endpoints:[7,9],failures9To7:fail(9,7),failures7To9:fail(7,9)},
  allGaps:gap,scope:'Not an SNC counterexample; negative-gap vertices and no strong minimality claim. Refutes a purely local ban on heavy-protecting-unit relations.'};
fs.writeFileSync(path.join(__dirname,'audit_heavy_protects_unit_control.results.json'),JSON.stringify(result,null,2));
console.log(JSON.stringify(result));
