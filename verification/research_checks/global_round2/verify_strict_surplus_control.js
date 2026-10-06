"use strict";
// Independent exact small control. No downloads, dependencies, or file writes.
function assert(v,s){if(!v)throw Error(s);}
function bits(m,n){return Array.from({length:n},(_,x)=>x).filter(x=>m&(1<<x));}
function size(m){let k=0;while(m){m&=m-1;k++;}return k;}
function inspect(out){
  const n=out.length,full=(1<<n)-1,inc=Array(n).fill(0),two=Array(n).fill(0);
  for(let x=0;x<n;x++)for(const y of bits(out[x],n)){
    assert(x!==y&&!(out[y]&(1<<x)),"Not oriented");
    inc[y]|=1<<x;two[x]|=out[y];
  }
  for(let x=0;x<n;x++)two[x]&=full&~(out[x]|1<<x);
  const protection=[];
  for(let a=0;a<n;a++)for(const b of bits(out[a],n))
    if(!(inc[a]&~inc[b]))protection.push([a,b]);
  const far=out.map((m,x)=>full&~(m|two[x]|1<<x));
  const unprotected=far.map((m,x)=>m&~protection.filter(p=>p[1]===x).reduce((z,p)=>z|1<<p[0],0));
  return {out,inc,two,far,protection,unprotected,gap:out.map((m,x)=>size(m)-size(two[x]))};
}
function score(out,L){let later=(1<<out.length)-1,s=0;for(const x of L){later&=~(1<<x);s+=size(out[x]&later);}return s;}
function permutations(n){const ans=[];function go(L,R){if(!R.length){ans.push(L);return;}for(let i=0;i<R.length;i++)go(L.concat(R[i]),R.slice(0,i).concat(R.slice(i+1)));}go([],Array.from({length:n},(_,x)=>x));return ans;}
const D=inspect([4,4,24,32,32,3]);
const Q=inspect([6,4,24,48,32,3]);
const T=inspect([30,28,56,48,32,3]);
const L=[0,1,2,3,4,5],f=5,orders=permutations(6);
const medianQ=Math.max(...orders.map(p=>score(Q.out,p)));
const medianT=Math.max(...orders.map(p=>score(T.out,p)));
assert(medianQ===8&&medianT===13&&score(T.out,L)===medianT,"Exact median score control");
assert(T.out[f]===D.out[f]&&Q.two[f]===D.two[f],"Feed original neighborhoods");
assert(D.gap[f]===1&&T.gap[f]===-1&&size(D.unprotected[f])===2,"Strict-surplus sharpness");
let good=0;const pos=Array(6);L.forEach((x,i)=>pos[x]=i);
for(const y of bits(T.inc[f],6))if(bits(T.out[f],6).some(a=>pos[a]<pos[y]&&(T.out[a]&(1<<y))))good|=1<<y;
assert(size(good)===3&&size(T.out[f])===2,"Stable strong-feed slack one");
const missingQ=((1<<6)-1)&~(Q.out[f]|Q.inc[f]|1<<f);
assert(bits(missingQ,6).join(",")==="2","One remaining partner");
assert(D.gap.some(g=>g<=0),"Control is NOT an SNC counterexample");
console.log(JSON.stringify({status:"PASS",out:D.out,terminalWeakClosure:Q.out,maximizingCompletion:T.out,medianOrder:L,ordersChecked:orders.length,medianScoreQ:medianQ,medianScoreT:medianT,feed:f,originalFirst:bits(D.out[f],6),originalSecond:bits(D.two[f],6),completedSecond:bits(T.two[f],6),originalGap:D.gap[f],completedGap:T.gap[f],originalUnprotectedFarHeads:bits(D.unprotected[f],6),remainingMissing:bits(missingQ,6),goodVertices:bits(good,6),strongGoodSlack:size(good)-size(T.out[f]),originalGaps:D.gap,scope:"An exact control against extending the zero-gap +3 bound to negative completed gaps; not an SNC counterexample."},null,2));
