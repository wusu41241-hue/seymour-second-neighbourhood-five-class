"use strict";
// Local multi-neighbour retention checks with the exact graph prerequisites.
const fs=require("fs"),path=require("path");
function ids(m,n){const a=[];for(let x=0;x<n;x++)if(m&(1<<x))a.push(x);return a;}
function pc(m){let c=0;for(;m;m&=m-1)c++;return c;}
function two(o,x){let m=0;for(const a of ids(o[x],o.length))m|=o[a];return m&~(o[x]|1<<x);}
function check(v,m,d){if(!v)throw Error(m+JSON.stringify(d));}
const counts={graphs5:0,sampledGraphs:0,saturatedExceptionalCases:0,twoSourceCases:0,
  multiKeeperCases:0,retainedFirstNeighbours:0,transfersWithNewFarHeads:0};let control=null;
function audit(o){
  const n=o.length,full=(1<<n)-1,inc=Array(n).fill(0),P=Array(n).fill(0),U=[],N2=[];
  for(let x=0;x<n;x++)for(const y of ids(o[x],n))inc[y]|=1<<x;
  for(let x=0;x<n;x++){N2[x]=two(o,x);U[x]=full&~(o[x]|N2[x]|1<<x);for(const y of ids(U[x],n))P[y]|=1<<x;}
  const M=o.map((m,x)=>full&~(m|inc[x]|1<<x)),bad=[],missing=[];let Z=0;
  for(let a=0;a<n;a++)for(let b=a+1;b<n;b++)if(M[a]&(1<<b)){const fa=inc[a]&P[b],fb=inc[b]&P[a];missing.push({a,b,fa,fb});if(fa&&fb){bad.push({a,b,fa,fb});Z|=fa|fb;}}
  if(!bad.length)return;
  for(let x=0;x<n;x++){
    const g=pc(o[x])-pc(N2[x]),eta=2*pc(M[x])+g-1-pc(P[x]);if(eta!==2||g<1||g>2||!P[x])continue;
    let C=0;for(const r of ids(P[x],n))C|=o[r];C&=full&~P[x];if(!C)continue;
    const Q=full&~(P[x]|inc[x]|1<<x),H=Q&~C;if(pc(H)!==1||(H&o[x]))continue;
    const q=ids(H,n)[0];let X=0;for(const r of ids(C,n))X|=o[r];X&=full&~(P[x]|C);
    if(N2[x]!==((M[x]&~H)|X)||pc(X)>=pc(C))continue;counts.saturatedExceptionalCases++;
    if((Z&~((1<<x)|(1<<q)))||!(Z&(1<<x))||!(Z&(1<<q)))continue;counts.twoSourceCases++;
    const R=M[x]&C;if(!R)continue;
    const T=o.slice();
    for(const{a,b,fa,fb}of missing){let forward;if(fa&&fb){forward=fa===(1<<x);check(forward||fb===(1<<x),"choose only x failures",{o,x,a,b});}else forward=!fa;T[forward?a:b]|=1<<(forward?b:a);}
    // Reverse every added first arc at x except all r in R. The R arcs are
    // uniquely convenient; incoming q is not retained.
    for(const r of ids(M[x],n)){if(R&(1<<r)){check(!(inc[x]&P[r])&&(inc[r]&P[x]),"unique x->r",{o,x,r});T[x]|=1<<r;T[r]&=~(1<<x);}else{T[x]&=~(1<<r);T[r]|=1<<x;}}
    const next=two(T,x),envelope=(N2[x]&~R)|U[x];
    check(T[x]===(o[x]|R),"retained first set",{o,x,R});
    check(!(next&~envelope),"multi-retention exact envelope",{o,x,R,next,envelope});
    for(const r of ids(R,n))check(!(T[r]&U[x]),"retained intermediate cannot reach original far head",{o,x,r});
    counts.multiKeeperCases++;counts.retainedFirstNeighbours+=pc(R);if(next&U[x])counts.transfersWithNewFarHeads++;
    if(!control)control={out:o,x,q,R,next};
  }
}
for(let c=0;c<59049;c++){let d=c;const o=Array(5).fill(0);for(let a=0;a<5;a++)for(let b=a+1;b<5;b++){const k=d%3;d=Math.floor(d/3);if(k===1)o[a]|=1<<b;if(k===2)o[b]|=1<<a;}audit(o);counts.graphs5++;}
let seed=0x22402026;function random(){seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;return(seed>>>0)/4294967296;}
for(let s=0;s<150000;s++){const n=6+s%7,o=Array(n).fill(0),density=[.35,.5,.65,.8,.9][s%5];for(let a=0;a<n;a++)for(let b=a+1;b<n;b++)if(random()<density){if(random()<.5)o[a]|=1<<b;else o[b]|=1<<a;}audit(o);counts.sampledGraphs++;}
const result={status:"PASS",counts,control,seed:"0x22402026",scope:"Conditional exact multi-retention set checks. Actual minimal all-deficient hypotheses are not presumed. Zero eligible cases, if any, must not be represented as a substantive test of multi-retention."};
fs.writeFileSync(path.join(__dirname,"audit_multikeeper.results.json"),JSON.stringify(result,null,2)+"\n");console.log(JSON.stringify(result,null,2));
