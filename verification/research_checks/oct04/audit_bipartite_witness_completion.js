"use strict";
// Independent verifier for the new fixed-tournament completion argument.
// No code/results from the Pro reply are imported. Run with Node.
// No arbitrary graph is assumed to satisfy minimal-counterexample lemmas.
const fs=require("fs"),path=require("path");
function assert(ok,msg,d){if(!ok)throw Error(msg+" "+JSON.stringify(d));}
function pc(m){let c=0;for(;m;m&=m-1)c++;return c;}
function ids(m,n){const a=[];for(let x=0;x<n;x++)if(m&(1<<x))a.push(x);return a;}
function info(o){
  const n=o.length,full=(1<<n)-1,inc=Array(n).fill(0),two=Array(n).fill(0),P=Array(n).fill(0);
  for(let x=0;x<n;x++)for(const a of ids(o[x],n)){inc[a]|=1<<x;two[x]|=o[a];}
  for(let x=0;x<n;x++)two[x]&=full&~(o[x]|1<<x);
  const far=o.map((m,x)=>full&~(m|two[x]|1<<x));for(let x=0;x<n;x++)for(const y of ids(far[x],n))P[y]|=1<<x;
  const prot=far.map((m,x)=>ids(m,n).reduce((r,y)=>(o[y]&(1<<x))&&!(inc[y]&~inc[x])?r|1<<y:r,0));
  const F=far.map((m,x)=>m&~prot[x]),M=o.map((m,x)=>full&~(m|inc[x]|1<<x));
  const g=o.map((m,x)=>pc(m)-pc(two[x])),eta=M.map((m,x)=>2*pc(m)+g[x]-1-pc(P[x]));
  const missing=[],bad=[];let Z=0;
  for(let a=0;a<n;a++)for(let b=a+1;b<n;b++)if(M[a]&(1<<b)){
    const fa=inc[a]&P[b],fb=inc[b]&P[a];missing.push({a,b,fa,fb});if(fa&&fb){bad.push({a,b,fa,fb});Z|=fa|fb;}
  }
  return {n,full,inc,two,P,far,prot,F,M,g,eta,missing,bad,Z};
}
function reference(d,reverse,before=-1,after=-1){
  const pred=d.prot.slice(),rank=Array(d.n);let left=d.full,pos=0;
  if(before>=0){assert(!(d.prot[before]&(1<<after)),"missing partners are incomparable",{before,after});pred[after]|=1<<before;}
  while(left){let a=ids(left,d.n).filter(v=>!(pred[v]&left));if(reverse)a.reverse();assert(a.length,"reference order acyclic",d);const v=a[0];rank[v]=pos++;left&=~(1<<v);}
  return rank;
}
function complete(o,d,u,v,rank){
  const A=o[u]&d.far[v],B=o[v]&d.far[u],T=o.slice();
  assert(A&&B&&!(A&B),"nonempty disjoint bad bipartition",{o,u,v,A,B});
  assert(d.bad.length===pc(A)*pc(B),"all bad pairs are exactly A times B",{o,u,v,A,B,bad:d.bad});
  for(const e of d.missing){let a,b;
    if(e.fa&&e.fb){
      if(A&(1<<e.a)){a=e.a;b=e.b;}else{a=e.b;b=e.a;}
      assert((A&(1<<a))&&(B&(1<<b)),"bad edge orientation A->B",{o,u,v,e,A,B});
      assert((a===e.a?e.fa:e.fb)===(1<<u),"selected bad direction fails only at u",{o,u,v,e});
    }else{
      const forward=!e.fa&&(!!e.fb||rank[e.a]<rank[e.b]);a=forward?e.a:e.b;b=forward?e.b:e.a;
    }T[a]|=1<<b;
  }
  return {T,A,B};
}
function target(o,d,v){
  const P=d.P[v];if(!P)return null;
  let C=0;for(const p of ids(P,d.n))C|=o[p];C&=d.full&~P;if(!C)return null;
  let X=0;for(const c of ids(C,d.n))X|=o[c];X&=d.full&~(P|C);
  const Q=d.full&~(P|d.inc[v]|1<<v),H=Q&~C,j=pc(H),s=pc(H&o[v]);
  return {P,C,X,Q,H,j,s};
}

function witness(d){
 const B=Array(d.n).fill(0);
 for(const e of d.bad)for(const x of ids(e.fa,d.n))for(const y of ids(e.fb,d.n)){B[x]|=1<<y;B[y]|=1<<x;}
 const col=Array(d.n).fill(-1);let L=0,R=0;
 for(const root of ids(d.Z,d.n))if(col[root]<0){
   const queue=[root],part=[[],[]];col[root]=0;
   for(let p=0;p<queue.length;p++){const x=queue[p];part[col[x]].push(x);for(const y of ids(B[x],d.n)){if(col[y]<0){col[y]=1-col[x];queue.push(y);}else if(col[y]===col[x])return null;}}
   if(part[0].length>part[1].length)part.reverse();
   for(const x of part[0])L|=1<<x;for(const x of part[1])R|=1<<x;
 }
 return {B,L,R};
}
function canonical(o,d,reverse){
 const rank=reference(d,reverse),T=o.slice();
 for(const e of d.missing)if(!e.fa||!e.fb){const f=!e.fa&&(!!e.fb||rank[e.a]<rank[e.b]);T[f?e.a:e.b]|=1<<(f?e.b:e.a);}return T;
}
const counts={graphs5:0,sampledGraphs:0,bipartiteBadGraphs:0,colouredCompletions:0,
 vertexEnvelopes:0,protectedSourceExactEqualities:0,noNewFirstUnselectedEqualities:0,
 addedBadFirstCases:0,nonnegativeSinkFreeTournaments6:0,zeroInducedNoSinkChecks:0};
let bipartiteControl=null;
function audit(o){
 const d=info(o);if(!d.bad.length)return;const W=witness(d);if(!W)return;counts.bipartiteBadGraphs++;
 for(const reverse of [false,true]){
  const T=canonical(o,d,reverse);
  for(const e of d.bad){
   const forward=!(e.fa&W.R);assert(forward?!(e.fb&W.L):!(e.fb&W.R),"opposite failure sets monochromatic",{o,e,W});
   T[forward?e.a:e.b]|=1<<(forward?e.b:e.a);
  }
  const a=info(T);counts.colouredCompletions++;
  for(let z=0;z<d.n;z++){
   const K=T[z]&d.M[z],env=(d.two[z]|d.F[z])&~K;
   assert(!(a.two[z]&~env),"bipartite completion exact-head envelope",{o,W,z,K,actual:a.two[z],env});
   assert(a.g[z]>=d.g[z]+2*pc(K)-pc(d.F[z]),"bipartite gap budget",{o,W,z});
   counts.vertexEnvelopes++;
   if(!d.F[z]){assert(a.two[z]===(d.two[z]&~K),"protected source exact equality",{o,z});counts.protectedSourceExactEqualities++;}
   if(!(W.L&(1<<z))&&!K){assert(a.two[z]===d.two[z],"unselected source without added first neighbours",{o,z,W});counts.noNewFirstUnselectedEqualities++;}
   if(d.bad.some(e=>(e.a===z&&(T[z]&(1<<e.b)))||(e.b===z&&(T[z]&(1<<e.a)))))counts.addedBadFirstCases++;
  }
  if(!bipartiteControl)bipartiteControl={out:o,L:ids(W.L,d.n),R:ids(W.R,d.n),completed:T};
 }
}
for(let c=0;c<59049;c++){let m=c;const o=Array(5).fill(0);for(let a=0;a<5;a++)for(let b=a+1;b<5;b++){const t=m%3;m=Math.floor(m/3);if(t===1)o[a]|=1<<b;if(t===2)o[b]|=1<<a;}audit(o);counts.graphs5++;}
let seed=0x5132026;function random(){seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;return(seed>>>0)/4294967296;}
for(let s=0;s<100000;s++){const n=6+s%7,density=[.3,.45,.6,.75,.9][s%5],o=Array(n).fill(0);for(let a=0;a<n;a++)for(let b=a+1;b<n;b++)if(random()<density){if(random()<.5)o[a]|=1<<b;else o[b]|=1<<a;}audit(o);counts.sampledGraphs++;}
for(let c=0;c<32768;c++){
 const o=Array(6).fill(0);let bit=0;for(let a=0;a<6;a++)for(let b=a+1;b<6;b++){if(c&(1<<bit))o[a]|=1<<b;else o[b]|=1<<a;bit++;}
 const d=info(o);if(o.some(x=>!x)||d.g.some(x=>x<0))continue;counts.nonnegativeSinkFreeTournaments6++;
 const S=d.g.reduce((m,g,x)=>!g?m|1<<x:m,0);
 assert(pc(S)>=3,"at least three zero gaps",{o,g:d.g});
 for(const x of ids(S,6))assert(o[x]&S,"zero-gap induced tournament has no sink",{o,g:d.g,S,x});
 counts.zeroInducedNoSinkChecks++;
}
const result={status:"PASS",counts,bipartiteControl,seed:"0x5132026",limits:["Actual graph envelope checks, not a search proof of SNC.","The zero-set theorem also has a mathematical weighted-perturbation proof; enumeration alone is not its proof."]};
fs.writeFileSync(path.join(__dirname,"audit_bipartite_witness_completion.results.json"),JSON.stringify(result,null,2)+"\n");console.log(JSON.stringify(result,null,2));

