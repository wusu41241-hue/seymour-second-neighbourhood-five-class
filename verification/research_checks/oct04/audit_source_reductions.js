"use strict";
// Exact checks of the new source reductions, including global median orders.
// Global median optimization uses dynamic programming over subsets, not a heuristic.
const fs=require("fs"),path=require("path");
function pc(x){let c=0;for(;x;x&=x-1)c++;return c;}
function ids(x,n){const a=[];for(let i=0;i<n;i++)if(x&(1<<i))a.push(i);return a;}
function check(ok,msg,d){if(!ok)throw Error(msg+JSON.stringify(d));}
function second(o,f){let r=0;for(const a of ids(o[f],o.length))r|=o[a];return r&~(o[f]|1<<f);}
function info(o){
  const n=o.length,full=(1<<n)-1,inc=Array(n).fill(0),P=Array(n).fill(0),two=[],far=[];
  for(let x=0;x<n;x++)for(const y of ids(o[x],n))inc[y]|=1<<x;
  for(let x=0;x<n;x++){two[x]=second(o,x);far[x]=full&~(o[x]|two[x]|1<<x);for(const y of ids(far[x],n))P[y]|=1<<x;}
  const prot=far.map((m,x)=>ids(m,n).reduce((r,y)=>(o[y]&(1<<x))&&!(inc[y]&~inc[x])?r|1<<y:r,0));
  const F=far.map((m,x)=>m&~prot[x]),M=o.map((m,x)=>full&~(m|inc[x]|1<<x)),bad=[],missing=[];let Z=0;
  for(let a=0;a<n;a++)for(let b=a+1;b<n;b++)if(M[a]&(1<<b)){
    const fa=inc[a]&P[b],fb=inc[b]&P[a];missing.push({a,b,fa,fb});if(fa&&fb){bad.push({a,b,fa,fb});Z|=fa|fb;}
  }
  return {n,full,inc,two,far,prot,F,M,bad,missing,Z};
}
function goodCompletion(o,d,reverse=false){
  const T=o.slice(),rank=Array(d.n);let left=d.full,pos=0;
  while(left){let a=ids(left,d.n).filter(v=>!(d.prot[v]&left));if(reverse)a.reverse();const v=a[0];check(v!==undefined,"protection acyclic",o);rank[v]=pos++;left&=~(1<<v);}
  for(const{a,b,fa,fb}of d.missing)if(!fa||!fb){const dir=!fa&&(!!fb||rank[a]<rank[b]);T[dir?a:b]|=1<<(dir?b:a);}
  return T;
}
function optimize(T){
  const n=T.length,full=(1<<n)-1,inc=Array(n).fill(0);for(let a=0;a<n;a++)for(const b of ids(T[a],n))inc[b]|=1<<a;
  const dp=Array(full+1).fill(-1),last=Array(full+1).fill(-1);dp[0]=0;
  for(let m=1;m<=full;m++)for(const v of ids(m,n)){const p=m&~(1<<v),s=dp[p]+pc(inc[v]&p);if(s>dp[m]){dp[m]=s;last[m]=v;}}
  const feeds=ids(full,n).filter(v=>dp[full&~(1<<v)]+pc(inc[v])===dp[full]);
  function order(feed){const a=[feed];let m=full&~(1<<feed);while(m){const v=last[m];a.push(v);m&=~(1<<v);}return a.reverse();}
  return {score:dp[full],feeds,order};
}
function score(T,L){let s=0;for(let i=0;i<L.length;i++)for(let j=i+1;j<L.length;j++)if(T[L[i]]&(1<<L[j]))s++;return s;}
function sediment(T,L){
  const n=T.length,f=L[n-1];let G=0;
  for(let j=0;j<n-1;j++)if(T[L[j]]&(1<<f))for(let i=0;i<j;i++)if((T[f]&(1<<L[i]))&&(T[L[i]]&(1<<L[j])))G|=1<<L[j];
  check(pc(T[f])<=pc(G),"strong feed theorem",{T,L,G});
  if(pc(T[f])!==pc(G))return null;
  const rest=T[f]|G,B=L.filter(v=>v!==f&&!(rest&(1<<v))),R=L.filter(v=>rest&(1<<v));
  return [...B,f,...R];
}
const counts={graphs5:0,sampledGraphs:0,unitFourSourceBadGraphs:0,internalBadMatchingCases:0,
  reciprocalCycleCases:0,reciprocalOrientationCases:0,singleVulnerablePositiveCases:0,
  singleVulnerableOriginalSeymourTransfers:0,sedimentationEqualityChecks:0};
let reciprocalControl=null;
function audit(o){
  const d=info(o);if(!d.bad.length)return;
  if(pc(d.Z)<=4&&ids(d.Z,d.n).every(x=>pc(d.F[x])<=1)){
    counts.unitFourSourceBadGraphs++;const internal=d.bad.filter(e=>(d.Z&(1<<e.a))&&(d.Z&(1<<e.b)));let used=0;
    for(const e of internal){check(!(used&((1<<e.a)|(1<<e.b))),"internal bad pairs form a matching",{o,internal});used|=1<<e.a|1<<e.b;}
    counts.internalBadMatchingCases++;check(internal.length<=2,"at most two internal bad pairs",{o,internal});
    if(internal.length===2){
      counts.reciprocalCycleCases++;check(d.bad.length===2,"no external bad pair in reciprocal case",{o,d});
      for(const x of ids(d.Z,d.n))check(pc(d.F[x])===1&&(o[ids(d.F[x],d.n)[0]]&(1<<x)),"unique head is original incoming cycle neighbour",{o,x});
      for(let choice=0;choice<4;choice++){
        const T=goodCompletion(o,d);let failure=0;
        internal.forEach((e,k)=>{const forward=!(choice&(1<<k));T[forward?e.a:e.b]|=1<<(forward?e.b:e.a);failure|=forward?e.fa:e.fb;});
        let unsafe=0;for(const x of ids(failure,d.n))if(!(T[x]&d.M[x]&d.Z))unsafe|=1<<x;
        check(pc(unsafe)===1,"exactly one internally unsupported failure source",{o,choice,unsafe});counts.reciprocalOrientationCases++;
      }
      if(!reciprocalControl)reciprocalControl={out:o,Z:d.Z};
    }
  }
  if(pc(d.Z)<=2)for(const v of ids(d.Z,d.n))if(pc(d.F[v])<=1&&pc(o[v])>pc(d.two[v])){
    for(const reverse of [false,true]){
      const T=goodCompletion(o,d,reverse);
      for(const e of d.bad){const forward=e.fa===(1<<v);check(forward||e.fb===(1<<v),"bad direction with sole unit source",{o,v,e});T[forward?e.a:e.b]|=1<<(forward?e.b:e.a);}
      check(d.missing.filter(e=>e.a===v||e.b===v).every(e=>!e.fa||!e.fb),"unit source incident pairs are good",{o,v});
      const med=optimize(T),f=med.feeds.find(x=>x!==v);
      check(f!==undefined,"positive unit source cannot be the sole global median feed",{o,v,T,feeds:med.feeds});
      check(pc(o[f])<=pc(d.two[f]),"other median feed is an original Seymour vertex",{o,v,f});
      counts.singleVulnerablePositiveCases++;counts.singleVulnerableOriginalSeymourTransfers++;
      for(const feed of med.feeds){const L=med.order(feed),S=sediment(T,L);if(S){check(score(T,S)===med.score,"global sedimentation preserves score",{T,L,S});counts.sedimentationEqualityChecks++;}}
    }
  }
}
for(let code=0;code<59049;code++){
  let c=code;const o=Array(5).fill(0);for(let a=0;a<5;a++)for(let b=a+1;b<5;b++){const d=c%3;c=Math.floor(c/3);if(d===1)o[a]|=1<<b;if(d===2)o[b]|=1<<a;}
  audit(o);counts.graphs5++;
}
let seed=0x71042026;function random(){seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;return(seed>>>0)/4294967296;}
for(let sample=0;sample<20000;sample++){
  const n=6+sample%5,density=[.4,.6,.8,.95][sample%4],o=Array(n).fill(0);for(let a=0;a<n;a++)for(let b=a+1;b<n;b++)if(random()<density){if(random()<.5)o[a]|=1<<b;else o[b]|=1<<a;}
  audit(o);counts.sampledGraphs++;
}
check(counts.reciprocalCycleCases>0,"nonvacuous reciprocal classification");
check(counts.singleVulnerablePositiveCases>0,"nonvacuous positive unit feed exclusion");
const result={status:"PASS",counts,reciprocalControl,seed:"0x71042026",scope:"Verifies actual graph classification, completion directions, exact global median-feed sets and original Seymour transfers; does not assume sampled graphs are minimal all-deficient counterexamples."};
fs.writeFileSync(path.join(__dirname,"audit_source_reductions.results.json"),JSON.stringify(result,null,2)+"\n");console.log(JSON.stringify(result,null,2));
