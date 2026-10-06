"use strict";
const fs=require('fs'),path=require('path');
function check(v,s,d){if(!v)throw Error(s+' '+JSON.stringify(d));}
function pc(m){let v=0;while(m){m&=m-1;v++;}return v;}
function ids(m,n){const a=[];for(let x=0;x<n;x++)if(m&(1<<x))a.push(x);return a;}
const permutations=new Map();for(let n=2;n<=7;n++){const a=[];function go(p,left){if(!left.length){const rank=Array(n);p.forEach((x,i)=>rank[x]=i);a.push({p:p.slice(),rank});return;}for(let i=0;i<left.length;i++)go(p.concat(left[i]),left.slice(0,i).concat(left.slice(i+1)));}go([],Array.from({length:n},(_,x)=>x));permutations.set(n,a);}
function score(out,p){let left=(1<<out.length)-1,v=0;for(const x of p){left&=~(1<<x);v+=pc(out[x]&left);}return v;}
function data(out){
 const n=out.length,full=(1<<n)-1,inc=Array(n).fill(0),two=Array(n).fill(0);
 for(let x=0;x<n;x++)for(const y of ids(out[x],n)){inc[y]|=1<<x;two[x]|=out[y];}
 for(let x=0;x<n;x++)two[x]&=full&~(out[x]|1<<x);
 const far=out.map((m,x)=>full&~(m|two[x]|1<<x)),P=[];
 for(let y=0;y<n;y++)for(let x=0;x<n;x++)if((out[y]&(1<<x))&&!(inc[y]&~inc[x]))P.push([y,x]);
 const F=far.map((m,x)=>m&~P.filter(p=>p[1]===x).reduce((z,p)=>z|1<<p[0],0)),missing=out.map((m,x)=>full&~(m|inc[x]|1<<x));
 const edges=[];for(let a=0;a<n;a++)for(let b=a+1;b<n;b++)if(missing[a]&(1<<b)){
  let fa=0,fb=0;for(let x=0;x<n;x++){if((out[x]&(1<<a))&&(far[x]&(1<<b)))fa|=1<<x;if((out[x]&(1<<b))&&(far[x]&(1<<a)))fb|=1<<x;}
  const forceAB=P.some(([y,w])=>y===a&&(out[w]&(1<<b))),forceBA=P.some(([y,w])=>y===b&&(out[w]&(1<<a)));
  check(!(forceAB&&forceBA),'opposite forced directions',{out,a,b});
  if(forceAB)check(!fa&&!!fb,'forced AB not unique convenient',{out,a,b,fa,fb});
  if(forceBA)check(!fb&&!!fa,'forced BA not unique convenient',{out,a,b,fa,fb});
  edges.push({a,b,fa,fb,forceAB,forceBA});
 }
 return {n,full,inc,two,far,P,F,missing,edges,g:out.map((m,x)=>pc(m)-pc(two[x]))};
}
const counts={graphs:0,enlargedReferenceCompletions:0,forcedDirections:0,releasedUniqueGoodReversals:0,vertexEnvelopes:0,maximalMedianOrders:0,feedNoAddedFirstChecks:0,forcedIncomingBoundaryChecks:0,fullBoundaryVertices:0,nonemptyFullBoundaryVertices:0,positiveOriginalMaxFeeds:0};let noncontainmentControl=null,positiveOriginalFeedControl=null;
function tournament(out,d,ref){const T=out.slice();for(const e of d.edges){const forward=e.forceAB||(!e.forceBA&&ref.rank[e.a]<ref.rank[e.b]);T[forward?e.a:e.b]|=1<<(forward?e.b:e.a);if((!e.fa)!==(!e.fb)&&!e.forceAB&&!e.forceBA&&((forward&&!!e.fa)||(!forward&&!!e.fb)))counts.releasedUniqueGoodReversals++;}return T;}
function envelope(out,d,T){const td=data(T);for(const[y,x]of d.P)check((T[y]&(1<<x))&&!(td.inc[y]&~td.inc[x]),'lost original protection',{out,T,y,x});for(let x=0;x<d.n;x++){
 const K=T[x]&~out[x],A=td.two[x]&d.far[x],c=pc(K&d.F[x])+pc(A);
 check(!(td.two[x]&~((d.two[x]|d.F[x])&~K)),'enlarged envelope',{out,T,x});
 check(c<=pc(d.F[x])&&td.g[x]-d.g[x]===2*pc(K)-c,'exact disjoint cost',{out,T,x,K,A,c});counts.vertexEnvelopes++;
}}
function oldContained(out,d,ref){const T=out.slice();for(const e of d.edges){const bad=!!(e.fa&&e.fb),forward=bad?ref.rank[e.a]<ref.rank[e.b]:!e.fa&&(!!e.fb||ref.rank[e.a]<ref.rank[e.b]);T[forward?e.a:e.b]|=1<<(forward?e.b:e.a);}
 const pred=Array(d.n).fill(0);for(const[y,x]of d.P)pred[x]|=1<<y;
 const released=[];for(const e of d.edges)if(!e.forceAB&&!e.forceBA){const tail=T[e.a]&(1<<e.b)?e.a:e.b,head=tail===e.a?e.b:e.a;pred[head]|=1<<tail;released.push([tail,head]);}
 let remaining=d.full;while(remaining){const available=ids(remaining,d.n).filter(x=>!(pred[x]&remaining));if(!available.length)return {out,canonicalReference:ref.p,canonicalT:T,originalProtection:d.P,releasedDirections:released,cyclicVertices:ids(remaining,d.n)};for(const x of available)remaining&=~(1<<x);}
 return null;
}
function attack(out){const d=data(out),orders=permutations.get(d.n),valid=orders.filter(q=>d.P.every(([y,x])=>q.rank[y]<q.rank[x]));check(valid.length,'no P extension',{out});counts.graphs++;counts.forcedDirections+=d.edges.filter(e=>e.forceAB||e.forceBA).length;
 for(let f=0;f<d.n;f++){
  let Pf=0,C=0,Q=0;for(let p=0;p<d.n;p++){if(d.far[p]&(1<<f))Pf|=1<<p;if(d.two[p]&(1<<f))Q|=1<<p;}
  for(const p of ids(Pf,d.n))C|=out[p];C&=d.full&~Pf;
  if(C===Q){counts.fullBoundaryVertices++;if(Pf)counts.nonemptyFullBoundaryVertices++;}
  for(const e of d.edges)if((e.forceAB&&e.b===f)||(e.forceBA&&e.a===f)){const r=e.a===f?e.b:e.a;check((Q&(1<<r))&&!(C&(1<<r)),'forced incoming has no boundary defect',{out,f,r,Pf,C,Q,e});counts.forcedIncomingBoundaryChecks++;}
 }
 for(const ref of [valid[0],valid.at(-1)]){const T=tournament(out,d,ref);envelope(out,d,T);counts.enlargedReferenceCompletions++;if(!noncontainmentControl)noncontainmentControl=oldContained(out,d,ref);}
 const fixed=out.slice();for(const e of d.edges)if(e.forceAB||e.forceBA)fixed[e.forceAB?e.a:e.b]|=1<<(e.forceAB?e.b:e.a);
 let best=-1,ref;for(const q of valid){const v=score(fixed,q.p);if(v>best){best=v;ref=q;}}
 const T=tournament(out,d,ref),expected=best+d.edges.filter(e=>!e.forceAB&&!e.forceBA).length;
 for(const q of orders){const v=score(T,q.p);check(v<=expected,'candidate not max median',{out,T,q});if(v===expected){counts.maximalMedianOrders++;check(d.P.every(([y,x])=>q.rank[y]<q.rank[x]),'max median P inversion',{out,T,q});for(const e of d.edges)if(!e.forceAB&&!e.forceBA){const tail=T[e.a]&(1<<e.b)?e.a:e.b,head=tail===e.a?e.b:e.a;check(q.rank[tail]<q.rank[head],'released arc backward in max median',{out,T,q,e});}const f=q.p[d.n-1];check(!(T[f]&~out[f]),'added outgoing max feed',{out,T,q,f});counts.feedNoAddedFirstChecks++;if(d.g[f]>0){counts.positiveOriginalMaxFeeds++;if(!positiveOriginalFeedControl){const td=data(T);let Pf=0,C=0,Q=0;for(let p=0;p<d.n;p++){if(d.far[p]&(1<<f))Pf|=1<<p;if(d.two[p]&(1<<f))Q|=1<<p;}for(const p of ids(Pf,d.n))C|=out[p];C&=d.full&~Pf;positiveOriginalFeedControl={out,T,median:q.p,feed:f,reference:ref.p,originalGaps:d.g,completedGap:td.g[f],unprotectedFarHeads:ids(d.F[f],d.n),newFarSecondHeads:ids(td.two[f]&d.far[f],d.n),missingPartners:ids(d.missing[f],d.n),P:ids(Pf,d.n),C:ids(C,d.n),Q:ids(Q,d.n),actualBadSource:d.edges.some(e=>e.fa&&e.fb&&((e.fa|e.fb)&(1<<f)))};}}}}
}
for(let n=2;n<=5;n++)for(let code=0;code<3**(n*(n-1)/2);code++){let c=code;const out=Array(n).fill(0);for(let a=0;a<n;a++)for(let b=a+1;b<n;b++){const v=c%3;c=Math.floor(c/3);if(v===1)out[a]|=1<<b;if(v===2)out[b]|=1<<a;}attack(out);}
let state=0x510faace;function random(){state=(Math.imul(state,1664525)+1013904223)>>>0;return state/4294967296;}
for(let trial=0;trial<1200;trial++){const n=6+trial%2,out=Array(n).fill(0),density=.25+.7*(trial%5)/4;for(let a=0;a<n;a++)for(let b=a+1;b<n;b++)if(random()<density){if(random()<.5)out[a]|=1<<b;else out[b]|=1<<a;}attack(out);}
attack([0,49,51,6,9,8]);
const result={status:'PASS',counts,noncontainmentControl,positiveOriginalFeedControl,scope:'All oriented graphs n=2..5 plus 1200 deterministic n=6/7 controls and the canonical-only budget obstruction. Fresh predicates, all orders enumerated, first/last protection extensions attacked. No all-deficient assumption or proof of SNC.'};fs.writeFileSync(path.join(__dirname,'audit_independent_protection_forced.results.json'),JSON.stringify(result,null,2)+'\n');console.log(JSON.stringify(result,null,2));
