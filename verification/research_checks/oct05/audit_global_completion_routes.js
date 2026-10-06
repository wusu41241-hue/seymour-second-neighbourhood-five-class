"use strict";
// Independent graph-level audits for global, not bounded-residual, routes.
const fs=require("fs"),path=require("path");
function demand(ok,msg,data){if(!ok)throw Error(msg+" "+JSON.stringify(data));}
function pc(m){let r=0;for(;m;m&=m-1)r++;return r;}
function ids(m,n){const r=[];for(let x=0;x<n;x++)if(m&(1<<x))r.push(x);return r;}
function data(out){
 const n=out.length,full=(1<<n)-1,inc=Array(n).fill(0),two=Array(n).fill(0),P=Array(n).fill(0);
 for(let x=0;x<n;x++)for(const q of ids(out[x],n)){demand(q!==x&&!(out[q]&(1<<x)),"oriented",{out,x,q});inc[q]|=1<<x;two[x]|=out[q];}
 for(let x=0;x<n;x++)two[x]&=full&~(out[x]|1<<x);
 const far=out.map((m,x)=>full&~(m|two[x]|1<<x));
 for(let x=0;x<n;x++)for(const y of ids(far[x],n))P[y]|=1<<x;
 const prot=far.map((m,x)=>ids(m,n).reduce((r,y)=>(out[y]&(1<<x))&&!(inc[y]&~inc[x])?r|1<<y:r,0));
 const F=far.map((m,x)=>m&~prot[x]),M=out.map((m,x)=>full&~(m|inc[x]|1<<x));
 const edges=[];let actual=0;
 for(let a=0;a<n;a++)for(let b=a+1;b<n;b++)if(M[a]&(1<<b)){
  const fa=inc[a]&P[b],fb=inc[b]&P[a];edges.push({a,b,fa,fb});if(fa&&fb)actual|=fa|fb;
 }
 return {n,full,inc,two,far,P,prot,F,M,edges,actual,g:out.map((m,x)=>pc(m)-pc(two[x]))};
}
function reference(d,reverse=false,targets=[]){
 const pred=d.prot.slice(),rank=Array(d.n);let left=d.full,index=0;
 for(const u of targets)for(const e of d.edges)if((e.a===u||e.b===u)&&!(e.fa&&e.fb))pred[u]|=1<<(e.a===u?e.b:e.a);
 while(left){const available=ids(left,d.n).filter(v=>!(pred[v]&left));if(!available.length)return null;const x=reverse?available.at(-1):available[0];rank[x]=index++;left&=~(1<<x);}
 return rank;
}
function completion(out,d,rank,badRule){
 const T=out.slice();let selected=0,badFirst=Array(d.n).fill(0);
 for(const e of d.edges){const bad=!!(e.fa&&e.fb);const forward=bad?badRule(e):!e.fa&&(!!e.fb||rank[e.a]<rank[e.b]);
  T[forward?e.a:e.b]|=1<<(forward?e.b:e.a);
  if(bad){selected|=forward?e.fa:e.fb;badFirst[forward?e.a:e.b]|=1<<(forward?e.b:e.a);}
 }
 return {T,selected,badFirst};
}
const counts={graphs5:0,randomGraphs:0,priorityCompletions:0,priorityVertexEnvelopes:0,
 priorityBadFirst:0,priorityMultipleBadFirst:0,priorityProtectedPairs:0,
 avoidingLargeCompletions:0,avoidingLargeWithActualLargeSources:0,
 avoidingLargeVertexEnvelopes:0,overlapPacketCompletions:0,positiveOverlapPackets:0,
 overlapBadKeepers:0};
let arbitraryBadViolation=null,seed=0x5105cafe;
function random(){seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;return(seed>>>0)/4294967296;}
function envelope(out,d,c,kind){
 const td=data(c.T);
 for(let x=0;x<d.n;x++){
  const K=c.T[x]&~out[x],bound=(d.two[x]|d.F[x])&~K;
  demand(!(td.two[x]&~bound),kind+" protected envelope",{out,T:c.T,x,K,d});
  demand(td.g[x]>=d.g[x]+2*pc(K)-pc(d.F[x]),kind+" gap bound",{out,T:c.T,x});
  demand(!(td.two[x]&d.prot[x]),kind+" preserves protected far heads",{out,T:c.T,x});
  if(!K&&!(c.selected&(1<<x)))demand(td.two[x]===d.two[x],kind+" exact persistence",{out,T:c.T,x});
  if(kind==="priority"){
   counts.priorityVertexEnvelopes++;counts.priorityProtectedPairs+=pc(d.prot[x]);
   if(c.badFirst[x])counts.priorityBadFirst++;if(pc(c.badFirst[x])>=2)counts.priorityMultipleBadFirst++;
  }else counts.avoidingLargeVertexEnvelopes++;
 }
}
function audit(out){
 const d=data(out);
 for(const reverse of [false,true]){
  const rank=reference(d,reverse);demand(rank,"canonical extension exists",out);
  const c=completion(out,d,rank,e=>rank[e.a]<rank[e.b]);envelope(out,d,c,"priority");counts.priorityCompletions++;
 }
 const H=d.F.reduce((m,f,x)=>pc(f)>1?m|1<<x:m,0);
 if(!d.edges.some(e=>e.fa&&e.fb&&(e.fa&H)&&(e.fb&H))){
  const rank=reference(d),c=completion(out,d,rank,e=>!(e.fa&H));
  demand(!(c.selected&H),"chosen failures avoid large sources",{out,H,c});
  envelope(out,d,c,"avoidingLarge");counts.avoidingLargeCompletions++;
  if(H&d.actual)counts.avoidingLargeWithActualLargeSources++;
 }
 for(let u=0;u<d.n;u++){
  const avoid=d.P[u]|1<<u;
  if(d.edges.some(e=>e.fa&&e.fb&&(e.fa&avoid)&&(e.fb&avoid)))continue;
  const rank=reference(d,false,[u]);demand(rank,"one target inward priorities acyclic",{out,u});
  const c=completion(out,d,rank,e=>!(e.fa&avoid)),td=data(c.T),K=c.T[u]&~out[u];
  demand(!(c.selected&avoid),"packet chosen failure avoidance",{out,u,c});
  counts.overlapPacketCompletions++;
  if(!d.P[u]){demand(!K&&td.two[u]===d.two[u],"empty packet persistence",{out,u});continue;}
  let C=0;for(const p of ids(d.P[u],d.n))C|=out[p];C&=d.full&~d.P[u];
  let X=0;for(const q of ids(C,d.n))X|=out[q];X&=d.full&~(d.P[u]|C);
  const Q=d.P.reduce((m,_,v)=>d.two[v]&(1<<u)?m|1<<v:m,0),B=(Q&~C)&d.M[u];
  const hat=out.slice();hat[u]&=~(Q&~C);const hd=data(hat);
  const E=(d.M[u]&~B)|X,L=E&~hd.two[u],overlap=d.M[u]&d.P[u];
  demand(!(K&B),"exceptional partners directed inward",{out,u,K,B});
  demand(pc(K)>=pc(d.M[u])-pc(B)-pc(overlap),"generalized keeper lower count",{out,u,K,B,overlap});
  demand(!(K&~(d.two[u]|L))&&!(td.two[u]&~((d.two[u]|L)&~K)),"overlap packet shared envelope",{out,u,K,L,c});
  demand(td.g[u]>=d.g[u]+2*pc(K)-pc(L),"overlap packet arithmetic",{out,u,K,L});
  if(overlap)counts.positiveOverlapPackets++;
  if(c.badFirst[u])counts.overlapBadKeepers++;
 }
 if(!arbitraryBadViolation){
  const rank=reference(d),c=completion(out,d,rank,e=>true),td=data(c.T);
  for(let x=0;x<d.n;x++)if(td.two[x]&d.prot[x]){arbitraryBadViolation={out,T:c.T,source:x,newProtectedHeads:ids(td.two[x]&d.prot[x],d.n)};break;}
 }
}
for(let code=0;code<59049;code++){let q=code;const out=Array(5).fill(0);for(let a=0;a<5;a++)for(let b=a+1;b<5;b++){const z=q%3;q=Math.floor(q/3);if(z===1)out[a]|=1<<b;if(z===2)out[b]|=1<<a;}audit(out);counts.graphs5++;}
for(let s=0;s<30000;s++){const n=6+s%7,out=Array(n).fill(0),density=[.3,.45,.6,.75,.9][s%5];for(let a=0;a<n;a++)for(let b=a+1;b<n;b++)if(random()<density){if(random()<.5)out[a]|=1<<b;else out[b]|=1<<a;}audit(out);counts.randomGraphs++;}
// Explicit failed shortcuts; none is a Seymour counterexample.
const orderControl=[26,52,41,0,0,0],oc=data(orderControl);
demand(reference(oc,false,[0,1,2])===null,"three inward priority families need not coexist");
const strongOrderControl=[26,52,41,64,128,256,18,36,9],soc=data(strongOrderControl);
demand(reference(soc,false,[0,1,2])===null,"priority conflict persists in a strong control");
const matrixControl=[2,4,24,17,3],weights=[1,2,2,1,1],mc=data(matrixControl);
const wsum=m=>ids(m,5).reduce((r,x)=>r+weights[x],0);
const skew=matrixControl.map((m,x)=>wsum(m)-wsum(mc.inc[x])),weightedGap=matrixControl.map((m,x)=>wsum(m)-wsum(mc.two[x]));
demand(skew.every(x=>x===0)&&weightedGap[4]===1,"positive skew-equilibrium is not automatically an expansion weighting",{skew,weightedGap});
const protectedControl=[0,0,1,2,5],pcd=data(protectedControl);
const heavy=pcd.F.reduce((m,f,x)=>pc(f)>1?m|1<<x:m,0);
const obstruction=pcd.edges.find(e=>e.fa&&e.fb&&(e.fa&heavy)&&(e.fb&heavy));
demand(obstruction,"large-source avoidance can be impossible",pcd);
const controls={threeTargetPriorities:{out:orderControl,targets:[0,1,2],protectedRelations:[[0,3],[1,4],[2,5]],newPrecedences:[[3,1],[4,2],[5,0]],originalGaps:oc.g},
 strongThreeTargetPriorities:{out:strongOrderControl,targets:[0,1,2],originalGaps:soc.g},
 skewWeighting:{out:matrixControl,positiveWeights:weights,skewBalance:skew,weightedGaps:weightedGap,originalGaps:mc.g},
 largeSourceAvoidance:{out:protectedControl,largeSources:ids(heavy,5),badPair:[obstruction.a,obstruction.b],forwardFailures:ids(obstruction.fa,5),reverseFailures:ids(obstruction.fb,5),originalGaps:pcd.g},arbitraryBadViolation};
demand(counts.priorityMultipleBadFirst>0&&counts.positiveOverlapPackets>0&&counts.avoidingLargeWithActualLargeSources>0,"nonvacuous audits",counts);
const result={status:"PASS",seed:"0x5105cafe",counts,controls,limits:[
 "Every audit graph is an arbitrary oriented graph, not assumed minimal or all-deficient.",
 "The packet audit tests overlap keeper counts and path envelopes, not the strict external-boundary or residual inequalities on arbitrary graphs.",
 "Control graphs refute generic shortcuts only; none refutes SSNC or a theorem restricted to actual minimal counterexamples.",
 "The finite checks are not an all-order proof. Global existence of a strict-budget completion remains unresolved."]};
fs.writeFileSync(path.join(__dirname,"audit_global_completion_routes.results.json"),JSON.stringify(result,null,2)+"\n");
console.log(JSON.stringify(result,null,2));
