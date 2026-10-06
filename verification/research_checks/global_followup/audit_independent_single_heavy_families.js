"use strict";
// Fresh, standalone predicates/order enumeration for the two-family proof.
const fs=require('fs'),path=require('path');
function demand(c,m,x){if(!c)throw Error(m+' '+JSON.stringify(x));}
function pc(x){let v=0;while(x){x&=x-1;v++;}return v;}
function vertices(m,n){const a=[];for(let x=0;x<n;x++)if(m&(1<<x))a.push(x);return a;}
const orders=new Map();for(let n=2;n<=7;n++){const a=[];function visit(p,left){if(!left.length){const rank=Array(n);p.forEach((x,i)=>rank[x]=i);a.push({p:p.slice(),rank});return;}for(let i=0;i<left.length;i++)visit(p.concat(left[i]),left.slice(0,i).concat(left.slice(i+1)));}visit([],Array.from({length:n},(_,x)=>x));orders.set(n,a);}
function score(out,p){let left=(1<<out.length)-1,result=0;for(const x of p){left&=~(1<<x);result+=pc(out[x]&left);}return result;}
function datum(out){
 const n=out.length,full=(1<<n)-1,inc=Array(n).fill(0),second=Array(n).fill(0);
 for(let x=0;x<n;x++)for(const y of vertices(out[x],n)){inc[y]|=1<<x;second[x]|=out[y];}
 for(let x=0;x<n;x++)second[x]&=full&~(out[x]|1<<x);
 const far=out.map((m,x)=>full&~(m|second[x]|1<<x)),protection=[];
 for(let x=0;x<n;x++)for(let y=0;y<n;y++)if((out[y]&(1<<x))&&!(inc[y]&~inc[x]))protection.push([y,x]);
 const unprotected=far.map((m,x)=>m&~protection.filter(p=>p[1]===x).reduce((r,p)=>r|1<<p[0],0));
 const edges=[],edgeAt=Array.from({length:n},()=>Array(n).fill(null));let actual=0;
 for(let a=0;a<n;a++)for(let b=a+1;b<n;b++)if(!((out[a]&(1<<b))||(out[b]&(1<<a)))){
  let fa=0,fb=0;for(let x=0;x<n;x++){if((out[x]&(1<<a))&&(far[x]&(1<<b)))fa|=1<<x;if((out[x]&(1<<b))&&(far[x]&(1<<a)))fb|=1<<x;}
  demand(!(fa&fb),'two failure sets overlap',{out,a,b,fa,fb});
  const e={a,b,fa,fb,bad:!!(fa&&fb),flex:(!fa&&!fb)||!!(fa&&fb)};edges.push(e);edgeAt[a][b]=edgeAt[b][a]=e;if(e.bad)actual|=fa|fb;
 }
 return {n,full,inc,second,far,protection,unprotected,edges,edgeAt,actual,g:out.map((m,x)=>pc(m)-pc(second[x]))};
}
function eligible(d,u){
 for(const x of vertices(d.actual&~(1<<u),d.n))if(pc(d.unprotected[x])>1)return false;
 for(const e of d.edges)if(e.bad)for(const x of vertices(e.fa&~(1<<u),d.n))for(const r of vertices(e.fb&~(1<<u),d.n)){
  const cross=d.edgeAt[x][r];demand(cross,'cross witnesses must be missing',{d,u,x,r});if(!cross.flex)return false;
 }
 return true;
}
function lexCompletion(out,d,u,avoidU){
 const fixed=out.slice(),flex=[];
 for(const e of d.edges){
  if(!e.bad&&!e.flex)fixed[e.fa?e.b:e.a]|=1<<(e.fa?e.a:e.b);
  else if(e.bad&&avoidU&&((e.fa|e.fb)&(1<<u))){const forward=!!(e.fb&(1<<u));fixed[forward?e.a:e.b]|=1<<(forward?e.b:e.a);}
  else flex.push(e);
 }
 let maximum=-1,chosen=null;for(const q of orders.get(d.n))if(d.protection.every(([y,x])=>q.rank[y]<q.rank[x])){
  const v=score(fixed,q.p);if(v>maximum||(v===maximum&&q.rank[u]>chosen.rank[u])){maximum=v;chosen=q;}
 }
 demand(chosen,'protection extension exists',{out,u});const T=fixed.slice();
 for(const e of flex){const forward=chosen.rank[e.a]<chosen.rank[e.b];T[forward?e.a:e.b]|=1<<(forward?e.b:e.a);}
 const td=datum(T);let selected=0;for(const e of d.edges)if(e.bad)selected|=(T[e.a]&(1<<e.b))?e.fa:e.fb;
 if(avoidU)demand(!(selected&(1<<u)),'restricted failures avoid u',{out,u,T});
 for(let x=0;x<d.n;x++){
  const K=T[x]&~out[x];demand(!(td.second[x]&~((d.second[x]|d.unprotected[x])&~K)),'family protection envelope',{out,u,T,x,avoidU});
 }
 const referenceScore=maximum+flex.length;for(const q of orders.get(d.n)){
  const v=score(T,q.p);demand(v<=referenceScore,'chosen order not global median',{out,u,T,order:q.p,avoidU});
  if(v===referenceScore){demand(q.rank[u]<=chosen.rank[u],'chosen median not secondary max',{out,u,T,order:q.p,chosen:chosen.p,avoidU});for(const e of flex){const forward=!!(T[e.a]&(1<<e.b));demand(forward?q.rank[e.a]<q.rank[e.b]:q.rank[e.b]<q.rank[e.a],'free FLEX backward in another median',{out,u,T,order:q.p,e,avoidU});}}
 }
 return {T,td,chosen,feed:chosen.p[d.n-1]};
}
const counts={graphs:0,eligibleVertices:0,heavyActualEligibleVertices:0,firstFamilyOriginalPositiveFeeds:0,secondFamilyRuns:0,secondFamilyHeavyRuns:0,secondFamilyPositiveFeeds:0};let activeControl=null;
function test(out){const d=datum(out);counts.graphs++;for(let u=0;u<d.n;u++)if(eligible(d,u)){
 counts.eligibleVertices++;if((d.actual&(1<<u))&&pc(d.unprotected[u])>1)counts.heavyActualEligibleVertices++;
 const first=lexCompletion(out,d,u,false),f=first.feed;
 if(d.g[f]>0){
  counts.firstFamilyOriginalPositiveFeeds++;demand(f===u,'phase one positive original feed not exceptional',{out,u,d,first});
  demand(!d.protection.some(([y,x])=>y===u),'phase one exception has protection successor',{out,u,d,first});
 }
 if(!d.protection.some(([y,x])=>y===u)){
  const second=lexCompletion(out,d,u,true);counts.secondFamilyRuns++;
  if((d.actual&(1<<u))&&pc(d.unprotected[u])>1)counts.secondFamilyHeavyRuns++;
  if(d.g[second.feed]>0)counts.secondFamilyPositiveFeeds++;
  demand(d.g[second.feed]<=0,'phase two still has originally deficient feed',{out,u,d,first,second});
  if(!activeControl&&(d.actual&(1<<u))&&pc(d.unprotected[u])>1)activeControl={out,u,firstFeed:first.feed,firstMedian:first.chosen.p,firstT:first.T,secondFeed:second.feed,secondMedian:second.chosen.p,secondT:second.T,originalGaps:d.g};
 }
}}
for(let n=2;n<=5;n++)for(let code=0;code<3**(n*(n-1)/2);code++){let c=code;const out=Array(n).fill(0);for(let a=0;a<n;a++)for(let b=a+1;b<n;b++){const v=c%3;c=Math.floor(c/3);if(v===1)out[a]|=1<<b;if(v===2)out[b]|=1<<a;}test(out);}
let state=0x511caffe;function random(){state^=state<<13;state^=state>>>17;state^=state<<5;return(state>>>0)/4294967296;}
for(let sample=0;sample<1200;sample++){const n=6+sample%2,out=Array(n).fill(0),density=.3+.6*(sample%5)/4;for(let a=0;a<n;a++)for(let b=a+1;b<n;b++)if(random()<density){if(random()<.5)out[a]|=1<<b;else out[b]|=1<<a;}test(out);}
test([0,36,17,34,2,4]);
const result={status:'PASS',counts,activeControl,scope:'Every oriented graph n=2..5; 1200 deterministic n=6/7 samples; known six-vertex arc-weighted-feed obstruction. Test applies to arbitrary graphs, not presumed minimal/all-deficient. Enumerates all orders. Does not prove SNC or existence of a counterexample.'};
fs.writeFileSync(path.join(__dirname,'audit_independent_single_heavy_families.results.json'),JSON.stringify(result,null,2)+'\n');console.log(JSON.stringify(result,null,2));
