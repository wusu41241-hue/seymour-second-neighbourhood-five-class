"use strict";
// Fresh independent iteration, protection, complete-order and feed-cost audit.
const fs=require('fs'),path=require('path');
function ok(v,s,d){if(!v)throw Error(s+' '+JSON.stringify(d));}
function pc(m){let a=0;while(m){m&=m-1;a++;}return a;}
function ids(m,n){const a=[];for(let x=0;x<n;x++)if(m&(1<<x))a.push(x);return a;}
const orders=new Map();for(let n=2;n<=7;n++){const a=[];function walk(p,left){if(!left.length){const rank=Array(n);p.forEach((x,i)=>rank[x]=i);a.push({p:p.slice(),rank});return;}for(let i=0;i<left.length;i++)walk(p.concat(left[i]),left.slice(0,i).concat(left.slice(i+1)));}walk([],Array.from({length:n},(_,x)=>x));orders.set(n,a);}
function score(out,p){let left=(1<<out.length)-1,s=0;for(const x of p){left&=~(1<<x);s+=pc(out[x]&left);}return s;}
function data(out){
 const n=out.length,full=(1<<n)-1,inc=Array(n).fill(0),two=Array(n).fill(0);
 for(let x=0;x<n;x++)for(const y of ids(out[x],n)){ok(x!==y&&!(out[y]&(1<<x)),'oriented invariant',{out,x,y});inc[y]|=1<<x;two[x]|=out[y];}
 for(let x=0;x<n;x++)two[x]&=full&~(out[x]|1<<x);
 const far=out.map((m,x)=>full&~(m|two[x]|1<<x)),P=[];
 for(let y=0;y<n;y++)for(let x=0;x<n;x++)if((out[y]&(1<<x))&&!(inc[y]&~inc[x]))P.push([y,x]);
 const F=far.map((m,x)=>m&~P.filter(([y,z])=>z===x).reduce((r,[y])=>r|1<<y,0));
 const edges=[];for(let a=0;a<n;a++)for(let b=a+1;b<n;b++)if(!((out[a]&(1<<b))||(out[b]&(1<<a)))){
  let fa=0,fb=0;for(let r=0;r<n;r++){if((out[r]&(1<<a))&&(far[r]&(1<<b)))fa|=1<<r;if((out[r]&(1<<b))&&(far[r]&(1<<a)))fb|=1<<r;}
  const ab=P.find(([y,w])=>y===a&&(out[w]&(1<<b))),ba=P.find(([y,w])=>y===b&&(out[w]&(1<<a)));
  ok(!(ab&&ba),'conflicting simultaneous force',{out,a,b});if(ab)ok(!fa&&fb,'AB force not uniquely convenient',{out,a,b,fa,fb});if(ba)ok(!fb&&fa,'BA force not uniquely convenient',{out,a,b,fa,fb});
  edges.push({a,b,fa,fb,ab,ba});
 }
 return {n,full,inc,two,far,P,F,edges,g:out.map((m,x)=>pc(m)-pc(two[x]))};
}
const counts={graphs:0,closureStagesWithAdditions:0,closureAddedArcs:0,weakSingleSteps:0,multistageGraphs:0,maxClosureStages:0,completedClosures:0,partialMedianOrders:0,finalMedianOrders:0,originalFirstSecondFeedChecks:0,positiveOriginalFeeds:0,strictSurplusChecks:0,zeroGapRemainingMissingChecks:0,strongGoodEqualityChecks:0};
let multistageControl=null,positiveFeedControl=null;
function attack(out){
 const original=data(out),n=out.length,stages=[out.slice()],tails=[];let Q=out.slice(),qd=original;
 while(true){const force=qd.edges.filter(e=>e.ab||e.ba);let weak=null;
  if(!force.length){for(const e of qd.edges){if(!(qd.inc[e.a]&~qd.inc[e.b])&&!qd.P.some(([y])=>y===e.b)){weak=[e.a,e.b];break;}if(!(qd.inc[e.b]&~qd.inc[e.a])&&!qd.P.some(([y])=>y===e.a)){weak=[e.b,e.a];break;}}if(!weak)break;}
  const next=Q.slice();
  if(force.length){for(const e of force){const tail=e.ab?e.a:e.b,head=e.ab?e.b:e.a,w=e.ab?e.ab[1]:e.ba[1];next[tail]|=1<<head;tails.push([tail,w]);counts.closureAddedArcs++;}}
  else {const[a,b]=weak;ok(!(qd.inc[a]&~qd.inc[b])&&!qd.P.some(([y])=>y===b),'unsafe weak step chosen',{out,Q,weak});next[a]|=1<<b;tails.push([a,b]);counts.closureAddedArcs++;counts.weakSingleSteps++;}
  const nd=data(next);for(const[y,x]of qd.P)ok((next[y]&(1<<x))&&!(nd.inc[y]&~nd.inc[x]),'simultaneous force loses current protection',{out,Q,next,y,x});
  Q=next;qd=nd;stages.push(Q.slice());counts.closureStagesWithAdditions++;ok(stages.length<=1+n*(n-1)/2,'nontermination',{out,stages});
 }
 const additions=stages.length-1;counts.graphs++;if(additions>1){counts.multistageGraphs++;if(!multistageControl)multistageControl={out,stages};}counts.maxClosureStages=Math.max(counts.maxClosureStages,additions);if(!qd.edges.length)counts.completedClosures++;
 for(const[y,x]of original.P)ok((Q[y]&(1<<x))&&!(qd.inc[y]&~qd.inc[x]),'closure loses original protection',{out,Q,y,x});
 for(const[r,w]of tails)ok(qd.P.some(([y,x])=>y===r&&x===w),'added tail successor not retained',{out,Q,r,w});
 for(const[y,x]of qd.P)ok(!(Q[x]&~Q[y]),'stable protection lacks outgoing nesting',{out,Q,y,x});
 let top=-1,ref;const all=orders.get(n);for(const q of all)if(qd.P.every(([y,x])=>q.rank[y]<q.rank[x])){const v=score(Q,q.p);if(v>top||(v===top&&original.g[q.p[n-1]]>original.g[ref.p[n-1]])){top=v;ref=q;}}
 ok(ref,'no final protection extension',{out,Q});
 for(const q of all){const v=score(Q,q.p);ok(v<=top,'partial unrestricted median exceeds protected max',{out,Q,q});if(v===top){counts.partialMedianOrders++;ok(qd.P.every(([y,x])=>q.rank[y]<q.rank[x]),'stable partial median inverts protection',{out,Q,q});}}
 const T=Q.slice();for(const e of qd.edges){const forward=ref.rank[e.a]<ref.rank[e.b];T[forward?e.a:e.b]|=1<<(forward?e.b:e.a);}const td=data(T),maximum=top+qd.edges.length;
 for(const[y,x]of qd.P)ok((T[y]&(1<<x))&&!(td.inc[y]&~td.inc[x]),'final completion loses closure protection',{out,Q,T,y,x});
 for(const q of all){const v=score(T,q.p);ok(v<=maximum,'chosen final reference not globally maximizing',{out,Q,T,q});if(v===maximum){
  counts.finalMedianOrders++;ok(qd.P.every(([y,x])=>q.rank[y]<q.rank[x]),'final median inverts closure protection',{out,Q,T,q});
  for(const e of qd.edges){const tail=T[e.a]&(1<<e.b)?e.a:e.b,head=tail===e.a?e.b:e.a;ok(q.rank[tail]<q.rank[head],'remaining free arc backward',{out,Q,T,q,e});}
  const f=q.p[n-1];ok(T[f]===out[f],'final feed acquires original-added first',{out,Q,T,q,f});
  for(const stage of stages){const sd=data(stage);ok(stage[f]===out[f]&&sd.two[f]===original.two[f],'feed closure first/second changes',{out,stage,Q,T,q,f});}
  counts.originalFirstSecondFeedChecks++;
  const A=td.two[f]&original.far[f];ok(!(A&~original.F[f]),'new head originally protected',{out,Q,T,q,f,A});ok(td.g[f]===original.g[f]-pc(A),'feed exact cost identity',{out,Q,T,q,f,A});
  if(!qd.edges.some(e=>e.a===f||e.b===f))ok(td.two[f]===qd.two[f],'whole closure feed gains new second',{out,Q,T,q,f});
  if(original.g[f]>0){counts.positiveOriginalFeeds++;ok(pc(original.F[f])>=original.g[f]+1,'strict-surplus theorem fails',{out,Q,T,q,f,original});counts.strictSurplusChecks++;
   const remainingMissing=qd.full&~(Q[f]|qd.inc[f]|1<<f);ok(remainingMissing,'positive original feed is whole in terminal closure',{out,Q,T,q,f});
   let sedimentation=null,Ggood=0;for(const y of ids(td.inc[f],n))if(ids(T[f],n).some(a=>q.rank[a]<q.rank[y]&&(T[a]&(1<<y))))Ggood|=1<<y;
   ok(pc(Ggood)>=pc(T[f]),'strong feed inequality fails',{out,Q,T,q,f,Ggood});
   if(pc(Ggood)===pc(T[f])){counts.strongGoodEqualityChecks++;ok(pc(remainingMissing)<=pc(original.F[f])-original.g[f],'strong good equality missing-degree budget fails',{out,Q,T,q,f,Ggood,remainingMissing});}
   if(td.g[f]===0){counts.zeroGapRemainingMissingChecks++;ok(pc(remainingMissing)>=3,'weak-stable zero-gap original-positive feed lacks three missing partners',{out,Q,T,q,f,remainingMissing});for(const r of ids(remainingMissing,n))ok(qd.inc[r]&remainingMissing,'zero-gap terminal missing core lacks internal predecessor',{out,Q,T,q,f,r,remainingMissing});let acyclicLeft=remainingMissing;while(acyclicLeft){const sources=ids(acyclicLeft,n).filter(r=>!(original.inc[r]&acyclicLeft));if(!sources.length)break;for(const r of sources)acyclicLeft&=~(1<<r);}ok(acyclicLeft,'zero-gap final missing core has no original cycle',{out,Q,T,q,f,remainingMissing});ok(!(remainingMissing&~td.far[f])&&!(remainingMissing&~(original.F[f]&~A)),'zero gap missing is not unpaid far',{out,Q,T,q,f,remainingMissing,A});ok(pc(original.F[f])>=original.g[f]+pc(remainingMissing),'zero gap missing-degree budget fails',{out,Q,T,q,f,remainingMissing,A});
    const O=T[f],G=td.two[f],B=td.full&~(O|G|1<<f);sedimentation=q.p.filter(x=>B&(1<<x)).concat(f,q.p.filter(x=>(O|G)&(1<<x)));ok(score(T,sedimentation)===maximum,'zero-gap sedimentation loses score',{out,Q,T,q,f,sedimentation});
   }else ok(td.g[f]<0&&pc(A)>=original.g[f]+1,'strict completed gap does not charge extra head',{out,Q,T,q,f,A});
   if(!positiveFeedControl)positiveFeedControl={out,Q,T,median:q.p,feed:f,gOriginal:original.g[f],gCompleted:td.g[f],tOriginal:pc(original.F[f]),strongGoodVertices:ids(Ggood,n),strongGoodSlack:pc(Ggood)-pc(T[f]),newHeads:ids(A,n),remainingMissing:ids(remainingMissing,n),finalFar:ids(td.far[f],n),sedimentation,originalGaps:original.g,closureStages:additions};
  }
 }}
}
for(let n=2;n<=5;n++)for(let code=0;code<3**(n*(n-1)/2);code++){let c=code;const out=Array(n).fill(0);for(let a=0;a<n;a++)for(let b=a+1;b<n;b++){const v=c%3;c=Math.floor(c/3);if(v===1)out[a]|=1<<b;if(v===2)out[b]|=1<<a;}attack(out);}
let state=0x5c105e;function rand(){state^=state<<13;state^=state>>>17;state^=state<<5;return(state>>>0)/4294967296;}
for(let trial=0;trial<1200;trial++){const n=6+trial%2,out=Array(n).fill(0),density=.25+.7*(trial%5)/4;for(let a=0;a<n;a++)for(let b=a+1;b<n;b++)if(rand()<density){if(rand()<.5)out[a]|=1<<b;else out[b]|=1<<a;}attack(out);}
attack([32,17,96,64,1,74,2]);
attack([6,8,8,17,65,22,33]);
attack([4,4,24,32,32,3]);
const result={status:'PASS',counts,multistageControl,positiveFeedControl,scope:'All oriented graphs n=2..5 plus 1200 deterministic n=6/7 controls and three explicit controls. Forces synchronous; weak steps strictly single and only at maximal head. All orders enumerated. No minimality assumed. Not a proof of SNC.'};fs.writeFileSync(path.join(__dirname,'audit_independent_weak_closure.results.json'),JSON.stringify(result,null,2)+'\n');console.log(JSON.stringify(result,null,2));
