"use strict";
// Exact subset-DP controls, including a sharp weak-closure zero-gap model.
const fs=require('fs'),path=require('path');
function check(v,m,o){if(!v)throw Error(m+' '+JSON.stringify(o));}
function pc(m){let v=0;while(m){m&=m-1;v++;}return v;}
function ids(m,n){const a=[];for(let x=0;x<n;x++)if(m&(1<<x))a.push(x);return a;}
function graph(out){const n=out.length,full=(1<<n)-1,inc=Array(n).fill(0),two=Array(n).fill(0);
 for(let x=0;x<n;x++)for(const y of ids(out[x],n)){check(x!==y&&!(out[y]&(1<<x)),'oriented',{out,x,y});inc[y]|=1<<x;two[x]|=out[y];}
 for(let x=0;x<n;x++)two[x]&=full&~(out[x]|1<<x);
 const far=out.map((m,x)=>full&~(m|two[x]|1<<x)),P=[];for(let y=0;y<n;y++)for(let x=0;x<n;x++)if((out[y]&(1<<x))&&!(inc[y]&~inc[x]))P.push([y,x]);
 const F=far.map((m,x)=>m&~P.filter(([y,z])=>z===x).reduce((r,[y])=>r|1<<y,0));
 const missing=out.map((m,x)=>full&~(m|inc[x]|1<<x)),forced=[];
 for(let a=0;a<n;a++)for(let b=a+1;b<n;b++)if(missing[a]&(1<<b)){
  const ab=P.find(([r,w])=>r===a&&(out[w]&(1<<b))),ba=P.find(([r,w])=>r===b&&(out[w]&(1<<a)));check(!(ab&&ba),'opposite forced',{out,a,b});if(ab)forced.push([a,b,ab[1]]);if(ba)forced.push([b,a,ba[1]]);
 }
 return {n,full,inc,two,far,P,F,missing,forced,g:out.map((m,x)=>pc(m)-pc(two[x]))};
}
function closure(out){let Q=out.slice(),d=graph(Q),stages=[Q.slice()],steps=[];
 while(true){let arcs=d.forced.map(([a,b,w])=>[a,b,w]),kind='forced';if(!arcs.length){let weak=null;for(let a=0;a<d.n&&!weak;a++)for(let b=a+1;b<d.n&&!weak;b++)if(d.missing[a]&(1<<b)){if(!(d.inc[a]&~d.inc[b])&&!d.P.some(([y])=>y===b))weak=[a,b,b];else if(!(d.inc[b]&~d.inc[a])&&!d.P.some(([y])=>y===a))weak=[b,a,a];}if(!weak)break;arcs=[weak];kind='weak';}
  const next=Q.slice();for(const[a,b]of arcs){for(const p of ids(d.inc[a],d.n))check((Q[p]&(1<<b))||(d.two[p]&(1<<b)),'step nonconvenient',{out,Q,a,b,p});next[a]|=1<<b;}
  const nd=graph(next);for(const[y,x]of d.P)check(nd.P.some(([a,b])=>a===y&&b===x),'step loses protection',{out,Q,next,y,x});for(const[a,b,w]of arcs)check(nd.P.some(([y,x])=>y===a&&x===w),'added tail lacks successor',{out,Q,next,a,b,w,kind});steps.push({kind,arcs});Q=next;d=nd;stages.push(Q.slice());
 }
 return {Q,d,stages,steps};
}
function medDP(out){const d=graph(out),dp=new Int32Array(1<<d.n),last=new Int16Array(1<<d.n),ways=new Float64Array(1<<d.n);dp.fill(-1000000);dp[0]=0;ways[0]=1;last.fill(-1);
 for(let m=1;m<=d.full;m++)for(const v of ids(m,d.n)){const before=m&~(1<<v),value=dp[before]+pc(d.inc[v]&before);if(value>dp[m]){dp[m]=value;last[m]=v;ways[m]=ways[before];}else if(value===dp[m])ways[m]+=ways[before];}
 function order(mask){const r=[];while(mask){const v=last[mask];r.push(v);mask&=~(1<<v);}return r.reverse();}
 const feeds=[];for(let f=0;f<d.n;f++)if(dp[d.full&~(1<<f)]+pc(d.inc[f])===dp[d.full])feeds.push(f);
 return {maximum:dp[d.full],feeds,order:order(d.full),optimalOrderCount:ways[d.full]};
}
function score(out,p){let left=(1<<out.length)-1,v=0;for(const x of p){left&=~(1<<x);v+=pc(out[x]&left);}return v;}
function analyze(out,reference){const original=graph(out),cl=closure(out),qd=cl.d,Q=cl.Q,partial=medDP(Q);const rank=Array(qd.n);reference.forEach((v,i)=>rank[v]=i);
 check(qd.P.every(([y,x])=>rank[y]<rank[x]),'reference not protected',{out,Q,reference});check(score(Q,reference)===partial.maximum,'specified control reference not median',{out,Q,reference,partial,referenceScore:score(Q,reference)});
 const T=Q.slice();let free=0;for(let a=0;a<qd.n;a++)for(let b=a+1;b<qd.n;b++)if(qd.missing[a]&(1<<b)){const forward=rank[a]<rank[b];T[forward?a:b]|=1<<(forward?b:a);free++;}
 const td=graph(T),complete=medDP(T),f=reference.at(-1);check(complete.maximum===partial.maximum+free&&score(T,reference)===complete.maximum,'specified final control not maximal',{out,Q,T,reference,partial,complete,free});
 check(T[f]===out[f]&&qd.two[f]===original.two[f],'feed transfer neighborhoods change',{out,Q,T,f});const A=td.two[f]&original.far[f],mu=pc(qd.missing[f]);let G=0;for(const y of ids(td.inc[f],qd.n))if(ids(T[f],qd.n).some(a=>rank[a]<rank[y]&&(T[a]&(1<<y))))G|=1<<y;
 check(original.g[f]>0&&pc(original.F[f])>=original.g[f]+1,'not positive strict-surplus model',{out,Q,T,f});
 if(td.g[f]===0){check(mu>=3&&!(qd.missing[f]&~td.far[f]),'zero model missing cycle bound',{out,Q,T,f});for(const r of ids(qd.missing[f],qd.n))check(qd.inc[r]&qd.missing[f],'missing core lacks predecessor',{out,Q,T,f,r});let acyclicLeft=qd.missing[f];while(acyclicLeft){const sources=ids(acyclicLeft,qd.n).filter(r=>!(original.inc[r]&acyclicLeft));if(!sources.length)break;for(const r of sources)acyclicLeft&=~(1<<r);}check(acyclicLeft,'zero model missing core has no ORIGINAL cycle',{out,Q,T,f});check(pc(original.F[f])>=original.g[f]+mu,'zero model head budget',{out,Q,T,f});}
 return {out,Q,T,closureSteps:cl.steps,reference,partialScore:partial.maximum,partialFeeds:partial.feeds,partialMedianOrderCount:partial.optimalOrderCount,finalScore:complete.maximum,finalFeeds:complete.feeds,finalMedianOrderCount:complete.optimalOrderCount,feed:f,originalGaps:original.g,gOriginal:original.g[f],gCompleted:td.g[f],tOriginal:pc(original.F[f]),originalFarHeads:ids(original.F[f],qd.n),newFarSecondHeads:ids(A,qd.n),remainingMissing:ids(qd.missing[f],qd.n),remainingMissingArcs:ids(qd.missing[f],qd.n).flatMap(r=>ids(Q[r]&qd.missing[f],qd.n).map(s=>[r,s])),finalFar:ids(td.far[f],qd.n),goodVertices:ids(G,qd.n),goodSlack:pc(G)-pc(T[f])};
}
const controls=[];
controls.push(analyze([4,4,24,32,32,3],[0,1,2,3,4,5]));
controls.push(analyze([6,8,8,17,1793,80,144,48,33,65,129],[8,9,10,5,6,7,1,2,3,4,0]));
controls.push(analyze([30,100,168,80,130,768,1,1,1,1],[1,2,3,4,5,6,7,8,9,0]));
const result={status:'PASS',controls,scope:'Exact ordinary maximum forward scores by subset dynamic programming. Controls have ordinary Seymour vertices and are not conjecture counterexamples. Two sharp negative stable models, including a feed-local eta=2 model, and one sharp zero cycle model are independently checked.'};fs.writeFileSync(path.join(__dirname,'audit_closure_exact_control_models.results.json'),JSON.stringify(result,null,2)+'\n');console.log(JSON.stringify(result,null,2));
