'use strict';
/* Finite attack of the structural path/cycle invariant. The invariant does
 * not need positive original gap, so all strong-equality feeds are tested;
 * MIN residual-two/three conclusions are NOT computationally certified.
 * Reuses the independently authored weak closure engine without editing it.
 */
const fs=require('fs'),path=require('path'),vm=require('vm');
const baseline=path.resolve(__dirname,'../global_round2/audit_independent_weak_closure.js');
let source=fs.readFileSync(baseline,'utf8');
const marker='counts.originalFirstSecondFeedChecks++;';
if(!source.includes(marker))throw Error('Baseline changed; explicit repair required');
const insertion=`counts.originalFirstSecondFeedChecks++;
  let GP=0;
  for(const r of ids(td.inc[f],n))if(ids(T[f],n).some(a=>q.rank[a]<q.rank[r]&&(T[a]&(1<<r))))GP|=1<<r;
  if(pc(GP)===pc(T[f])){
    extra.equalityFeeds++;
    const R=qd.full&~(Q[f]|qd.inc[f]|1<<f),S=R&original.two[f],F=R&td.far[f];
    ok(R===(S|F)&&!(S&F),'partner partition failed',{out,Q,T,q,f,R,S,F,GP});
    ok(!(R&GP),'remaining partner good at strong equality',{out,Q,T,q,f,R,GP});
    function reachable(graph,seed,within){let seen=seed,next=seed;while(next){let heads=0;for(const v of ids(next,n))heads|=graph[v]&within;next=heads&~seen;seen|=next;}return seen;}
    const oldReach=reachable(out,S,R);
    for(const stage of stages)ok(reachable(stage,S,R)===oldReach,'closure creates partner seed reachability',{out,stage,Q,T,q,f,R,S,F,oldReach});
    extra.stageReachabilityChecks+=stages.length;
    const U=F&~oldReach;
    if(U){let left=U;while(left){const ss=ids(left,n).filter(v=>!(original.inc[v]&left));if(!ss.length)break;for(const v of ss)left&=~(1<<v);}ok(left,'unreachable far subset has no original cycle',{out,Q,T,q,f,R,S,F,U});extra.unreachableOriginalCycles++;}
    if(S)extra.nonemptySeedChecks++;
    if(S&&F){extra.seedAndFarChecks++;if(!extra.seedAndFarControl)extra.seedAndFarControl={out,Q,T,median:q.p,feed:f,gOriginal:original.g[f],gCompleted:td.g[f],seeds:ids(S,n),far:ids(F,n),originalReach:ids(oldReach,n),unreachable:ids(U,n)};}
  }`;
source=source.replace(marker,insertion);
source=source.replace('const result={status:', 'const result={partnerPathInvariant:extra,status:');
const extra={equalityFeeds:0,stageReachabilityChecks:0,nonemptySeedChecks:0,
  seedAndFarChecks:0,unreachableOriginalCycles:0,seedAndFarControl:null};
const resultPath=path.join(__dirname,'audit_weak_equality_original_partner_paths.results.json');
const req=name=>name==='fs'?{...fs,writeFileSync:(_old,data)=>fs.writeFileSync(resultPath,data)}:require(name);
vm.runInNewContext(source,{require:req,__dirname:path.dirname(baseline),console,extra},{filename:baseline,timeout:240000});
