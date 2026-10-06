'use strict';
/* Reuses the independently authored closure enumerator without editing it.
 * Adds checks for the new strong-feed equality degree budget.
 * Outputs only this audit's result file, never the reused script's file.
 */
const fs=require('fs'),path=require('path'),vm=require('vm');
const baseline=path.join(__dirname,'audit_independent_iterated_forced_closure.js');
let source=fs.readFileSync(baseline,'utf8');
const marker='if(original.g[f]>0){counts.positiveOriginalFeeds++;';
if(!source.includes(marker))throw Error('Baseline marker changed; no silent audit rewrite');
const insertion=`if(original.g[f]>0){
  let good=0;
  for(const z of ids(td.inc[f],n))for(const a of ids(T[f],n))
    if(q.rank[a]<q.rank[z]&&(T[a]&(1<<z)))good|=1<<z;
  ok(pc(good)>=pc(T[f]),'strong-feed good inequality fails',{out,Q,T,q,f,good});
  const mu=qd.edges.filter(e=>e.a===f||e.b===f).length;
  if(pc(good)===pc(T[f])){
    extra.equalityChecks++;
    if(td.g[f]<0)extra.negativeCompletedGapEqualityChecks++;
    ok(mu<=pc(original.F[f])-original.g[f],'new equality missing-degree budget fails',{out,Q,T,q,f,good,mu,t:pc(original.F[f]),g:original.g[f]});
    for(const e of qd.edges)if(e.a===f||e.b===f){const r=e.a===f?e.b:e.a;ok(!(good&(1<<r)),'remaining missing partner good',{out,Q,T,q,f,r});}
  }else{
    extra.stableOrders++;
    if(mu>pc(original.F[f])-original.g[f]){
      extra.largeDegreeStableChecks++;
      if(!extra.largeDegreeStableControl)extra.largeDegreeStableControl={out,Q,T,median:q.p,feed:f,mu,g:original.g[f],t:pc(original.F[f]),good:ids(good,n),completedGap:td.g[f]};
    }
  }
  counts.positiveOriginalFeeds++;`;
source=source.replace(marker,insertion);
source=source.replace('const result={status:', 'const result={newStrongEqualityBudget:extra,status:');
const extra={equalityChecks:0,negativeCompletedGapEqualityChecks:0,stableOrders:0,
  largeDegreeStableChecks:0,largeDegreeStableControl:null};
const output=path.join(__dirname,'audit_closure_good_equality_budget.results.json');
const requireWrapped=name=>name==='fs'?{...fs,writeFileSync:(_old,data)=>fs.writeFileSync(output,data)}:require(name);
vm.runInNewContext(source,{require:requireWrapped,__dirname,console,extra},{filename:baseline,timeout:240000});
