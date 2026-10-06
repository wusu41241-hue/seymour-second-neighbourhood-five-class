"use strict";

// Run: node audit_good_missing.js
// Exhaustive, nonvacuous tests of the local cross-witness lemma and the
// convenient-completion / median-feed transfer on every oriented 5-vertex
// graph.  The numerical eta=0 condition is NOT treated as protection on
// arbitrary graphs: that implication requires the manuscript hypotheses.
// No files are written and no complete proof of SSNC is claimed.

function check(ok,msg){if(!ok)throw new Error(msg);}
function pc(x){let c=0;while(x){x&=x-1;c++;}return c;}
function pairs(n){const a=[];for(let i=0;i<n;i++)for(let j=i+1;j<n;j++)a.push([i,j]);return a;}
function oriented(n,code,p){const out=Array(n).fill(0);for(const[i,j]of p){const d=code%3;code=Math.floor(code/3);if(d===1)out[i]|=1<<j;if(d===2)out[j]|=1<<i;}return out;}
function data(out){
  const n=out.length,all=(1<<n)-1,inc=Array(n).fill(0),two=Array(n).fill(0),far=Array(n).fill(0),P=Array(n).fill(0);
  for(let v=0;v<n;v++)for(let u=0;u<n;u++)if(out[v]&(1<<u)){inc[u]|=1<<v;two[v]|=out[u];}
  for(let v=0;v<n;v++){
    two[v]&=all&~(out[v]|(1<<v));far[v]=all&~(out[v]|two[v]|(1<<v));
    for(let x=0;x<n;x++)if(far[v]&(1<<x))P[x]|=1<<v;
  }
  const protectedSource=far.map((row,v)=>{
    for(let x=0;x<n;x++)if(row&(1<<x))
      if(!(out[x]&(1<<v))||(inc[x]&~(inc[v]&~(1<<x))))return false;
    return true;
  });
  return{inc,two,far,P,protectedSource};
}
function perms(a){if(a.length===0)return[[]];return a.flatMap((v,i)=>perms(a.filter((_,j)=>j!==i)).map(p=>[v,...p]));}
function score(out,order){let result=0;for(let i=0;i<order.length;i++)for(let j=i+1;j<order.length;j++)if(out[order[i]]&(1<<order[j]))result++;return result;}

const n=5,ps=pairs(n),orders=perms([0,1,2,3,4]),medianCache=new Map();
function tournamentId(out){let id=0;ps.forEach(([i,j],k)=>{if(out[i]&(1<<j))id|=1<<k;});return id;}
function median(out){
  const id=tournamentId(out);if(medianCache.has(id))return medianCache.get(id);
  let best=-1,order=null;for(const candidate of orders){const value=score(out,candidate);if(value>best){best=value;order=candidate;}}
  const result={best,order};medianCache.set(id,result);return result;
}

const stats={orientedGraphs:59049,missingEdges:0,badMissingEdges:0,crossWitnessConfigurations:0,
  whollyProtectedGraphs:0,allGoodGraphs:0,medianFeedTransfers:0,allVertexNeighborhoodTransfers:0,
  nonemptyReversalBundles:0,lowUnprotectedSupportGraphs:0};
for(let code=0;code<stats.orientedGraphs;code++){
  const out=oriented(n,code,ps),g=data(out),missing=[],dependencies=[];
  let allGood=true;
  for(const[a,b]of ps){
    if((out[a]&(1<<b))||(out[b]&(1<<a)))continue;
    stats.missingEdges++;
    const left=g.inc[a]&g.P[b],right=g.inc[b]&g.P[a];
    missing.push({a,b,left,right});
    if(!left||!right)continue;
    stats.badMissingEdges++;allGood=false;
    for(let u=0;u<n;u++)if(left&(1<<u))for(let v=0;v<n;v++)if(right&(1<<v)){
      stats.crossWitnessConfigurations++;
      check(new Set([a,b,u,v]).size===4,"cross witnesses must be four distinct vertices");
      check(!(out[u]&(1<<v))&&!(out[v]&(1<<u)),"cross witnesses must form a missing pair");
      check(!g.protectedSource[u]&&!g.protectedSource[v],"a protected source cannot be a bad-edge witness");
      dependencies.push({tail:[u,v].sort((x,y)=>x-y).join(","),head:[a,b].join(",")});
    }
  }
  if(g.protectedSource.every(Boolean)){
    stats.whollyProtectedGraphs++;
    check(allGood,"all protected sources imply all missing edges good");
  }
  if(g.protectedSource.filter(x=>!x).length<=3){
    stats.lowUnprotectedSupportGraphs++;
    const tails=new Set(dependencies.map(x=>x.tail));
    check(dependencies.every(x=>!tails.has(x.head)),"support of at most three cannot support a length-two dependency path");
  }
  if(!allGood)continue;
  stats.allGoodGraphs++;
  const T=out.slice();
  for(const{a,b,left}of missing){if(left===0)T[a]|=1<<b;else T[b]|=1<<a;}
  const L=median(T),feed=L.order[n-1];
  for(let f=0;f<n;f++){
    const prime=T.slice();let reversals=0;
    for(const{a,b}of missing)if(a===f||b===f){
      const z=a===f?b:a;
      if(prime[f]&(1<<z))reversals++;
      prime[f]&=~(1<<z);prime[z]|=1<<f;
    }
    const gp=data(prime);
    stats.allVertexNeighborhoodTransfers++;
    check(prime[f]===out[f],"first neighborhood survives inward missing-edge reversal exactly");
    check(gp.two[f]===g.two[f],"exact second neighborhood transfers both ways");
    if(f===feed){
      stats.medianFeedTransfers++;
      if(reversals>0)stats.nonemptyReversalBundles++;
      check(score(prime,L.order)===L.best+reversals,"the chosen median gains every reversed feed arc");
      check(score(prime,L.order)===median(prime).best,"the order remains globally median");
      check(pc(prime[f])<=pc(gp.two[f]),"median feed theorem on completed tournament");
      check(pc(out[f])<=pc(g.two[f]),"the feed is Seymour in the original all-good graph");
    }
  }
}
check(stats.crossWitnessConfigurations>0,"witness test must not be vacuous");
check(stats.nonemptyReversalBundles>0,"reversal test must not be vacuous");
const cycle=[2,4,8,1],cg=data(cycle),cp=pairs(4);
const cycleGaps=cycle.map((row,v)=>pc(row)-pc(cg.two[v]));
const cycleEta=cycle.map((row,v)=>3-pc(row)-pc(cg.inc[v])-1+
  cg.two.reduce((s,r)=>s+((r&(1<<v))?1:0),0)-pc(cg.two[v]));
const cycleBad=cp.filter(([a,b])=>!(cycle[a]&(1<<b))&&!(cycle[b]&(1<<a))&&
  Boolean(cg.inc[a]&cg.P[b])&&Boolean(cg.inc[b]&cg.P[a])).length;
check(cycleEta.every(x=>x===0)&&cycleGaps.every(x=>x===0)&&cycleBad===2,
      "numerical zero eta alone does not imply good missing edges");
process.stdout.write(JSON.stringify({date:"2026-10-04",status:"PASS",stats,
  cachedTournaments:medianCache.size,
  outsideHypothesesControl:{name:"directed four-cycle",outBitmasks:cycle,
    eta:cycleEta,gaps:cycleGaps,badMissingEdges:cycleBad,
    note:"Not an all-deficient graph; the protected-source hypothesis is essential."},
  limitations:["Finite tests supplement the written proof and cited published theorem.",
    "No small graph was assumed to be an SSNC counterexample.",
    "No acyclic-dependency-graph theorem is asserted by the length-two check."]},null,2)+"\n");
