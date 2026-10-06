"use strict";

// Checks the new partial-protection completion argument on actual graphs.
// It never assumes that numeric eta<g implies protection on arbitrary graphs.
// Run: node audit_protection_completion.js
function check(ok,m){if(!ok)throw new Error(m);}
function pc(x){let n=0;while(x){x&=x-1;n++;}return n;}
function pairs(n){const p=[];for(let i=0;i<n;i++)for(let j=i+1;j<n;j++)p.push([i,j]);return p;}
function orientation(n,c,p){const o=Array(n).fill(0);for(const[i,j]of p){const d=c%3;c=Math.floor(c/3);if(d===1)o[i]|=1<<j;if(d===2)o[j]|=1<<i;}return o;}
function info(o){
  const n=o.length,all=(1<<n)-1,inc=Array(n).fill(0),two=Array(n).fill(0),U=Array(n).fill(0),P=Array(n).fill(0);
  for(let i=0;i<n;i++)for(let j=0;j<n;j++)if(o[i]&(1<<j)){inc[j]|=1<<i;two[i]|=o[j];}
  for(let i=0;i<n;i++){two[i]&=all&~(o[i]|1<<i);U[i]=all&~(o[i]|two[i]|1<<i);for(let j=0;j<n;j++)if(U[i]&(1<<j))P[j]|=1<<i;}
  const unprotected=U.map((row,i)=>{let mask=0;for(let j=0;j<n;j++)if(row&(1<<j))if(!(o[j]&(1<<i))||(inc[j]&~inc[i]))mask|=1<<j;return mask;});
  const gap=o.map((r,i)=>pc(r)-pc(two[i])),mu=o.map((r,i)=>n-1-pc(r)-pc(inc[i]));
  const eta=mu.map((a,i)=>2*a+gap[i]-1-pc(P[i]));
  return{inc,two,U,P,unprotected,gap,mu,eta};
}
function permutations(a){return a.length?a.flatMap((v,i)=>permutations(a.filter((_,j)=>i!==j)).map(t=>[v,...t])):[[]];}
const n=5,all=31,p=pairs(n),orders=permutations([0,1,2,3,4]),cache=new Map();
function median(T){let id=0;p.forEach(([i,j],k)=>{if(T[i]&(1<<j))id|=1<<k;});if(cache.has(id))return cache.get(id);let best=-1,L;for(const q of orders){let score=0;for(let i=0;i<n;i++)for(let j=i+1;j<n;j++)if(T[q[i]]&(1<<q[j]))score++;if(score>best){best=score;L=q;}}cache.set(id,L);return L;}
function inward(T,missing,f){const r=T.slice();for(const[a,b]of missing)if(a===f||b===f){const z=a===f?b:a;r[f]&=~(1<<z);r[z]|=1<<f;}return r;}
const counts={graphs:59049,partialProtectionTransfers:0,transfersWithNewSecondHeads:0,
  safeLocalCases:0,safeEtaOneGapTwoCases:0,adaptivelyOrientableGraphs:0,
  adaptivelyOrientableBadEdgeGraphs:0,constructiveSeymourTransfers:0};
for(let code=0;code<counts.graphs;code++){
  const out=orientation(n,code,p),a=info(out),missing=[],T=out.slice(),adaptive=out.slice();
  let B=0,hasBad=false,canAdapt=true;
  for(let v=0;v<n;v++)if(pc(a.unprotected[v])>=a.gap[v])B|=1<<v;
  for(const[x,y]of p){
    if((out[x]&(1<<y))||(out[y]&(1<<x)))continue;missing.push([x,y]);
    const L=a.inc[x]&a.P[y],R=a.inc[y]&a.P[x];
    if(!L){T[x]|=1<<y;adaptive[x]|=1<<y;}
    else if(!R){T[y]|=1<<x;adaptive[y]|=1<<x;}
    else{hasBad=true;T[x]|=1<<y;if(!(L&B))adaptive[x]|=1<<y;else if(!(R&B))adaptive[y]|=1<<x;else canAdapt=false;}
  }
  for(let v=0;v<n;v++){
    const prime=inward(T,missing,v),b=info(prime),extra=b.two[v]&~a.two[v];
    counts.partialProtectionTransfers++;
    if(extra)counts.transfersWithNewSecondHeads++;
    check(prime[v]===out[v],"inward completion preserves original first neighborhood");
    check((extra&~a.unprotected[v])===0,"new second heads are unprotected far targets");
    if(a.gap[v]>=1&&a.gap[v]<=2&&a.eta[v]>=0&&a.eta[v]<a.gap[v]){
      let local=a.P[v]===0;
      if(a.P[v]){
        let C=0;for(let u=0;u<n;u++)if(a.P[v]&(1<<u))C|=out[u];C&=all&~a.P[v];
        const R=all&~((1<<v)|a.inc[v]|a.P[v]);let X=0;
        for(let u=0;u<n;u++)if(C&(1<<u))X|=out[u];X&=all&~(a.P[v]|C);
        local=C===R&&C!==0&&pc(X)<pc(C);
      }
      if(local){counts.safeLocalCases++;if(a.eta[v]===1&&a.gap[v]===2)counts.safeEtaOneGapTwoCases++;
        check(pc(a.unprotected[v])<=a.eta[v],"safe local residual bound with explicit boundary premises");}
    }
  }
  if(canAdapt){
    counts.adaptivelyOrientableGraphs++;if(hasBad)counts.adaptivelyOrientableBadEdgeGraphs++;
    const f=median(adaptive)[n-1],prime=inward(adaptive,missing,f),b=info(prime);
    check(pc(prime[f])<=pc(b.two[f]),"median-feed property");
    check(pc(out[f])<=pc(a.two[f]),"adaptive completion produces an original Seymour vertex");
    counts.constructiveSeymourTransfers++;
  }
}
check(counts.transfersWithNewSecondHeads>0,"partial protection check must exercise added second heads");
// A non-all-good six-vertex control: a directed four-cycle dominates
// a two-vertex transitive tail. It has a sink and is not a counterexample.
const controlOut=[50,52,56,49,32,0],control=info(controlOut),controlMissing=[];
const controlT=controlOut.slice();let controlB=0,controlBad=0;
for(let v=0;v<6;v++)if(pc(control.unprotected[v])>=control.gap[v])controlB|=1<<v;
for(const[x,y]of pairs(6)){
  if((controlOut[x]&(1<<y))||(controlOut[y]&(1<<x)))continue;
  controlMissing.push([x,y]);const L=control.inc[x]&control.P[y],R=control.inc[y]&control.P[x];
  if(!L)controlT[x]|=1<<y;
  else if(!R)controlT[y]|=1<<x;
  else{controlBad++;if(!(L&controlB))controlT[x]|=1<<y;
    else if(!(R&controlB))controlT[y]|=1<<x;else throw new Error("control orientation unavailable");}
}
let controlBest=-1,controlOrder;
for(const q of permutations([0,1,2,3,4,5])){let score=0;
  for(let i=0;i<6;i++)for(let j=i+1;j<6;j++)if(controlT[q[i]]&(1<<q[j]))score++;
  if(score>controlBest){controlBest=score;controlOrder=q;}}
const controlFeed=controlOrder[5],controlPrime=inward(controlT,controlMissing,controlFeed);
check(controlBad===2&&controlB===32,"control exercises bad edges with safe failure sources");
check(pc(controlPrime[controlFeed])<=pc(info(controlPrime).two[controlFeed])&&
  control.gap[controlFeed]<=0,"adaptive completion transfers on the non-all-good control");
process.stdout.write(JSON.stringify({date:"2026-10-04",status:"PASS",counts,
  nonAllGoodControl:{outBitmasks:controlOut,badMissingEdges:controlBad,
    gaps:control.gap,unprotectedFarCounts:control.unprotected.map(pc),feed:controlFeed,
    note:"This control has a sink. Its numeric eta=0 at cycle vertices does not grant protected-source structure."},
  scope:"Checks partial-protection accounting and adaptive completion, not the existence of a counterexample or the complete conjecture."},null,2)+"\n");
