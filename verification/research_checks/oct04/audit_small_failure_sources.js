"use strict";

// Independent audit of the 4 October Pro reply. No imported Pro code/results.
// Run with Node: node audit_small_failure_sources.js
// Exact second neighbours exclude the vertex and all first neighbours.
// Tests identities on actual graphs, not hypothetical SNC counterexamples.
const fs = require("fs");
const path = require("path");
function assert(ok, message, data) {
  if (!ok) throw new Error(message + " " + JSON.stringify(data));
}
function pc(x) { let c=0; for (;x;x&=x-1)c++; return c; }
function vertices(mask,n) { const a=[]; for(let v=0;v<n;v++)if(mask&(1<<v))a.push(v); return a; }
function data(out) {
  const n=out.length, full=(1<<n)-1, inc=Array(n).fill(0), two=Array(n).fill(0);
  for(let x=0;x<n;x++)for(const y of vertices(out[x],n)){ inc[y]|=1<<x; two[x]|=out[y]; }
  for(let x=0;x<n;x++)two[x]&=full&~(out[x]|(1<<x));
  const far=out.map((a,x)=>full&~(a|two[x]|(1<<x))), P=Array(n).fill(0);
  for(let x=0;x<n;x++)for(const y of vertices(far[x],n))P[y]|=1<<x;
  const protectedMasks=far.map((a,x)=>vertices(a,n).reduce((m,y)=>
    (out[y]&(1<<x))&&!(inc[y]&~inc[x])?m|(1<<y):m,0));
  const unprotected=far.map((a,x)=>a&~protectedMasks[x]);
  const gap=out.map((a,x)=>pc(a)-pc(two[x]));
  const missingMasks=out.map((a,x)=>full&~(a|inc[x]|(1<<x)));
  const eta=missingMasks.map((a,x)=>2*pc(a)+gap[x]-1-pc(P[x]));
  const missing=[], bad=[]; let sources=0;
  for(let a=0;a<n;a++)for(let b=a+1;b<n;b++)if(missingMasks[a]&(1<<b)){
    const fa=inc[a]&P[b], fb=inc[b]&P[a], e={a,b,fa,fb}; missing.push(e);
    if(fa&&fb){bad.push(e);sources|=fa|fb;}
  }
  return {n,full,inc,two,far,P,protectedMasks,unprotected,gap,missingMasks,eta,missing,bad,sources};
}
function canonicalOrder(out,d,reverse) {
  let left=d.full; const rank=Array(d.n).fill(-1); let pos=0;
  while(left){
    let candidates=vertices(left,d.n).filter(x=>!(d.protectedMasks[x]&left));
    assert(candidates.length,"protection relation must be acyclic",out);
    if(reverse)candidates.reverse(); const x=candidates[0]; rank[x]=pos++; left&=~(1<<x);
  }
  return rank;
}
function second(out,f) { let two=0; for(const a of vertices(out[f],out.length))two|=out[a]; return two&~(out[f]|(1<<f)); }
function flipInward(T,d,f,keep=-1) {
  const Q=T.slice(); for(const x of vertices(d.missingMasks[f],d.n))if(x!==keep){Q[f]&=~(1<<x);Q[x]|=1<<f;} return Q;
}
const counts={exhaustiveGraphs5:0,sampledGraphs:0,localEnvelopeCases:0,nonemptyBundleCases:0,
  etaOneCases:0,etaTwoDichotomyCases:0,etaTwoExceptionalCases:0,
  smallSourceGraphs:0,smallSourceBadGraphs:0,completions:0,
  compatibilityChecks:0,inwardTransfers:0,retainedArcTransfers:0,
  retainedTransfersWithProtectedTargets:0,retainedTransfersWithNewSecondHeads:0,
  retainedFormerSecond:0,retainedFormerFar:0,allDeficientGraphs:0};
const examples={};
function localAudit(out,d) {
  for(let x=0;x<d.n;x++){
    const P=d.P[x]; if(!P)continue;
    let C=0; for(const v of vertices(P,d.n))C|=out[v]; C&=d.full&~P;
    if(!C)continue;
    let X=0; for(const v of vertices(C,d.n))X|=out[v]; X&=d.full&~(P|C);
    const Q=d.full&~((1<<x)|d.inc[x]|P), H=Q&~C;
    const j=pc(H), s=pc(H&out[x]);
    assert(!(C&~Q),"target boundary inclusion",{out,x});
    if(pc(X)>=pc(C))continue; // Explicit prerequisite, never presumed on arbitrary graphs.
    if(j===s){
      const prime=out.slice(); prime[x]&=~H;
      const n2=second(prime,x), E=d.missingMasks[x]|X;
      counts.localEnvelopeCases++;
      assert(!(d.missingMasks[x]&X),"disjoint envelope",{out,x});
      assert(!(n2&~E),"deleted target envelope",{out,x});
      assert(!(d.unprotected[x]&~(E&~n2)),"unprotected heads occupy envelope slack",{out,x});
      assert(pc(E)<=pc(d.two[x])+d.eta[x]-s,"envelope cardinality",{out,x});
      if(!s)assert(pc(d.unprotected[x])<=d.eta[x],"j=s=0 bound",{out,x});
      else if(pc(n2)>=pc(prime[x])){
        counts.nonemptyBundleCases++;
        assert(pc(d.unprotected[x])<=d.eta[x]-d.gap[x],"nonempty bundle bound",{out,x});
      }
    }
    // The numeric residual bounds require counterexample hypotheses; supply
    // them here explicitly, along with the deleted-source SNP when needed.
    const prime=out.slice(); prime[x]&=~H;
    const bound=s?d.eta[x]>=d.gap[x]+2*(j-s):d.eta[x]>=2*j;
    const hypotheses=d.gap[x]>=1&&d.gap[x]<=2&&bound&&(!s||pc(second(prime,x))>=pc(prime[x]));
    if(!hypotheses)continue;
    if(d.eta[x]===1){counts.etaOneCases++;assert(pc(d.unprotected[x])<=1,"unit residual",{out,x});}
    if(d.eta[x]===2)for(const r of vertices(d.missingMasks[x],d.n))if(out[r]&d.far[x]){
      counts.etaTwoDichotomyCases++;
      if(!s&&j===1)counts.etaTwoExceptionalCases++;
      assert(pc(d.unprotected[x])<=2||!(d.inc[r]&P),"eta=2 dichotomy",{out,x,r});
    }
  }
}
function audit(out) {
  const d=data(out); localAudit(out,d);
  if(d.gap.every(g=>g>0))counts.allDeficientGraphs++;
  if(pc(d.sources)>3)return;
  counts.smallSourceGraphs++; if(d.bad.length)counts.smallSourceBadGraphs++;
  // Test every eligible source cover of size <=3, not just the smallest.
  const covers=[]; for(let Z=d.sources;Z<=d.full;Z++)if((Z&d.sources)===d.sources&&pc(Z)<=3)covers.push(Z);
  for(const reverse of [false,true]){
    const rank=canonicalOrder(out,d,reverse), goodT=out.slice();
    for(const e of d.missing)if(!e.fa||!e.fb){
      const forward=!e.fa&&(!!e.fb||rank[e.a]<rank[e.b]);
      goodT[forward?e.a:e.b]|=1<<(forward?e.b:e.a);
    }
    for(const Z of covers){
      let S=0; const K=Array(d.n).fill(0);
      for(const p of vertices(Z,d.n)){
        K[p]=goodT[p]&d.missingMasks[p]&Z;
        if(!K[p])S|=1<<p;
        for(const q of vertices(K[p],d.n))for(const y of vertices(d.protectedMasks[p]&d.missingMasks[q],d.n)){
          counts.compatibilityChecks++;
          assert(goodT[y]&(1<<q),"coordinated orientation protects a far target",{out,Z,p,q,y});
        }
      }
      for(const choice of [false,true]){
        const T=goodT.slice();
        for(const {a,b,fa,fb} of d.bad){
          assert(!(fa&S)||!(fb&S),"one direction must avoid zero-outdegree sources",{out,Z,a,b});
          const forward=!(fa&S)&&((fb&S)||!choice);
          T[forward?a:b]|=1<<(forward?b:a);
        }
        counts.completions++;
        for(let f=0;f<d.n;f++){
          if(!K[f]){
            const Q=flipInward(T,d,f), n2=second(Q,f); counts.inwardTransfers++;
            assert(Q[f]===out[f]&&!(n2&~d.two[f]),"all-inward safe-source transfer",{out,Z,f});
          }else for(const q of vertices(K[f],d.n)){
            const Q=flipInward(T,d,f,q), n2=second(Q,f);
            const envelope=(d.two[f]|d.unprotected[f])&~(1<<q);
            counts.retainedArcTransfers++;
            if(d.protectedMasks[f])counts.retainedTransfersWithProtectedTargets++;
            if(n2&~d.two[f])counts.retainedTransfersWithNewSecondHeads++;
            if(d.two[f]&(1<<q))counts.retainedFormerSecond++;else counts.retainedFormerFar++;
            assert(Q[f]===(out[f]|(1<<q)),"retained first-neighbor equality",{out,Z,f,q});
            assert(!(n2&~envelope),"retained-arc exact set inclusion (13)",{out,Z,f,q,n2,envelope});
            assert(pc(n2)<=pc(d.two[f])+pc(d.unprotected[f])-1,"minus-one count",{out,Z,f,q});
            if(!examples.retainedWithBad&&d.bad.length&&d.protectedMasks[f])examples.retainedWithBad={out,Z,f,q,oldSecond:d.two[f],unprotected:d.unprotected[f],newSecond:n2};
          }
        }
      }
    }
  }
}
for(let code=0;code<59049;code++){
  let x=code; const out=Array(5).fill(0);
  for(let a=0;a<5;a++)for(let b=a+1;b<5;b++){const digit=x%3;x=Math.floor(x/3);if(digit===1)out[a]|=1<<b;if(digit===2)out[b]|=1<<a;}
  audit(out); counts.exhaustiveGraphs5++;
}
let seed=0x4c031026;
function random(){seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;return(seed>>>0)/4294967296;}
for(let sample=0;sample<12000;sample++){
  const n=6+sample%5, out=Array(n).fill(0), density=[0.35,0.55,0.75,0.9][sample%4];
  for(let a=0;a<n;a++)for(let b=a+1;b<n;b++)if(random()<density){if(random()<0.5)out[a]|=1<<b;else out[b]|=1<<a;}
  audit(out); counts.sampledGraphs++;
}
assert(counts.retainedTransfersWithNewSecondHeads>0,"non-vacuous new second heads");
assert(counts.retainedTransfersWithProtectedTargets>0,"non-vacuous protection compatibility");
assert(counts.etaTwoExceptionalCases>0,"non-vacuous exceptional eta=2 branch");
const result={status:"PASS",counts,examples,seed:"0x4c031026",limitations:[
  "Not a proof of SNC or of the minimal-counterexample hypotheses.",
  "No all-deficient counterexamples occurred; local hypotheses were checked explicitly on arbitrary graphs.",
  "Two linear extensions and two bad-edge tie choices per eligible source cover, not all completions.",
  "The median-feed theorem is a published dependency; this script tests set transfer at every vertex and does not enumerate median orders."
]};
fs.writeFileSync(path.join(__dirname,"audit_small_failure_sources.results.json"),JSON.stringify(result,null,2)+"\n");
console.log(JSON.stringify(result,null,2));
