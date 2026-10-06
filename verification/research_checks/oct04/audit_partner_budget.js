"use strict";
// Independent explicit-graph checks for partner_budget.tex. Run with Node.
const fs=require("fs"),path=require("path");
function assert(ok,msg,data){if(!ok)throw Error(msg+JSON.stringify(data));}
function pc(x){let c=0;for(;x;x&=x-1)c++;return c;}
function ids(x,n){const a=[];for(let i=0;i<n;i++)if(x&(1<<i))a.push(i);return a;}
function two(o,x){let r=0;for(const z of ids(o[x],o.length))r|=o[z];return r&~(o[x]|1<<x);}
const counts={allFiveVertexGraphs:0,sampledGraphs:0,targetCases:0,exceptionalPartnerConvenience:0,
  sharedHeadInclusions:0,nonemptySharedHeads:0,strictBoundaryCases:0,nonemptyDeletedBundleSnpCases:0,
  etaThreeOneExceptionCases:0,etaThreeNonemptyOneExceptionCases:0};
const examples={};
function audit(o){
  const n=o.length,full=(1<<n)-1,inc=Array(n).fill(0),P=Array(n).fill(0),far=[];
  for(let a=0;a<n;a++)for(const b of ids(o[a],n))inc[b]|=1<<a;
  for(let a=0;a<n;a++){far[a]=full&~(o[a]|two(o,a)|1<<a);for(const b of ids(far[a],n))P[b]|=1<<a;}
  for(let x=0;x<n;x++){
    if(!P[x])continue;
    let C=0;for(const r of ids(P[x],n))C|=o[r];C&=full&~P[x];if(!C)continue;
    counts.targetCases++;
    let X=0;for(const r of ids(C,n))X|=o[r];X&=full&~(P[x]|C);
    const Q=full&~(P[x]|inc[x]|1<<x),H=Q&~C,M=full&~(o[x]|inc[x]|1<<x),B=H&M;
    const k=pc(B),s=pc(H&o[x]),prime=o.slice();prime[x]&=~H;
    const E=(M&~B)|X,n2=two(prime,x),L=E&~n2;
    const g=pc(o[x])-pc(two(o,x)),eta=pc(M)-1+pc(Q)-pc(two(o,x));
    assert(!((M&~B)&X),"disjoint envelope",{o,x});
    assert(!(n2&~E),"deleted source envelope",{o,x});
    let shared=0;
    for(const r of ids(B,n)){counts.exceptionalPartnerConvenience++;assert(!(inc[r]&P[x]),"exceptional partner direction",{o,x,r});}
    for(const r of ids(M&~B,n))shared|=o[r]&far[x];
    counts.sharedHeadInclusions++;if(shared)counts.nonemptySharedHeads++;
    assert(!(shared&~L),"shared head inclusion",{o,x,shared,L});
    if(pc(X)>=pc(C))continue;counts.strictBoundaryCases++;
    assert(pc(E)<=pc(two(o,x))+eta-s-2*k,"general envelope count",{o,x});
    if(!s){
      assert(pc(L)<=eta-2*k,"zero bundle budget",{o,x});
      if(eta===3&&k===1&&g>0){counts.etaThreeOneExceptionCases++;assert(pc(shared)<=1,"eta3 exceptional shared heads",{o,x});if(!examples.eta3)examples.eta3={out:o,x,B,shared,L,g};}
    }else if(pc(n2)>=pc(prime[x])){
      counts.nonemptyDeletedBundleSnpCases++;
      assert(pc(L)<=eta-g-2*k,"nonempty bundle budget",{o,x});
      if(eta===3&&k===1&&g>0){counts.etaThreeNonemptyOneExceptionCases++;assert(!shared&&g===1,"eta3 nonempty exceptional budget",{o,x});}
    }
  }
}
for(let code=0;code<59049;code++){
  let c=code;const o=Array(5).fill(0);
  for(let a=0;a<5;a++)for(let b=a+1;b<5;b++){const d=c%3;c=Math.floor(c/3);if(d===1)o[a]|=1<<b;if(d===2)o[b]|=1<<a;}
  audit(o);counts.allFiveVertexGraphs++;
}
let seed=0x4042026;function random(){seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;return(seed>>>0)/4294967296;}
for(let sample=0;sample<100000;sample++){
  const n=6+sample%7,density=[.3,.5,.65,.8,.95][sample%5],o=Array(n).fill(0);
  for(let a=0;a<n;a++)for(let b=a+1;b<n;b++)if(random()<density){if(random()<.5)o[a]|=1<<b;else o[b]|=1<<a;}
  audit(o);counts.sampledGraphs++;
}
assert(counts.nonemptySharedHeads>0,"nonvacuous shared heads");
const result={status:"PASS",counts,examples,seed:"0x4042026",scope:"Tests actual local inclusions, and numeric bounds only when strict boundary and deleted-source SNP prerequisites are checked. Does not test existence of all-deficient minimal counterexamples."};
fs.writeFileSync(path.join(__dirname,"audit_partner_budget.results.json"),JSON.stringify(result,null,2)+"\n");
console.log(JSON.stringify(result,null,2));
