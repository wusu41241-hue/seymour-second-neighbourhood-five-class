"use strict";
// Independent verifier for the new fixed-tournament completion argument.
// No code/results from the Pro reply are imported. Run with Node.
// No arbitrary graph is assumed to satisfy minimal-counterexample lemmas.
const fs=require("fs"),path=require("path");
function assert(ok,msg,d){if(!ok)throw Error(msg+" "+JSON.stringify(d));}
function pc(m){let c=0;for(;m;m&=m-1)c++;return c;}
function ids(m,n){const a=[];for(let x=0;x<n;x++)if(m&(1<<x))a.push(x);return a;}
function info(o){
  const n=o.length,full=(1<<n)-1,inc=Array(n).fill(0),two=Array(n).fill(0),P=Array(n).fill(0);
  for(let x=0;x<n;x++)for(const a of ids(o[x],n)){inc[a]|=1<<x;two[x]|=o[a];}
  for(let x=0;x<n;x++)two[x]&=full&~(o[x]|1<<x);
  const far=o.map((m,x)=>full&~(m|two[x]|1<<x));for(let x=0;x<n;x++)for(const y of ids(far[x],n))P[y]|=1<<x;
  const prot=far.map((m,x)=>ids(m,n).reduce((r,y)=>(o[y]&(1<<x))&&!(inc[y]&~inc[x])?r|1<<y:r,0));
  const F=far.map((m,x)=>m&~prot[x]),M=o.map((m,x)=>full&~(m|inc[x]|1<<x));
  const g=o.map((m,x)=>pc(m)-pc(two[x])),eta=M.map((m,x)=>2*pc(m)+g[x]-1-pc(P[x]));
  const missing=[],bad=[];let Z=0;
  for(let a=0;a<n;a++)for(let b=a+1;b<n;b++)if(M[a]&(1<<b)){
    const fa=inc[a]&P[b],fb=inc[b]&P[a];missing.push({a,b,fa,fb});if(fa&&fb){bad.push({a,b,fa,fb});Z|=fa|fb;}
  }
  return {n,full,inc,two,P,far,prot,F,M,g,eta,missing,bad,Z};
}
function reference(d,reverse,before=-1,after=-1){
  const pred=d.prot.slice(),rank=Array(d.n);let left=d.full,pos=0;
  if(before>=0){assert(!(d.prot[before]&(1<<after)),"missing partners are incomparable",{before,after});pred[after]|=1<<before;}
  while(left){let a=ids(left,d.n).filter(v=>!(pred[v]&left));if(reverse)a.reverse();assert(a.length,"reference order acyclic",d);const v=a[0];rank[v]=pos++;left&=~(1<<v);}
  return rank;
}
function complete(o,d,u,v,rank){
  const A=o[u]&d.far[v],B=o[v]&d.far[u],T=o.slice();
  assert(A&&B&&!(A&B),"nonempty disjoint bad bipartition",{o,u,v,A,B});
  assert(d.bad.length===pc(A)*pc(B),"all bad pairs are exactly A times B",{o,u,v,A,B,bad:d.bad});
  for(const e of d.missing){let a,b;
    if(e.fa&&e.fb){
      if(A&(1<<e.a)){a=e.a;b=e.b;}else{a=e.b;b=e.a;}
      assert((A&(1<<a))&&(B&(1<<b)),"bad edge orientation A->B",{o,u,v,e,A,B});
      assert((a===e.a?e.fa:e.fb)===(1<<u),"selected bad direction fails only at u",{o,u,v,e});
    }else{
      const forward=!e.fa&&(!!e.fb||rank[e.a]<rank[e.b]);a=forward?e.a:e.b;b=forward?e.b:e.a;
    }T[a]|=1<<b;
  }
  return {T,A,B};
}
function target(o,d,v){
  const P=d.P[v];if(!P)return null;
  let C=0;for(const p of ids(P,d.n))C|=o[p];C&=d.full&~P;if(!C)return null;
  let X=0;for(const c of ids(C,d.n))X|=o[c];X&=d.full&~(P|C);
  const Q=d.full&~(P|d.inc[v]|1<<v),H=Q&~C,j=pc(H),s=pc(H&o[v]);
  return {P,C,X,Q,H,j,s};
}

const counts={graphs5:0,sampledGraphs:0,unitHeadMissingPartnerChecks:0,
 protectedAncestorExclusions:0,unitHeadPropagationChecks:0,
 fiveDerangements:0,invariantActiveGraphs:0,disjointInvariantGraphs:0,
 graphsCompatibleWithRequiredArcs:0};
function audit(o){
 const d=info(o);
 for(let c=0;c<d.n;c++)if(pc(d.F[c])===1){
  const a=ids(d.F[c],d.n)[0];
  for(const u of ids(d.M[c]&~(1<<a),d.n)){
   assert(d.two[c]&(1<<u),"a second missing far head would violate unit budget",{o,c,a,u});
   counts.unitHeadMissingPartnerChecks++;
   assert(!(d.prot[a]&(1<<u)),"unit failure head cannot have this protected ancestor",{o,c,a,u});
   counts.protectedAncestorExclusions++;
   if(pc(d.F[a])===1&&(d.far[a]&(1<<u))){
    assert(d.F[a]===(1<<u),"unit failure head propagation",{o,c,a,u});counts.unitHeadPropagationChecks++;
   }
  }
 }
}
for(let code=0;code<59049;code++){let q=code;const o=Array(5).fill(0);for(let a=0;a<5;a++)for(let b=a+1;b<5;b++){const k=q%3;q=Math.floor(q/3);if(k===1)o[a]|=1<<b;if(k===2)o[b]|=1<<a;}audit(o);counts.graphs5++;}
let seed=0x55102026;function random(){seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;return(seed>>>0)/4294967296;}
for(let s=0;s<100000;s++){const n=6+s%7,o=Array(n).fill(0),density=[.3,.45,.6,.75,.9][s%5];for(let a=0;a<n;a++)for(let b=a+1;b<n;b++)if(random()<density){if(random()<.5)o[a]|=1<<b;else o[b]|=1<<a;}audit(o);counts.sampledGraphs++;}
function perms(a){return a.length?a.flatMap((x,i)=>perms(a.filter((_,j)=>j!==i)).map(t=>[x,...t])):[[]];}
const pairs=[];for(let a=0;a<5;a++)for(let b=a+1;b<5;b++)pairs.push([a,b]);
const edgeIndex=(a,b)=>pairs.findIndex(p=>p[0]===Math.min(a,b)&&p[1]===Math.max(a,b));
for(const h of perms([0,1,2,3,4]).filter(p=>p.every((x,i)=>x!==i))){
 counts.fiveDerangements++;
 for(let mask=1;mask<1024;mask++){
  let incident=0,image=0,disjoint=true,compatible=true;
  pairs.forEach(([a,b],i)=>{if(mask&(1<<i)){incident|=1<<a|1<<b;image|=1<<edgeIndex(h[a],h[b]);
    if(h[a]===a||h[a]===b||h[b]===a||h[b]===b)disjoint=false;
    if((mask&(1<<edgeIndex(a,h[b])))||(mask&(1<<edgeIndex(b,h[a]))))compatible=false;
  }});
  if(incident!==31||image!==mask)continue;counts.invariantActiveGraphs++;
  if(!disjoint)continue;counts.disjointInvariantGraphs++;
  if(compatible)counts.graphsCompatibleWithRequiredArcs++;
 }
}
assert(counts.fiveDerangements===44,"five-point derangement count");
assert(counts.graphsCompatibleWithRequiredArcs===0,"five-unit functional skeleton cannot exist");
assert(counts.unitHeadPropagationChecks>0,"nonvacuous unit-head propagation");
const result={status:"PASS",counts,seed:"0x55102026",limits:[
 "Graph checks test the pure unit-head and protection implication, not numerical eta claims on arbitrary graphs.",
 "The derangement scan validates a finite skeleton used in the proof; the local minimal-counterexample reduction into that skeleton must be proved separately.",
 "No full SNC proof or counterexample is claimed by this verifier."
]};
fs.writeFileSync(path.join(__dirname,"audit_unit_head_constraints.results.json"),JSON.stringify(result,null,2)+"\n");console.log(JSON.stringify(result,null,2));

