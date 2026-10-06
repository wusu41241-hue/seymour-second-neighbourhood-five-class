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

function referenceBeforeAll(d,v,reverse){
 const pred=d.prot.slice(),rank=Array(d.n);pred[v]|=d.M[v];let left=d.full,pos=0;
 while(left){let a=ids(left,d.n).filter(x=>!(pred[x]&left));if(reverse)a.reverse();assert(a.length,"all partners before v is compatible",d);const x=a[0];rank[x]=pos++;left&=~(1<<x);}return rank;
}
const counts={graphs5:0,sampledGraphs:0,twoSourceGraphs:0,positiveEndpointCompletions:0,
 emptyFarInPersistence:0,noAddedFirstPersistence:0,packetPersistenceCases:0,
 nonemptyDeletedBundleCases:0,singletonFarInCases:0,
 casesWithTwoPlusAddedFirst:0,casesWithOverlapInUnion:0,
 wholeNonSourceProtectionCases:0,targetedControls:0};
const examples={};
function audit(o,targeted=false){
 const d=info(o);if(pc(d.Z)!==2)return;counts.twoSourceGraphs++;
 const pair=ids(d.Z,d.n),allOthersProtected=ids(d.full&~d.Z,d.n).every(x=>!d.F[x]);
 for(const [u,v]of [pair,pair.slice().reverse()])if(d.g[v]>0)for(const reverse of [false,true]){
   const rank=referenceBeforeAll(d,v,reverse),{T}=complete(o,d,u,v,rank),a=info(T),K=T[v]&d.M[v],h=pc(K);
   counts.positiveEndpointCompletions++;
   if(!d.P[v]){
     assert(!K&&a.two[v]===d.two[v]&&a.g[v]===d.g[v],"empty far-in all-inward persistence",{o,u,v});
     counts.emptyFarInPersistence++;continue;
   }
   if(!K){
     assert(a.two[v]===d.two[v]&&a.g[v]===d.g[v],"no added first persistence",{o,u,v});
     counts.noAddedFirstPersistence++;continue;
   }
   const packet=target(o,d,v);if(!packet||pc(packet.X)>=pc(packet.C))continue;
   const {P,C,X,Q,H,s}=packet,B=H&d.M[v],k=pc(B);
   // On arbitrary graphs this is an explicit local prerequisite, rather
   // than an inferred consequence of numeric zero residual.
   if((d.M[v]&~(B|(1<<u)))&P)continue;
   const prime=o.slice();prime[v]&=~H;const n2hat=info(prime).two[v];
   if(s&&pc(n2hat)<pc(prime[v]))continue;
   const E=(d.M[v]&~B)|X,L=E&~n2hat,lambda=d.eta[v]-2*k-(s?d.g[v]:0);
   assert(!(K&~E)&&h>=pc(d.M[v])-k-1,"added first count",{o,u,v,K,B});
   for(const r of ids(K,d.n))assert(d.inc[r]&P,"every added first has far-in predecessor",{o,u,v,r});
   assert(!(n2hat&~E)&&pc(L)<=lambda,"packet slack bound under explicit prerequisites",{o,u,v,L,lambda});
   const union=d.two[v]|L;
   assert(!(K&~union),"whole first set lies in second-slack union",{o,u,v,K,union});
   assert(!(a.two[v]&~(union&~K)),"general fixed-completion packet envelope",{o,u,v,K,L,actual:a.two[v]});
   assert(a.g[v]>=d.g[v]+2*h-lambda,"general packet gap lower bound",{o,u,v});
   assert(a.g[v]>0,"all remaining singleton and multi-point cases preserve deficiency",{o,u,v,p:pc(P),h,s});
   counts.packetPersistenceCases++;if(s)counts.nonemptyDeletedBundleCases++;
   if(pc(P)===1)counts.singletonFarInCases++;if(h>=2)counts.casesWithTwoPlusAddedFirst++;
   if(L&d.two[v])counts.casesWithOverlapInUnion++;
   if(allOthersProtected)counts.wholeNonSourceProtectionCases++;
   if(!examples.packet)examples.packet={out:o,u,v,p:pc(P),s,k,h,eta:d.eta[v],lambda,originalGap:d.g[v],completedGap:a.g[v]};
   if(targeted&&!examples.targeted)examples.targeted={out:o,u,v,p:pc(P),h,originalGap:d.g[v],completedGap:a.g[v]};
 }
}
for(let code=0;code<59049;code++){
 let c=code;const o=Array(5).fill(0);for(let a=0;a<5;a++)for(let b=a+1;b<5;b++){const d=c%3;c=Math.floor(c/3);if(d===1)o[a]|=1<<b;if(d===2)o[b]|=1<<a;}audit(o);counts.graphs5++;
}
let seed=0x3e24026;function random(){seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;return(seed>>>0)/4294967296;}
for(let sample=0;sample<100000;sample++){
 const n=6+sample%7,density=[.3,.45,.6,.75,.9][sample%5],o=Array(n).fill(0);
 for(let x=0;x<n;x++)for(let y=x+1;y<n;y++)if(random()<density){if(random()<.5)o[x]|=1<<y;else o[y]|=1<<x;}audit(o);counts.sampledGraphs++;
}
for(const o of [
 [28,224,266,274,262,321,385,289,3],
 [70,192,18,480,130,83,16,289,83],
 [3142,704,274,4832,642,339,272,4129,642,4129,274,274,339]
]){audit(o,true);counts.targetedControls++;}
assert(counts.packetPersistenceCases>0&&counts.casesWithTwoPlusAddedFirst>0,"nonvacuous general packet and multiple first-neighbour checks");
const result={status:"PASS",counts,examples,seed:"0x3e24026",limits:[
 "The program checks local prerequisites explicitly; it does not infer them from arbitrary numerical eta values.",
 "The general theorem's outside-vertex protection hypothesis is used in its proof to derive a local missing-partner condition; tests can also supply that condition directly.",
 "No finite experiment proves the all-order minimal-counterexample theorem.",
 "The verifier is self-contained and imports no Pro code."
]};
fs.writeFileSync(path.join(__dirname,"audit_two_protected_exceptions.results.json"),JSON.stringify(result,null,2)+"\n");console.log(JSON.stringify(result,null,2));

