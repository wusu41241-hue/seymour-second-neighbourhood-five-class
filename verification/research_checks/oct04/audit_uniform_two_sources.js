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
const counts={graphs5:0,sampledGraphs:0,twoSourceGraphs5:0,twoSourceSampleGraphs:0,
  allNonSourcesProtectedGraphs5:0,allNonSourcesProtectedSampleGraphs:0,
  targetedActiveControlGraphs:0,completions:0,protectedNonSourceEqualities:0,nonSourceAddedBadFirstCases:0,
  nonSourceMultipleAddedBadFirstCases:0,smallBudgetPersistenceCases:0,
  inactiveLargeBudgetPersistenceCases:0,activeSaturatedPersistenceCases:0,
  activeCasesWithMultipleAddedNeighbours:0,tournamentTwoSnpChecks:0,allDeficientInputGraphs:0};
const examples={};
function audit(o,isFive,targeted=false){
  const d=info(o);if(d.g.every(x=>x>0))counts.allDeficientInputGraphs++;
  if(pc(d.Z)!==2)return;
  if(!targeted)counts[isFive?"twoSourceGraphs5":"twoSourceSampleGraphs"]++;
  const [p,q]=ids(d.Z,d.n),otherProtected=ids(d.full&~d.Z,d.n).every(z=>!d.F[z]);
  if(otherProtected&&!targeted)counts[isFive?"allNonSourcesProtectedGraphs5":"allNonSourcesProtectedSampleGraphs"]++;
  for(const[u,v]of [[p,q],[q,p]])for(const reverse of [false,true]){
    const t=pc(d.F[v]),local=target(o,d,v);
    let force=false,active=false;
    if(d.eta[v]===2&&d.g[v]>=1&&d.g[v]<=2&&t>2){
      if(!d.P[v])force=true;
      else if(local&&local.s===0&&local.j===1&&local.H===(1<<u)&&pc(local.X)<pc(local.C)&&
          d.two[v]===((d.M[v]&~(1<<u))|local.X)&&!(d.M[v]&~((1<<u)|local.C))){force=true;active=true;}
    }
    const rank=reference(d,reverse,force?u:-1,force?v:-1),{T,A,B}=complete(o,d,u,v,rank),a=info(T);counts.completions++;
    for(const z of ids(d.full&~d.Z,d.n))if(!d.F[z]){
      const K=T[z]&d.M[z];assert(!(K&~d.two[z]),"new first neighbours were exact second neighbours",{o,u,v,z,K});
      assert(a.two[z]===(d.two[z]&~K),"fixed tournament non-source exact identity",{o,u,v,z,K,actual:a.two[z],expected:d.two[z]&~K});
      assert(a.g[z]===d.g[z]+2*pc(K),"fixed tournament non-source gap identity",{o,u,v,z,K});counts.protectedNonSourceEqualities++;
      const addedBadFirst=(A&(1<<z))?pc(B):0;
      if(addedBadFirst)counts.nonSourceAddedBadFirstCases++;
      if(addedBadFirst>=2)counts.nonSourceMultipleAddedBadFirstCases++;
    }
    if(d.g[v]>=1&&t<=2){
      const K=T[v]&d.M[v];if(!K)assert(a.two[v]===d.two[v],"small budget no new first exact equality",{o,u,v});
      else assert(!(a.two[v]&~((d.two[v]|d.F[v])&~K)),"simultaneous small budget envelope",{o,u,v,K});
      assert(a.g[v]>0,"small budget preserves positive gap",{o,u,v,old:d.g[v],next:a.g[v],t});counts.smallBudgetPersistenceCases++;
    }
    if(force&&!active){
      assert(pc(d.M[v])===1&&d.g[v]===1,"inactive eta2 identity",{o,u,v});
      assert(T[v]===o[v]&&a.two[v]===d.two[v]&&a.g[v]===1,"inactive arbitrary budget persistence",{o,u,v,t});counts.inactiveLargeBudgetPersistenceCases++;
      if(!examples.inactive)examples.inactive={out:o,u,v,t};
    }
    if(active){
      const J=d.M[v]&~(1<<u);
      assert(T[v]===(o[v]|J)&&a.two[v]===(d.two[v]&~J),"active saturated exact equality",{o,u,v,J,actual:a.two[v]});
      assert(a.g[v]===d.g[v]+2*pc(J)&&a.g[v]>0,"active large budget positive gap",{o,u,v,J});counts.activeSaturatedPersistenceCases++;
      if(pc(J)>=2)counts.activeCasesWithMultipleAddedNeighbours++;
      if(!examples.active)examples.active={out:o,u,v,J,t};
    }
    if(T.every(m=>m!==0)){assert(a.g.filter(x=>x<=0).length>=2,"published two Seymour vertex property",{T,g:a.g});counts.tournamentTwoSnpChecks++;}
  }
}
for(let code=0;code<59049;code++){
  let c=code;const o=Array(5).fill(0);for(let a=0;a<5;a++)for(let b=a+1;b<5;b++){const d=c%3;c=Math.floor(c/3);if(d===1)o[a]|=1<<b;if(d===2)o[b]|=1<<a;}
  audit(o,true);counts.graphs5++;
}
let seed=0x2241026;function random(){seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;return(seed>>>0)/4294967296;}
for(let sample=0;sample<100000;sample++){
  const n=6+sample%7,density=[.3,.45,.6,.75,.9][sample%5],o=Array(n).fill(0);
  for(let a=0;a<n;a++)for(let b=a+1;b<n;b++)if(random()<density){if(random()<.5)o[a]|=1<<b;else o[b]|=1<<a;}
  audit(o,false);counts.sampledGraphs++;
}
// Purpose-built active controls, derived by false-twin duplication of a
// previously checked local graph. They are NOT all-deficient graphs.
// The second control genuinely retains two added first neighbours at once.
const targetedActive=[
  [70,192,18,480,130,83,16,289,83],
  [3142,704,274,4832,642,339,272,4129,642,4129,274,274,339]
];
examples.targetedActiveControls=[];
for(const o of targetedActive){
  audit(o,false,true);counts.targetedActiveControlGraphs++;
  const d=info(o),{T}=complete(o,d,3,0,reference(d,false,3,0)),a=info(T),J=d.M[0]&~(1<<3);
  assert(d.eta[0]===2&&d.g[0]===1&&pc(d.F[0])===3,"active control numerical hypotheses",o);
  assert(T[0]===(o[0]|J)&&a.two[0]===(d.two[0]&~J),"active multi-neighbour exact identity",o);
  examples.targetedActiveControls.push({out:o,sourceSet:ids(d.Z,d.n),safeEtaTwoVertex:0,
    originalGap:d.g[0],originalEta:d.eta[0],unprotectedFar:ids(d.F[0],d.n),
    retainedNeighbours:ids(J,d.n),completedGap:a.g[0],notAllDeficient:!d.g.every(x=>x>0)});
}
const nine=[28,224,266,274,262,321,385,289,3],d=info(nine),{T}=complete(nine,d,0,1,reference(d,false,0,1)),a=info(T);
for(let z=2;z<9;z++)assert(a.two[z]===(d.two[z]&~(T[z]&d.M[z])),"nine vertex multiple bad out-arcs control",{z});
assert(a.g[1]===1,"nine vertex inactive endpoint persistence");
examples.nineVertexControl={out:nine,completedOut:T,originalGap:d.g,originalEta:d.eta,completedGap:a.g,sourceSet:ids(d.Z,9),addedBadFirstNeighboursAtEachA:3,notAllDeficient:true};
assert(counts.twoSourceGraphs5===7320,"five-vertex source count independently reproduces 7320");
assert(counts.allNonSourcesProtectedGraphs5===60,"five-vertex simultaneous protection count independently reproduces 60");
assert(counts.activeCasesWithMultipleAddedNeighbours>0,"must exercise active retention of two or more added neighbours");
const result={status:"PASS",counts,examples,seed:"0x2241026",limitations:[
  "No all-deficient input graph occurred; the scan checks actual local set statements and explicit premises.",
  "Two canonical reference orders and both source-role assignments per graph, not all possible orders.",
  "Purpose-built active controls exercise retaining one and two added neighbours; finite tests do not verify every possible set size.",
  "The nine-vertex control exercises three simultaneous added bad first arcs, and has many original Seymour vertices.",
  "Pro sandbox code and result links were not imported."
]};
fs.writeFileSync(path.join(__dirname,"audit_uniform_two_sources.results.json"),JSON.stringify(result,null,2)+"\n");console.log(JSON.stringify(result,null,2));
