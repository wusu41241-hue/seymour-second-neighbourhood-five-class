"use strict";
// Exact simultaneous original-snapshot row surgery. No external dependencies.
const fs=require("fs"),path=require("path");
function demand(v,s,d){if(!v)throw Error(s+" "+JSON.stringify(d));}
function pc(m){let r=0;for(;m;m&=m-1)r++;return r;}
function ids(m,n){const a=[];for(let x=0;x<n;x++)if(m&(1<<x))a.push(x);return a;}
function data(out){const n=out.length,full=(1<<n)-1,inc=Array(n).fill(0),two=Array(n).fill(0);
 for(let a=0;a<n;a++)for(const b of ids(out[a],n)){demand(a!==b&&!(out[b]&(1<<a)),"Oriented graph",{out,a,b});inc[b]|=1<<a;two[a]|=out[b];}
 for(let a=0;a<n;a++)two[a]&=full&~(out[a]|1<<a);
 return{out,n,full,inc,two,g:out.map((m,a)=>pc(m)-pc(two[a]))};}
const counts={allFourVertexGraphs:0,randomGraphs:0,simultaneousMaps:0,multipleTailMaps:0,sharedHeadMaps:0,pathsThroughOtherModifiedTails:0,gapComparisons:0,nonmodifiedSecondSetChecks:0,unitPredecessorDeletionChecks:0,fullDomainMaps:0,headInsideModifiedSetMaps:0};
function fullMap(out,rho,save=false){const D=data(out);for(let v=0;v<D.n;v++)demand(!(D.inc[v]&~D.inc[rho[v]]),"Full-domain original containment",{out,rho,v});const E=data(out.map((_,v)=>out[rho[v]])),changed=new Set(rho.map((b,a)=>b!==a?a:null).filter(a=>a!==null));counts.fullDomainMaps++;if([...changed].some(a=>changed.has(rho[a])))counts.headInsideModifiedSetMaps++;
 for(let v=0;v<D.n;v++)demand(E.out[v]===D.out[rho[v]]&&!(E.two[v]&~D.two[rho[v]])&&E.g[v]>=D.g[rho[v]],"Full-domain head second and gap bound",{out,rho,new:E.out,v});
 if(save)return{out,rho,next:E.out,originalGaps:D.g,newGaps:E.g};}
function check(out,A,rho,save=false){const D=data(out),next=out.slice(),tails=ids(A,D.n),heads=tails.map(a=>rho[a]);
 for(const a of tails){const b=rho[a];demand(!(A&(1<<b))&&!(D.inc[a]&~D.inc[b]),"Original hypothesis",{out,A,rho,a,b});next[a]=out[b];}
 const E=data(next);counts.simultaneousMaps++;if(tails.length>1)counts.multipleTailMaps++;if(new Set(heads).size<heads.length)counts.sharedHeadMaps++;
 for(let v=0;v<D.n;v++){if(A&(1<<v)){const b=rho[v];demand(E.out[v]===D.out[b]&&!(E.two[v]&~D.two[b])&&E.g[v]>=D.g[b],"Changed-tail head gap bound",{out,next,A,rho,v,b,D,E});counts.gapComparisons++;
  for(const c of ids(E.out[v]&A,D.n))counts.pathsThroughOtherModifiedTails+=pc(E.out[c]&~(E.out[v]|1<<v));
 }else{demand(E.out[v]===D.out[v]&&!(E.two[v]&~D.two[v])&&E.g[v]>=D.g[v],"Unchanged-source second-set bound",{out,next,A,rho,v,D,E});counts.nonmodifiedSecondSetChecks++;counts.gapComparisons++;}}
 // Nonvacuous local check of the vertex-deletion part, without assuming D all-deficient.
 for(let f=0;f<D.n;f++){const unit=D.inc[f]&D.g.reduce((m,g,v)=>g===1?m|1<<v:m,0);if(unit!==A||ids(D.inc[f],D.n).some(v=>D.g[v]<=0))continue;
  demand(ids(E.inc[f],D.n).every(v=>E.g[v]>=2),"Unit-predecessor cover raises every surviving predecessor",{out,next,A,rho,f,D,E});
  const remaining=ids(D.full&~(1<<f),D.n),without=remaining.map(v=>remaining.reduce((m,w,j)=>E.out[v]&(1<<w)?m|1<<j:m,0)),F=data(without);
  remaining.forEach((v,j)=>demand(F.g[j]>=E.g[v]-((E.inc[f]&(1<<v))?1:0),"Deletion gap lower bound",{out,next,A,rho,f,v,after:F.g[j],before:E.g[v]}));counts.unitPredecessorDeletionChecks++;
 }
 if(save)return{out,tails,heads,next,originalGaps:D.g,newGaps:E.g,originalSecond:D.two.map(m=>ids(m,D.n)),newSecond:E.two.map(m=>ids(m,D.n))};}
for(let code=0;code<729;code++){let q=code;const out=Array(4).fill(0);for(let a=0;a<4;a++)for(let b=a+1;b<4;b++){const x=q%3;q=Math.floor(q/3);if(x===1)out[a]|=1<<b;if(x===2)out[b]|=1<<a;}const D=data(out);counts.allFourVertexGraphs++;
 for(let A=1;A<D.full;A++){const tails=ids(A,4),domains=tails.map(a=>ids(D.full&~A,4).filter(b=>!(D.inc[a]&~D.inc[b])));if(domains.some(d=>!d.length))continue;
  const rho=Array(4);function walk(i){if(i===tails.length){check(out,A,rho);return;}for(const b of domains[i]){rho[tails[i]]=b;walk(i+1);}}walk(0);}
 const allDomains=Array.from({length:4},(_,v)=>ids(D.full,4).filter(b=>!(D.inc[v]&~D.inc[b]))),allRho=Array(4);function allWalk(v){if(v===4){fullMap(out,allRho);return;}for(const b of allDomains[v]){allRho[v]=b;allWalk(v+1);}}allWalk(0);}
let seed=0x5300c10e;function random(){seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;return(seed>>>0)/4294967296;}
for(let sample=0;sample<5000;sample++){const n=5+sample%8,out=Array(n).fill(0),density=[.2,.4,.6,.8][sample%4];for(let a=0;a<n;a++)for(let b=a+1;b<n;b++)if(random()<density){if(random()<.5)out[a]|=1<<b;else out[b]|=1<<a;}const D=data(out);counts.randomGraphs++;let A=0;for(let a=0;a<n;a++)if(random()<.5)A|=1<<a;if(A===D.full)A&=~1;
 let changed=true;while(changed){changed=false;for(const a of ids(A,n))if(!ids(D.full&~A,n).some(b=>!(D.inc[a]&~D.inc[b]))){A&=~(1<<a);changed=true;}}
 if(!A)continue;const rho=Array(n);for(const a of ids(A,n)){const choices=ids(D.full&~A,n).filter(b=>!(D.inc[a]&~D.inc[b]));rho[a]=choices[Math.floor(random()*choices.length)];}check(out,A,rho);}
const controls=[check([0,0,10,16,0],3,[2,3],true),check([0,0,24,0,0],3,[2,2],true),check([12,0,8,0],1,[2],true)],fullMapControls=[fullMap([8,16,0,0,0],[1,0,2,3,4],true),fullMap([16,4,16,6,0],[1,2,2,3,4],true)];
demand(counts.multipleTailMaps>0&&counts.sharedHeadMaps>0&&counts.pathsThroughOtherModifiedTails>0&&counts.unitPredecessorDeletionChecks>0,"Nonvacuous surgery features",counts);
const result={status:"PASS",seed:"0x5300c10e",counts,controls,fullMapControls,limits:["Every check uses exact integer bit operations.","All four-vertex oriented graphs and their admissible subset and full-domain maps are tested; samples are independent arbitrary graphs, not conjecture counterexamples.","The cover-to-smaller-counter implication is mathematical and requires minimum order; these tests verify its local inequalities without fabricating all-deficient inputs.","Only original incoming predicates and original head outgoing rows are used; recomputed sequential surgery is not tested or assumed."]};
fs.writeFileSync(path.join(__dirname,"audit_simultaneous_row_clone.results.json"),JSON.stringify(result,null,2)+"\n");console.log(JSON.stringify(result,null,2));
