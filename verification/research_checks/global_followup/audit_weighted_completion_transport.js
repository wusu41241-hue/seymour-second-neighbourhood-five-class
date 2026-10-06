"use strict";
// Floating basis enumeration locates controls; exact rational verification is separate.
const fs=require("fs"),path=require("path");
const useForcedFamily=process.argv[3]==="protection-forced";
function pc(m){let r=0;for(;m;m&=m-1)r++;return r;}
function ids(m,n){const r=[];for(let x=0;x<n;x++)if(m&(1<<x))r.push(x);return r;}
function graph(out){const n=out.length,full=(1<<n)-1,inc=Array(n).fill(0),two=Array(n).fill(0),P=Array(n).fill(0);
 for(let x=0;x<n;x++)for(const q of ids(out[x],n)){if(q===x||out[q]&(1<<x))throw Error("Invalid oriented graph");inc[q]|=1<<x;two[x]|=out[q];}
 for(let x=0;x<n;x++)two[x]&=full&~(out[x]|1<<x);
 const far=out.map((m,x)=>full&~(m|two[x]|1<<x));for(let x=0;x<n;x++)for(const y of ids(far[x],n))P[y]|=1<<x;
 const prot=far.map((m,x)=>ids(m,n).reduce((r,y)=>(out[y]&(1<<x))&&!(inc[y]&~inc[x])?r|1<<y:r,0));
 const F=far.map((m,x)=>m&~prot[x]),M=out.map((m,x)=>full&~(m|inc[x]|1<<x)),edges=[];
 for(let a=0;a<n;a++)for(let b=a+1;b<n;b++)if(M[a]&(1<<b)){const fa=inc[a]&P[b],fb=inc[b]&P[a];edges.push({a,b,fa,fb});}
 const N=out.map((m,x)=>Array.from({length:n},(_,y)=>(two[x]&(1<<y))?1:(m&(1<<y))?-1:0)),forced=Array(n).fill(0);for(let w=0;w<n;w++)for(const a of ids(prot[w],n))forced[a]|=out[w]&M[a];
 return{out,n,full,inc,two,P,prot,F,M,edges,N,forced,g:out.map((m,x)=>pc(m)-pc(two[x]))};}
function refs(d){const choices=new Map();function go(left,rank){if(!left){const out=d.out.slice();for(const e of d.edges){const bad=e.fa&&e.fb,forward=useForcedFamily?!!(d.forced[e.a]&(1<<e.b))||(!(d.forced[e.b]&(1<<e.a))&&rank[e.a]<rank[e.b]):bad?rank[e.a]<rank[e.b]:!e.fa&&(!!e.fb||rank[e.a]<rank[e.b]);out[forward?e.a:e.b]|=1<<(forward?e.b:e.a);}const key=out.join(",");if(!choices.has(key))choices.set(key,{out,rank:rank.slice()});return;}
 const step=d.n-pc(left);for(const x of ids(left,d.n))if(!(d.prot[x]&left)){rank[x]=step;go(left&~(1<<x),rank);}}go(d.full,Array(d.n));return[...choices.values()];}
function solve(A,b){const n=b.length,m=A.map((r,i)=>[...r,b[i]]);for(let k=0;k<n;k++){let p=k;for(let j=k+1;j<n;j++)if(Math.abs(m[j][k])>Math.abs(m[p][k]))p=j;if(Math.abs(m[p][k])<1e-9)return null;[m[p],m[k]]=[m[k],m[p]];const q=m[k][k];for(let j=k;j<=n;j++)m[k][j]/=q;for(let i=0;i<n;i++)if(i!==k){const q=m[i][k];for(let j=k;j<=n;j++)m[i][j]-=q*m[k][j];}}return m.map(r=>r[n]);}
function combinations(n,k,fn){const s=[];function go(next){if(s.length===k){fn(s);return;}for(let i=next;i<=n-(k-s.length);i++){s.push(i);go(i+1);s.pop();}}go(0);}
function dot(a,b){return a.reduce((r,x,i)=>r+x*b[i],0);}
function expansionLP(T,delta){const n=T.n,cons=Array.from({length:2*n},(_,k)=>k<n?Array.from({length:n},(_,j)=>k===j?1:0):T.N.map(r=>r[k-n]));let best=-Infinity,winner=null,basis=null;
 combinations(2*n,n-1,s=>{const lam=solve([Array(n).fill(1),...s.map(i=>cons[i])],[1,...s.map(()=>0)]);if(!lam||cons.some(r=>dot(r,lam)<-1e-8))return;const score=dot(delta,lam);if(score>best+1e-8){best=score;winner=lam;basis=s.slice();}});return{best,lambda:winner,basis,cons};}
function losing(T){const n=T.n,K=T.out.map((_,i)=>Array.from({length:n},(_,j)=>T.inc[i]&(1<<j)?-1:T.out[i]&(1<<j)?1:0));let sol=null;
 for(let mask=1;mask<(1<<n)&&!sol;mask++)if(pc(mask)%2){const S=ids(mask,n),A=S.map(x=>S.map(y=>K[x][y]));A[A.length-1]=S.map(()=>1);const v=solve(A,S.map((_,i)=>i===S.length-1?1:0));if(!v||v.some(x=>x<1e-9))continue;const l=Array(n).fill(0);S.forEach((x,i)=>l[x]=v[i]);if(K.every(r=>dot(r,l)>-1e-8))sol=l;}if(!sol)throw Error("Missing Fisher density");return sol;}
function medianForced(T){const n=T.n,dp=Array(1<<n).fill(-1);dp[0]=0;for(let m=1;m<(1<<n);m++)for(const v of ids(m,n)){const old=m&~(1<<v);dp[m]=Math.max(dp[m],dp[old]+pc(T.inc[v]&old));}
 const common=Array.from({length:n},()=>Array(n).fill(true));let total=0;function walk(m,order){if(!m){total++;const rank=Array(n);order.forEach((v,i)=>rank[v]=n-1-i);for(let a=0;a<n;a++)for(const b of ids(T.out[a],n))if(rank[a]>rank[b])common[a][b]=false;return;}for(const v of ids(m,n)){const old=m&~(1<<v);if(dp[old]+pc(T.inc[v]&old)===dp[m])walk(old,[...order,v]);}}walk((1<<n)-1,[]);return{score:dp.at(-1),total,forced:common};}
let seed=0x5106bada;function random(){seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;return(seed>>>0)/4294967296;}
const count={graphs:0,referenceCompletions:0,expansionLPs:0,skewObstructionCandidates:0};let obstruction=null,forcedSupportControl=null;
const maxSamples=process.argv[2]?Number(process.argv[2]):5000;
for(let s=0;s<maxSamples&&!obstruction;s++){const n=process.argv[4]?Number(process.argv[4]):5+s%2,out=Array(n).fill(0),density=[.4,.55,.7,.85][s%4];for(let a=0;a<n;a++)for(let b=a+1;b<n;b++)if(random()<density){if(random()<.5)out[a]|=1<<b;else out[b]|=1<<a;}
 const d=graph(out),choices=refs(d);let bestSkew=-Infinity;const details=[];
 for(const c of choices){const T=graph(c.out),delta=T.g.map((g,x)=>g-d.g[x]),l=losing(T),score=dot(l,delta);bestSkew=Math.max(bestSkew,score);details.push({...c,T,delta,losingDensity:l,skewScore:score});count.referenceCompletions++;
  if(!forcedSupportControl){const med=medianForced(T);for(let a=0;a<n;a++)for(const b of ids(T.out[a],n))if(l[a]>1e-8&&l[b]>1e-8&&med.forced[a][b]){forcedSupportControl={out:T.out,losingDensity:l,forcedArc:[a,b],medianScore:med.score,medianOrders:med.total};break;}}
 }
 count.graphs++;if(bestSkew< -1e-8){count.skewObstructionCandidates++;let bestExpansion=-Infinity;const full=[];for(const c of details){const lp=expansionLP(c.T,c.delta);count.expansionLPs++;bestExpansion=Math.max(bestExpansion,lp.best);full.push({out:c.out,rank:c.rank,delta:c.delta,skewScore:c.skewScore,losingDensity:c.losingDensity,expansionScore:lp.best,expansionLambda:lp.lambda,expansionBasis:lp.basis});if(bestExpansion>=-1e-8)break;}
  if(bestExpansion< -1e-8)obstruction={original:out,originalGaps:d.g,protectedRelations:d.prot.map(m=>ids(m,n)),allReferenceCompletions:full,bestExpansion};}
 if(s%500===499)console.log(JSON.stringify({progress:s+1,count,forcedSupportControl}));}
const result={status:obstruction?"OBSTRUCTION FOUND":"NO OBSTRUCTION IN SAMPLE",family:useForcedFamily?"protection-forced":"canonical",sampleOrders:process.argv[4]?[Number(process.argv[4])]:[5,6],seed:"0x5106bada",count,obstruction,forcedSupportControl,limits:["A control is not assumed all-deficient or arc-minimal.","Reference completions, not every arbitrary tournament completion, are enumerated.","Floating basis enumeration locates examples; rational verification is separate."]},filename=(useForcedFamily?"audit_weighted_protection_forced_transport":"audit_weighted_completion_transport")+(process.argv[4]?".n"+process.argv[4]:"")+".results.json";fs.writeFileSync(path.join(__dirname,filename),JSON.stringify(result,null,2)+"\n");console.log(JSON.stringify(result,null,2));
