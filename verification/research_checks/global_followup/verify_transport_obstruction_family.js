"use strict";
// Exact integer verification; no numerical solver or third-party package.
const fs=require("fs"),path=require("path");
function demand(ok,reason,data){if(!ok)throw Error(reason+" "+JSON.stringify(data));}
function make(n){return Array.from({length:n},()=>Array(n).fill(0));}
function sets(A){const n=A.length,O=[],S=[],N=[],gap=[];for(let x=0;x<n;x++){const out=[],second=[];for(let y=0;y<n;y++)if(A[x][y])out.push(y);for(let y=0;y<n;y++)if(x!==y&&!A[x][y]&&out.some(z=>A[z][y]))second.push(y);O.push(out);S.push(second);N.push(Array.from({length:n},(_,y)=>A[x][y]?-1:second.includes(y)?1:0));gap.push(out.length-second.length);}return{O,S,N,gap};}
function words(k){const a=[];function go(z,f,w){if(!z&&!f){a.push(w);return;}if(z)go(z-1,f,[...w,4]);if(f)go(z,f-1,[...w,5]);}go(k,k,[]);return a;}
const base=[0,49,51,6,9,8];
function cloneGraph(k){const A=make(6*k);for(let a=0;a<6;a++)for(let b=0;b<6;b++)if(base[a]&(1<<b))for(let i=0;i<k;i++)for(let j=0;j<k;j++)A[a*k+i][b*k+j]=1;return A;}
function complete(k,word){const T=cloneGraph(k);for(let a=0;a<4;a++)for(let i=0;i<k;i++)for(let j=i+1;j<k;j++)T[a*k+i][a*k+j]=1;
 for(let i=0;i<k;i++)for(let j=0;j<k;j++){T[i][3*k+j]=1;T[5*k+i][j]=1;}
 const used={4:0,5:0},union=word.map(a=>a*k+used[a]++);for(let i=0;i<union.length;i++)for(let j=i+1;j<union.length;j++)T[union[i]][union[j]]=1;return T;}
function amplify(A){const n=A.length,B=make(3*n);for(let i=0;i<3;i++){for(let x=0;x<n;x++)for(let y=0;y<n;y++){B[i*n+x][i*n+y]=A[x][y];B[i*n+x][((i+1)%3)*n+y]=1;}}return B;}
function combine(A,k,choices){const n=6*k,B=amplify(A);for(let i=0;i<3;i++){const T=complete(k,choices[i]);for(let x=0;x<n;x++)for(let y=0;y<n;y++)B[i*n+x][i*n+y]=T[x][y];}return B;}
function certificate(A,T,k){const n=A.length,d=sets(A),t=sets(T),copies=n/(6*k),delta=t.gap.map((g,x)=>g-d.gap[x]),q=Array.from({length:n},(_,x)=>[12,13,0,11,0,0][Math.floor((x%(6*k))/k)]),r=Array(n).fill(0);
 for(let c=0;c<copies;c++)for(const a of [0,1,3])r[c*6*k+a*k+k-1]=1;
 const dual=t.N.map((row,x)=>3*delta[x]+row.reduce((z,v,j)=>z+v*q[j],0)),columns=Array.from({length:n},(_,y)=>t.N.reduce((z,row,x)=>z+r[x]*row[y],0)),objective=delta.reduce((z,v,x)=>z+r[x]*v,0),mass=r.reduce((z,v)=>z+v,0);
 demand(dual.every(v=>v<=-k),"Common dual bound",{k,n,dual});demand(columns.every(v=>v===0),"Attaining exact expansion density",{k,n,columns});demand(objective*3===-k*mass,"Exact optimum -k/3",{k,n,objective,mass});demand(d.gap.every((g,x)=>g===k*[0,2,3,-1,0,-1][Math.floor((x%(6*k))/k)]),"Original scaled gaps");
 return{order:n,minimumOutdegree:Math.min(...d.O.map(s=>s.length)),dualMaximum:Math.max(...dual),budgetNumerator:objective,budgetDenominator:mass};}
const counts={quotientCompletionTypes:0,independentThreeCopyChoices:0,iteratedAmplifications:0},examples=[];
for(let k=1;k<=4;k++){const A=cloneGraph(k),W=words(k);for(const word of W){const e=certificate(A,complete(k,word),k);counts.quotientCompletionTypes++;if(word===W[0])examples.push({k,completionTypesUpToCloneRelabeling:W.length,...e});}
 if(k<=2)for(const a of W)for(const b of W)for(const c of W){certificate(amplify(A),combine(A,k,[a,b,c]),k);counts.independentThreeCopyChoices++;}
 let B=A,T=complete(k,W.at(-1));for(let depth=1;depth<=(k===1?3:2);depth++){B=amplify(B);T=amplify(T);const e=certificate(B,T,k);counts.iteratedAmplifications++;examples.push({k,amplificationDepth:depth,...e});}}
// The unique median order control from the exploratory program is checked independently.
const forced=[42,60,57,16,33,8],F=make(6);for(let x=0;x<6;x++)for(let y=0;y<6;y++)F[x][y]=forced[x]>>y&1;
let medianScore=-1,orders=[];function perms(a,p){if(!a.length){let s=0;for(let i=0;i<p.length;i++)for(let j=i+1;j<p.length;j++)s+=F[p[i]][p[j]];if(s>medianScore){medianScore=s;orders=[p];}else if(s===medianScore)orders.push(p);return;}for(const x of a)perms(a.filter(y=>y!==x),[...p,x]);}perms([0,1,2,3,4,5],[]);
const weights=[0,0,0,1,1,1],skew=F.map((row,x)=>row.reduce((s,v,y)=>s+(v-F[y][x])*weights[y],0));demand(skew.every(v=>v>=0),"Losing-density support control");demand(orders.length===1&&orders[0].indexOf(5)<orders[0].indexOf(3),"Forced forward arc inside losing-density support");
const result={status:"PASS",counts,examples,forcedSupportControl:{out:forced,losingDensityNumerator:weights,denominator:3,skewResidual:skew,medianScore,medianOrders:orders,forcedArc:[5,3]},limits:["All arithmetic in this verification is exact integer arithmetic.","Clone relabeling reduces all reference completions to binomial(2k,k) binary words; the all-k proof is separate.","These are already-SNC graphs, not counterexamples to the conjecture.","The control refutes unconditional completion-budget existence, not a theorem assuming an all-deficient arc-minimal counterexample."]};fs.writeFileSync(path.join(__dirname,"verify_transport_obstruction_family.results.json"),JSON.stringify(result,null,2)+"\n");console.log(JSON.stringify(result,null,2));
