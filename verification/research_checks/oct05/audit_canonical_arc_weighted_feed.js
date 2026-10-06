"use strict";
const fs=require("fs"),path=require("path");
// Reuse only the pure raw-adjacency helpers before the audit driver.
const helperSource=fs.readFileSync(path.join(__dirname,"audit_global_completion_routes.js"),"utf8").split("const counts=")[0];
const {data,reference,completion}=new Function("require",helperSource+"\nreturn {data,reference,completion};")(require);
function* permutations(a){if(!a.length){yield [];return;}for(let i=0;i<a.length;i++)for(const p of permutations([...a.slice(0,i),...a.slice(i+1)]))yield[a[i],...p];}
let found=null,tested=0,seed=0x5105acfe;
function rng(){seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;return(seed>>>0)/4294967296;}
for(let n=4;n<=6&&!found;n++){
 const orders=[...permutations(Array.from({length:n},(_,i)=>i))],pairs=[];for(let a=0;a<n;a++)for(let b=a+1;b<n;b++)pairs.push([a,b]);
 const total=n<=5?3**pairs.length:1000;
 for(let code=0;code<total&&!found;code++){
  let q=code;const out=Array(n).fill(0);for(const[a,b]of pairs){let z;if(n<=5){z=q%3;q=Math.floor(q/3);}else z=rng()<.4?0:(rng()<.5?1:2);if(z===1)out[a]|=1<<b;if(z===2)out[b]|=1<<a;}
  const d=data(out);if(!d.g.some(x=>x>0))continue;
  for(const reverse of [false,true]){
   const rank=reference(d,reverse),c=completion(out,d,rank,e=>rank[e.a]<rank[e.b]),T=c.T;
   const high=n*n+1,W=T.map((m,x)=>Array.from({length:n},(_,y)=>m&(1<<y)?high:0));
   for(const e of d.edges)if((e.fa&&e.fb)||(!e.fa&&!e.fb))W[rank[e.a]<rank[e.b]?e.a:e.b][rank[e.a]<rank[e.b]?e.b:e.a]=1;
   tested++;let best=-1,bestOrders=[];
   for(const p of orders){let s=0;for(let i=0;i<n;i++)for(let j=i+1;j<n;j++)s+=W[p[i]][p[j]];if(s>best){best=s;bestOrders=[p];}else if(s===best)bestOrders.push(p);}
   for(const order of bestOrders){const f=order.at(-1);if(d.g[f]<=0)continue;
    const modified=T.slice(),MW=W.map(r=>r.slice());
    for(let r=0;r<n;r++)if((T[f]&(1<<r))&&!(out[f]&(1<<r))){modified[f]&=~(1<<r);modified[r]|=1<<f;MW[r][f]=MW[f][r];MW[f][r]=0;}
    let alpha=0,beta=0;for(let r=0;r<n;r++)if(modified[f]&(1<<r))alpha+=MW[f][r];
    for(let y=0;y<n;y++)if(y!==f){let b=0;for(let r=0;r<n;r++)if((modified[f]&(1<<r))&&(modified[r]&(1<<y)))b=Math.max(b,MW[r][y]-MW[f][y]);beta+=b;}
    if(!(alpha>beta))throw Error("unexpected accounting: low weights chosen below original integer gap");
    let newBest=-1;for(const p of orders){let s=0;for(let i=0;i<n;i++)for(let j=i+1;j<n;j++)s+=MW[p[i]][p[j]];newBest=Math.max(newBest,s);}
    let reported=0;for(let i=0;i<n;i++)for(let j=i+1;j<n;j++)reported+=MW[order[i]][order[j]];
    if(reported!==newBest)throw Error("backward-weight reversal did not preserve median order");
    found={n,originalOut:out,originalGaps:d.g,canonicalCompletion:T,highWeight:high,lowWeight:1,weightedMedianOrder:order,modifiedCompletion:modified,modifiedArcWeights:MW,modifiedGlobalMedianScore:newBest,feed:f,alpha,beta};break;
   }
   if(found)break;
  }
 }
}
const result={status:found?"CANONICAL_FEED_SHORTCUT_REFUTED":"NO_FINITE_WITNESS",tested,seed:"0x5105acfe",control:found,
 limits:["This tests the exact canonical low-weight completion plus backward feed reversals, not SNC or Seacrest's existential theorem.","Original and uniquely convenient arcs have weight n^2+1; bad and double-convenient additions have weight one.","All median scores for the reported small tournament are exactly enumerated. No minimal-counterexample hypotheses are asserted on the control."]};
fs.writeFileSync(path.join(__dirname,"audit_canonical_arc_weighted_feed.results.json"),JSON.stringify(result,null,2)+"\n");console.log(JSON.stringify(result,null,2));
