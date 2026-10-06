"use strict";
// Audit the unproved shortcut that every arc-weighted median feed has SNP.
// Seacrest's theorem asserts existence of a vertex, not this feed claim.
const fs=require("fs"),path=require("path");
function* permutations(a){if(!a.length){yield [];return;}for(let i=0;i<a.length;i++)for(const p of permutations([...a.slice(0,i),...a.slice(i+1)]))yield [a[i],...p];}
function score(out,W,p){let s=0;for(let i=0;i<p.length;i++)for(let j=i+1;j<p.length;j++)if(out[p[i]]&(1<<p[j]))s+=W[p[i]][p[j]];return s;}
function arcGap(out,W,v){
 const n=out.length;let first=0,second=0;const headContributions=[];
 for(let a=0;a<n;a++)if(out[v]&(1<<a))first+=W[v][a];
 for(let y=0;y<n;y++)if(y!==v){let beta=0;for(let a=0;a<n;a++)if((out[v]&(1<<a))&&(out[a]&(1<<y)))beta=Math.max(beta,W[a][y]-W[v][y]);if(beta){second+=beta;headContributions.push({head:y,beta});}}
 return {first,second,gap:first-second,headContributions};
}
let tested=0,found=null;
for(const n of [3,4]){
 const ps=[...permutations(Array.from({length:n},(_,x)=>x))],pairs=[];
 for(let a=0;a<n;a++)for(let b=a+1;b<n;b++)pairs.push([a,b]);
 outer:for(let orientation=0;orientation<2**pairs.length;orientation++){
  const out=Array(n).fill(0),arcs=pairs.map(([a,b],i)=>orientation&(1<<i)?[b,a]:[a,b]);for(const [a,b]of arcs)out[a]|=1<<b;
  for(let weights=0;weights<3**arcs.length;weights++){
   let q=weights;const W=Array.from({length:n},()=>Array(n).fill(0));for(const [a,b]of arcs){W[a][b]=q%3+1;q=Math.floor(q/3);}tested++;
   let optimum=-Infinity,best=[];for(const p of ps){const s=score(out,W,p);if(s>optimum){optimum=s;best=[p];}else if(s===optimum)best.push(p);}
   for(const order of best){const feed=order.at(-1),f=arcGap(out,W,feed);if(f.gap>0){
    const gaps=out.map((_,v)=>arcGap(out,W,v));
    if(!gaps.some(x=>x.gap<=0))throw Error("unexpected arc-weighted tournament counterexample");
    found={n,out,arcWeights:W,globalMedianScore:optimum,globalMedianOrder:order,feed,feedArcNeighborhoods:f,allVertexArcGaps:gaps.map(x=>x.gap),numberOfGlobalMedianOrders:best.length};break;
   }}if(found)break outer;
  }
 }if(found)break;
}
if(!found)throw Error("No shortcut counterexample within checked range; do not assume theorem");
const result={status:"SHORTCUT_REFUTED",tested,control:found,limits:[
 "This is a counterexample to a claimed arc-weighted median-FEED statement, not to Seacrest's existential arc-weighted tournament theorem.",
 "Arc second-neighborhood weights use max(w(a,y)-w(v,y),0) over actual two-step paths, including first targets as prescribed by the paper.",
 "All median orders were enumerated exactly for the reported tournament; integer weights avoid tolerances."]};
fs.writeFileSync(path.join(__dirname,"audit_arc_weighted_feed_shortcut.results.json"),JSON.stringify(result,null,2)+"\n");console.log(JSON.stringify(result,null,2));
