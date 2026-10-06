"use strict";
const fs=require("fs"),path=require("path");
const src=fs.readFileSync(path.join(__dirname,"audit_global_completion_routes.js"),"utf8").split("const counts=")[0];
const {data,completion}=new Function("require",src+"\nreturn {data,completion};")(require);
function* perms(a){if(!a.length){yield [];return;}for(let i=0;i<a.length;i++)for(const p of perms([...a.slice(0,i),...a.slice(i+1)]))yield[a[i],...p];}
function rankOf(p){const r=Array(p.length);p.forEach((v,i)=>r[v]=i);return r;}
function extendsProtection(d,r){for(let x=0;x<d.n;x++)for(let y=0;y<d.n;y++)if((d.prot[x]&(1<<y))&&r[y]>=r[x])return false;return true;}
function score(out,p){let n=0;for(let i=0;i<p.length;i++)for(let j=i+1;j<p.length;j++)if(out[p[i]]&(1<<p[j]))n++;return n;}
let seed=0x51a0cafe;function rng(){seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;return(seed>>>0)/4294967296;}
const totals={graphs:0,admissibleReferences:0,allOrdersChecked:0,globalMedianOrders:0,
 flexibleForwardChecks:0,positiveProtectedPairs:0};
for(let n=1;n<=7;n++){
 const ps=[...perms(Array.from({length:n},(_,i)=>i))],ranks=ps.map(rankOf),pairs=[];for(let a=0;a<n;a++)for(let b=a+1;b<n;b++)pairs.push([a,b]);
 const total=n<=4?3**pairs.length:(n===7?50:100);
 for(let code=0;code<total;code++){
  const out=Array(n).fill(0);let word=code;for(const[a,b]of pairs){let k;if(n<=4){k=word%3;word=Math.floor(word/3);}else k=rng()<.4?0:(rng()<.5?1:2);if(k===1)out[a]|=1<<b;if(k===2)out[b]|=1<<a;}
  const d=data(out),fixed=out.slice(),flex=d.edges.filter(e=>e.fa&&e.fb||!e.fa&&!e.fb);
  for(const e of d.edges)if(!(e.fa&&e.fb)&&!!e.fa!==!!e.fb)fixed[e.fa?e.b:e.a]|=1<<(e.fa?e.a:e.b);
  let best=-1,referenceIndex=-1;
  for(let i=0;i<ps.length;i++)if(extendsProtection(d,ranks[i])){totals.admissibleReferences++;const s=score(fixed,ps[i]);if(s>best){best=s;referenceIndex=i;}}
  if(referenceIndex<0)throw Error("no protection extension");
  const rank=ranks[referenceIndex],c=completion(out,d,rank,e=>rank[e.a]<rank[e.b]),td=data(c.T),target=best+flex.length;
  if(score(c.T,ps[referenceIndex])!==target)throw Error("fixed-plus-flex score mismatch");
  let maximum=-1;for(const p of ps){maximum=Math.max(maximum,score(c.T,p));totals.allOrdersChecked++;}
  if(maximum!==target)throw Error("max reference is not global median");
  for(let i=0;i<ps.length;i++)if(score(c.T,ps[i])===maximum){
   totals.globalMedianOrders++;const r=ranks[i];if(!extendsProtection(d,r))throw Error("median violates protection");
   for(const e of flex){const a=c.T[e.a]&(1<<e.b)?e.a:e.b,b=a===e.a?e.b:e.a;if(r[a]>=r[b])throw Error("flex edge backward in global median");totals.flexibleForwardChecks++;}
   const f=ps[i].at(-1),K=c.T[f]&~out[f];for(const e of flex)if((e.a===f||e.b===f)&&(K&(1<<(e.a===f?e.b:e.a))))throw Error("flex added out at feed");
   if(d.g[f]>0&&d.F[f]&&!(d.F[f]&(d.F[f]-1))&&K)throw Error("unit-budget positive feed has a forbidden good keeper");
  }
  for(const p of d.prot){let q=p;for(;q;q&=q-1)totals.positiveProtectedPairs++;}
  totals.graphs++;
 }
}
const result={status:"PASS",seed:"0x51a0cafe",totals,scope:"Maximal reference-completion lemma checked on every labeled graph of orders one to four and 250 fixed-seed samples of orders five to seven; all orders of each reported tournament are enumerated. No SNC or arc-set-minimal theorem is proved computationally."};
fs.writeFileSync(path.join(__dirname,"audit_maximal_reference_completion.results.json"),JSON.stringify(result,null,2)+"\n");console.log(JSON.stringify(result,null,2));
