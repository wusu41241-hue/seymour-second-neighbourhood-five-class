"use strict";
// Independent attack: do not import the main project's graph helpers.
const fs=require('fs'), path=require('path');
function fail(s,o){throw new Error(s+' '+JSON.stringify(o));}
function pop(m){let n=0;while(m){m&=m-1;n++;}return n;}
function perms(n){const r=[];function go(p,left){if(!left.length){const rank=Array(n);p.forEach((v,i)=>rank[v]=i);r.push({p:p.slice(),rank});return;}for(let i=0;i<left.length;i++)go(p.concat(left[i]),left.slice(0,i).concat(left.slice(i+1)));}go([],Array.from({length:n},(_,i)=>i));return r;}
const allPerms=new Map();for(let n=2;n<=7;n++)allPerms.set(n,perms(n));
function forward(out,p){let s=0,left=(1<<out.length)-1;for(const x of p){left&=~(1<<x);s+=pop(out[x]&left);}return s;}
let counts={graphs:0,medianOrders:0,flexibleEdges:0,nonunitWitnessGraphs:0};
let nonunitFeedControl=null;
let restrictedFamilyControl=null;
function attack(out){
 const n=out.length, full=(1<<n)-1, inc=Array(n).fill(0), second=Array(n).fill(0);
 for(let x=0;x<n;x++)for(let y=0;y<n;y++)if(out[x]&(1<<y)){inc[y]|=1<<x;second[x]|=out[y];}
 for(let x=0;x<n;x++)second[x]&=full&~(out[x]|1<<x);
 const far=out.map((m,x)=>full&~(m|second[x]|1<<x));
 const protection=[];for(let x=0;x<n;x++)for(let y=0;y<n;y++)if((out[y]&(1<<x))&&!(inc[y]&~inc[x]))protection.push([y,x]);
 const F=far.map((m,x)=>m&~protection.filter(e=>e[1]===x).reduce((b,e)=>b|1<<e[0],0));
 const fixed=out.slice(), flexible=[];let actual=0;
 for(let a=0;a<n;a++)for(let b=a+1;b<n;b++)if(!((out[a]&(1<<b))||(out[b]&(1<<a)))){
  let fa=0,fb=0;for(let r=0;r<n;r++){if((out[r]&(1<<a))&&(far[r]&(1<<b)))fa|=1<<r;if((out[r]&(1<<b))&&(far[r]&(1<<a)))fb|=1<<r;}
  if((!fa&&!fb)||(fa&&fb)){flexible.push([a,b]);if(fa&&fb)actual|=fa|fb;}
  else fixed[fa?b:a]|=1<<(fa?a:b);
 }
 const orders=allPerms.get(n);let best=-1,chosen;
 for(const q of orders)if(protection.every(([y,x])=>q.rank[y]<q.rank[x])){const score=forward(fixed,q.p);if(score>best){best=score;chosen=q;}}
 if(!chosen)fail('no protection extension',{out,protection});
 if(!restrictedFamilyControl){
  const ref=orders.find(q=>protection.every(([y,x])=>q.rank[y]<q.rank[x])),T0=fixed.slice();
  for(const [a,b]of flexible)T0[ref.rank[a]<ref.rank[b]?a:b]|=1<<(ref.rank[a]<ref.rank[b]?b:a);
  let top=-1,candidates=[];for(const q of orders){const v=forward(T0,q.p);if(v>top){top=v;candidates=[q];}else if(v===top)candidates.push(q);}
  for(const q of candidates)for(const [a,b]of flexible){const tail=T0[a]&(1<<b)?a:b,head=tail===a?b:a;if(q.rank[tail]>q.rank[head])restrictedFamilyControl={out,originalProtection:protection,onlyReference:ref.p,T0,median:q.p,backwardFlex:[tail,head],medianScore:top};}
 }
 const T=fixed.slice();for(const [a,b]of flexible)T[chosen.rank[a]<chosen.rank[b]?a:b]|=1<<(chosen.rank[a]<chosen.rank[b]?b:a);
 let medBest=-1,medians=[];for(const q of orders){const v=forward(T,q.p);if(v>medBest){medBest=v;medians=[q];}else if(v===medBest)medians.push(q);}
 if(medBest!==best+flexible.length)fail('unexpected maximizing score',{out,T,best,medBest,flexible});
 for(const q of medians){
  if(!protection.every(([y,x])=>q.rank[y]<q.rank[x]))fail('median violates original protection',{out,T,order:q.p,protection});
  for(const [a,b]of flexible){const tail=T[a]&(1<<b)?a:b,head=tail===a?b:a;if(q.rank[tail]>q.rank[head])fail('median has backward flexible edge',{out,T,order:q.p,tail,head});}
  const f=q.p[n-1];
  if(!nonunitFeedControl&&(actual&(1<<f))&&pop(F[f])>1&&pop(out[f])>pop(second[f])){
   let Ttwo=0;for(let a=0;a<n;a++)if(T[f]&(1<<a))Ttwo|=T[a];Ttwo&=full&~(T[f]|1<<f);
   nonunitFeedControl={out,T,median:q.p,feed:f,originalGap:pop(out[f])-pop(second[f]),unprotectedHeads:pop(F[f]),addedFirst:pop(T[f]&~out[f]),newFarSecondHeads:pop(Ttwo&far[f]),completedGap:pop(T[f])-pop(Ttwo)};
  }
 }
 counts.graphs++;counts.medianOrders+=medians.length;counts.flexibleEdges+=flexible.length;
 if(Array.from({length:n},(_,x)=>x).some(x=>(actual&(1<<x))&&pop(F[x])>1))counts.nonunitWitnessGraphs++;
}
for(let n=2;n<=5;n++){const pairs=n*(n-1)/2,total=3**pairs;for(let code=0;code<total;code++){let c=code;const out=Array(n).fill(0);for(let a=0;a<n;a++)for(let b=a+1;b<n;b++){const v=c%3;c=Math.floor(c/3);if(v===1)out[a]|=1<<b;if(v===2)out[b]|=1<<a;}attack(out);}}
attack([0,36,17,34,2,4]);
let state=0xc051005;function rand(){state=(Math.imul(state,1664525)+1013904223)>>>0;return state/4294967296;}
for(let trial=0;trial<1200;trial++){const n=6+(trial%2),out=Array(n).fill(0),density=.3+.6*(trial%5)/4;for(let a=0;a<n;a++)for(let b=a+1;b<n;b++)if(rand()<density){if(rand()<.5)out[a]|=1<<b;else out[b]|=1<<a;}attack(out);}
const result={status:'PASS',counts,nonunitFeedControl,restrictedFamilyControl,scope:'Every oriented graph n=2..5 plus 1200 fixed-seed six/seven-vertex graphs. Independently enumerates every order, every median of one maximizing completion, and all flexible directions. Not a proof of SNC.'};
fs.writeFileSync(path.join(__dirname,'audit_independent_maximal_reference.results.json'),JSON.stringify(result,null,2)+'\n');console.log(JSON.stringify(result,null,2));
