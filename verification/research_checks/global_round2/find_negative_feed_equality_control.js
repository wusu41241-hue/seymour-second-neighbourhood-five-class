'use strict';
// Diagnostic cloning search, NOT a search for a complete SNC counterexample.
const fs=require('fs'),path=require('path');
const pc=x=>{let k=0;while(x){x&=x-1;k++;}return k;};
const ids=(x,n)=>Array.from({length:n},(_,i)=>i).filter(i=>(x>>>i)&1);
function data(out){
 const n=out.length,all=(1<<n)-1,inn=Array(n).fill(0),two=Array(n).fill(0);
 for(let x=0;x<n;x++)for(const y of ids(out[x],n)){inn[y]|=1<<x;two[x]|=out[y];}
 for(let x=0;x<n;x++)two[x]&=all&~(out[x]|1<<x);
 const far=out.map((m,x)=>all&~(m|two[x]|1<<x)),prot=[];
 for(let a=0;a<n;a++)for(let w=0;w<n;w++)if((out[a]&(1<<w))&&!(inn[a]&~inn[w]))prot.push([a,w]);
 const unprot=far.map((m,x)=>m&~prot.filter(([a,w])=>w===x).reduce((m,[a])=>m|1<<a,0));
 const missing=[];for(let a=0;a<n;a++)for(let b=a+1;b<n;b++)if(!((out[a]&(1<<b))||(out[b]&(1<<a))))missing.push([a,b]);
 return{n,all,inn,two,far,prot,unprot,missing,g:out.map((m,x)=>pc(m)-pc(two[x]))};
}
function closure(out){let Q=out.slice(),rounds=0;while(true){const qd=data(Q),next=Q.slice();let c=0;
 for(const[a,b]of qd.missing){const ab=qd.prot.some(([x,w])=>x===a&&(Q[w]&(1<<b))),ba=qd.prot.some(([x,w])=>x===b&&(Q[w]&(1<<a)));
  if(ab&&ba)throw Error('Contradictory force');if(ab){next[a]|=1<<b;c++;}if(ba){next[b]|=1<<a;c++;}}
 if(!c)return{Q,rounds};Q=next;rounds++;}}
function dp(out){const n=out.length,d=data(out),F=Array(1<<n).fill(0),ends=Array(1<<n).fill(0);
 for(let S=1;S<1<<n;S++){let best=-1;for(let v=0;v<n;v++)if(S&(1<<v)){const val=F[S^(1<<v)]+pc(d.inn[v]&S);if(val>best){best=val;ends[S]=1<<v;}else if(val===best)ends[S]|=1<<v;}F[S]=best;}
 return{F,ends};}
function* orders(ends,n,cap,last){let count=0;function* rec(S,suffix){if(!S){if(count++<cap)yield suffix;return;}if(count>=cap)return;for(let v=0;v<n;v++)if(ends[S]&(1<<v))yield*rec(S^(1<<v),[v,...suffix]);}
 const all=(1<<n)-1;if(last===undefined)yield*rec(all,[]);else if(ends[all]&(1<<last))yield*rec(all^(1<<last),[last]);}
function clone(base,x,copies,reverse){const n=base.length,N=n+copies-1,out=base.slice();while(out.length<N)out.push(0);
 const twins=[x,...Array.from({length:copies-1},(_,i)=>n+i)];
 for(let i=n;i<N;i++)for(let y=0;y<n;y++)if(y!==x){if(base[x]&(1<<y))out[i]|=1<<y;else if(base[y]&(1<<x))out[y]|=1<<i;}
 for(let i=0;i<twins.length;i++)for(let j=i+1;j<twins.length;j++){const a=twins[i],b=twins[j];out[reverse?b:a]|=1<<(reverse?a:b);}
 return out;}
const base=[6,8,8,17,65,22,33],counts={graphs:0,positivePartialMedianFeeds:0,maxCompletions:0,positiveTournamentMedianFeeds:0,negativeCompleted:0,negativeEquality:0};
let found=null,stable=null;
function attack(out){counts.graphs++;const od=data(out),n=out.length,{Q,rounds}=closure(out),qd=data(Q),D=dp(Q),all=(1<<n)-1;
 for(const f of ids(D.ends[all],n)){if(od.g[f]<=0)continue;counts.positivePartialMedianFeeds++;
 for(const ref of orders(D.ends,n,400,f)){const rank=Array(n);ref.forEach((x,i)=>rank[x]=i);const T=Q.slice();
  for(const[a,b]of qd.missing)T[rank[a]<rank[b]?a:b]|=1<<(rank[a]<rank[b]?b:a);
  counts.maxCompletions++;const td=data(T),E=dp(T);
  if(E.F[all]!==D.F[all]+qd.missing.length)throw Error('Nonmaximal clone completion');
  for(const L of orders(E.ends,n,1500,f)){counts.positiveTournamentMedianFeeds++;if(td.g[f]>=0)continue;counts.negativeCompleted++;
   const pos=Array(n);L.forEach((x,i)=>pos[x]=i);let G=0;
   for(const z of ids(td.inn[f],n))for(const a of ids(T[f],n))if(pos[a]<pos[z]&&(T[a]&(1<<z)))G|=1<<z;
   const mu=qd.missing.filter(([a,b])=>a===f||b===f).length;
   if(pc(G)===pc(T[f])){counts.negativeEquality++;const c={out,Q,T,median:L,feed:f,gOriginal:od.g[f],gCompleted:td.g[f],tOriginal:pc(od.unprot[f]),muQ:mu,good:ids(G,n),newHeads:ids(td.two[f]&~od.two[f],n),rounds};
    if(mu>pc(od.unprot[f])-od.g[f])throw Error('Degree budget failed '+JSON.stringify(c));if(!found)found=c;
   }else if(!stable)stable={out,Q,T,median:L,feed:f,gOriginal:od.g[f],gCompleted:td.g[f],tOriginal:pc(od.unprot[f]),muQ:mu,good:ids(G,n),rounds};
  }
  if(found)return;
 }
 }
}
for(let x=0;x<base.length&&!found;x++)for(let copies=2;copies<=4&&!found;copies++)for(const reverse of[false,true]){attack(clone(base,x,copies,reverse));if(found)break;}
if(!found){
 const pairs=[];for(let a=0;a<base.length;a++)for(let b=a+1;b<base.length;b++)pairs.push([a,b]);
 function change(out,a,b,state){out[a]&=~(1<<b);out[b]&=~(1<<a);if(state===1)out[a]|=1<<b;else if(state===2)out[b]|=1<<a;}
 for(const[a,b]of pairs){for(let state=0;state<3&&!found;state++){const out=base.slice();change(out,a,b,state);attack(out);}if(found)break;}
 let seed=0xfeed25;function random(){seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;return(seed>>>0)/4294967296;}
 for(let trial=0;trial<1800&&!found;trial++){const out=base.slice();for(let k=0;k<2+trial%3;k++){const[a,b]=pairs[Math.floor(random()*pairs.length)];change(out,a,b,Math.floor(3*random()));}attack(out);}
}
const result={status:'PASS',scope:'Clones and fixed-seed orientation perturbations of a known positive-original closure-feed control. Other vertices may have nonpositive gaps. Not an SNC counterexample or an exhaustive proof.',counts,negativeEqualityControl:found,stableNegativeControl:stable};
fs.writeFileSync(path.join(__dirname,'find_negative_feed_equality_control.results.json'),JSON.stringify(result,null,2));console.log(JSON.stringify(result,null,2));
