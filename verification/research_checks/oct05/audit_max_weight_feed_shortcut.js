"use strict";
const fs=require("fs"),path=require("path");
function* perms(a){if(!a.length){yield [];return;}for(let i=0;i<a.length;i++)for(const p of perms([...a.slice(0,i),...a.slice(i+1)]))yield [a[i],...p];}
let seed=0x5105feed;function rng(){seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;return(seed>>>0)/4294967296;}
let found=null,tested=0;
for(let n=4;n<=6&&!found;n++){
 const orders=[...perms(Array.from({length:n},(_,i)=>i))];
 for(let trial=0;trial<30000&&!found;trial++){
  const out=Array(n).fill(0),W=Array.from({length:n},()=>Array(n).fill(0));
  for(let a=0;a<n;a++)for(let b=a+1;b<n;b++){const x=rng()<.5?a:b,y=x===a?b:a;out[x]|=1<<y;W[x][y]=x===0?2:(rng()<.5?1:2);}
  tested++;if(!out[0])continue;
  let alpha=0,beta=0;for(let a=0;a<n;a++)if(out[0]&(1<<a))alpha+=W[0][a];
  const heads=[];for(let y=1;y<n;y++){let m=0;for(let a=0;a<n;a++)if((out[0]&(1<<a))&&(out[a]&(1<<y)))m=Math.max(m,W[a][y]-W[0][y]);if(m>0){beta+=m;heads.push([y,m]);}}
  if(alpha<=beta)continue;
  let best=-1,endingBest=-1,endingOrder=null;
  for(const p of orders){let score=0;for(let i=0;i<n;i++)for(let j=i+1;j<n;j++)score+=W[p[i]][p[j]];best=Math.max(best,score);if(p.at(-1)===0&&score>endingBest){endingBest=score;endingOrder=p;}}
  if(endingBest===best)found={n,out,arcWeights:W,globalMedianOrder:endingOrder,globalMedianScore:best,feed:0,allOutgoingFeedWeights:2,maximumArcWeight:2,alpha,beta,heads};
 }
}
const result={status:found?"RESTRICTED_SHORTCUT_REFUTED":"NO_WITNESS_FOUND_IN_FINITE_SAMPLE",seed:"0x5105feed",tested,control:found,
 limits:["This tests an unproved median-FEED claim, not the existential arc-weighted tournament theorem or SNC.","The tested feed has every outgoing arc at maximum global weight; all orders are exactly enumerated for any found witness."]};
fs.writeFileSync(path.join(__dirname,"audit_max_weight_feed_shortcut.results.json"),JSON.stringify(result,null,2)+"\n");console.log(JSON.stringify(result,null,2));
