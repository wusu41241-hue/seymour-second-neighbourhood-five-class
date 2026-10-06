'use strict';
// Independent exhaustive attack on the relational premises of the general
// closed matching module lemma. No all-deficiency/eta/minimality is assumed
// for sampled graphs; hence this is not a counterexample search for SSNC.
const assert=require('node:assert/strict');
function data(A) {
  const n=A.length,R=Array.from({length:n},()=>({first:new Set(),second:new Set()}));
  for(let x=0;x<n;x++){
    for(let y=0;y<n;y++)if(A[x][y])R[x].first.add(y);
    for(const q of R[x].first)for(let y=0;y<n;y++)if(A[q][y]&&y!==x&&!R[x].first.has(y))R[x].second.add(y);
  }
  const Far=Array.from({length:n},(_,x)=>new Set(Array.from({length:n},(_,y)=>y).filter(y=>y!==x&&!R[x].first.has(y)&&!R[x].second.has(y))));
  const P=Array.from({length:n},(_,x)=>new Set(Array.from({length:n},(_,y)=>y).filter(y=>Far[y].has(x))));
  const Q=Array.from({length:n},(_,x)=>new Set(Array.from({length:n},(_,y)=>y).filter(y=>R[y].second.has(x))));
  const C=P.map(S=>{const B=new Set();for(const p of S)for(let y=0;y<n;y++)if(A[p][y]&&!S.has(y))B.add(y);return B;});
  const F=Far.map((S,x)=>new Set([...S].filter(y=>!A[y][x]||Array.from({length:n},(_,q)=>q).some(q=>A[q][y]&&!A[q][x]))));
  const bad=[],sources=new Set();
  for(let a=0;a<n;a++)for(let b=a+1;b<n;b++)if(!A[a][b]&&!A[b][a]) {
    const ab=Array.from({length:n},(_,x)=>x).filter(x=>A[x][a]&&Far[x].has(b));
    const ba=Array.from({length:n},(_,x)=>x).filter(x=>A[x][b]&&Far[x].has(a));
    if(ab.length&&ba.length){bad.push([a,b]);for(const x of [...ab,...ba])sources.add(x);}
  }
  return{R,Far,P,Q,C,F,bad,sources};
}
const results=[];
for(const [H,o] of [[4,1],[6,1],[8,1],[4,2]]) {
  const n=H+o,k=H/2,base=Array.from({length:n},()=>Array(n).fill(0)),free=[];
  for(let x=0;x<H;x++)for(let y=0;y<H;y++)if((y-x+H)%H>k)base[x][y]=1;
  for(let a=0;a<n;a++)for(let b=a+1;b<n;b++)if(a>=H||b>=H)free.push([a,b]);
  const total=3**free.length;
  let eligible=0,partialOutsideCandidates=0;
  for(let code=0;code<total;code++) {
    const A=base.map(r=>r.slice());let word=code;
    for(const[a,b]of free){const r=word%3;word=Math.floor(word/3);if(r===1)A[a][b]=1;if(r===2)A[b][a]=1;}
    const D=data(A);
    if(D.F.some(S=>S.size>1)||Array.from({length:H},(_,x)=>x).some(x=>D.F[x].size!==1||!D.F[x].has((x+1)%H)))continue;
    if(D.bad.length!==k||D.bad.some(([a,b])=>a>=H||b-a!==k))continue;
    if(D.sources.size!==H||[...D.sources].some(x=>x>=H))continue;
    if(Array.from({length:H},(_,x)=>x).some(x=>D.Q[x].size!==D.C[x].size||[...D.Q[x]].some(q=>!D.C[x].has(q))))continue;
    let weakPacket=true;
    for(let y=H;y<n;y++)for(const x of D.Q[y])if(!A[x][y]&&!A[y][x]&&!D.C[y].has(x))weakPacket=false;
    if(!weakPacket)continue;
    eligible++;
    for(let y=H;y<n;y++) {
      const toH=Array.from({length:H},(_,x)=>x).filter(x=>A[y][x]).length;
      const fromH=Array.from({length:H},(_,x)=>x).filter(x=>A[x][y]).length;
      if(toH+fromH!==H)partialOutsideCandidates++;
      assert.ok((toH===H&&fromH===0)||(fromH===H&&toH===0));
    }
    const Hat=A.map(r=>r.slice());for(let x=0;x<H;x++)for(let y=0;y<H;y++)Hat[x][y]=0;
    const after=data(Hat);
    for(let x=0;x<n;x++)assert.equal(after.R[x].first.size-after.R[x].second.size,D.R[x].first.size-D.R[x].second.size);
    for(let y=H;y<n;y++){assert.deepEqual(after.R[y].first,D.R[y].first);assert.deepEqual(after.R[y].second,D.R[y].second);}
  }
  assert.ok(eligible>0);
  results.push({H,outside:o,graphs:total,eligible,partialOutsideCandidates});
}
console.log(JSON.stringify({status:'PASS',scope:'relational module and exact internal-deletion accounting only; no eta/minimality/SSNC assertion',results},null,2));
