'use strict';
// Independent finite check of the graph-level envelope, not of minimality
// or the external-boundary inequality. Enumerates every labeled oriented
// graph on at most five vertices and one specified canonical completion
// per eligible vertex; also checks fixed-seed random orders six to twelve.
const assert = require('node:assert/strict');
const nMax = Number(process.argv[2] || 5);
const randomPerOrder = Number(process.argv[3] || 2000);
let randomState = 0x31a11ce5;
function rng() {randomState^=randomState<<13;randomState^=randomState>>>17;randomState^=randomState<<5;return(randomState>>>0)/4294967296;}
const results = [];
function reach2(A,v) {
  const first=new Set(),second=new Set();
  for(let q=0;q<A.length;q++)if(A[v][q])first.add(q);
  for(const q of first)for(let y=0;y<A.length;y++)
    if(A[q][y]&&y!==v&&!first.has(y))second.add(y);
  return {first,second};
}
function boundary(A,S) {
  const B=new Set();
  for(const x of S)for(let y=0;y<A.length;y++)if(A[x][y]&&!S.has(y))B.add(y);
  return B;
}
for(let n=1;n<=Math.max(12,nMax);n++) {
  const pairs=[];
  for(let a=0;a<n;a++)for(let b=a+1;b<n;b++)pairs.push([a,b]);
  const exhaustive=n<=nMax;
  const total=exhaustive?3**pairs.length:randomPerOrder;
  let tested=0,nonemptyP=0,badKeepers=0,multipleKeepers=0;
  for(let code=0;code<total;code++) {
    const A=Array.from({length:n},()=>Array(n).fill(0));
    let word=code;
    for(const [a,b]of pairs){let r;
      if(exhaustive){r=word%3;word=Math.floor(word/3);}
      else {const q=rng(),missingRate=[0.1,1/3,0.55,0.75][code%4];r=q<missingRate?0:(rng()<0.5?1:2);}
      if(r===1)A[a][b]=1;if(r===2)A[b][a]=1;
    }
    const R=Array.from({length:n},(_,v)=>reach2(A,v));
    const Far=Array.from({length:n},(_,v)=>new Set(Array.from({length:n},(_,q)=>q).filter(q=>q!==v&&!R[v].first.has(q)&&!R[v].second.has(q))));
    const P=Array.from({length:n},(_,v)=>new Set(Array.from({length:n},(_,q)=>q).filter(q=>Far[q].has(v))));
    const protectedEdges=[];
    for(let x=0;x<n;x++)for(const y of Far[x])if(A[y][x]&&Array.from({length:n},(_,q)=>q).every(q=>!A[q][y]||(q!==y&&A[q][x])))protectedEdges.push([y,x]);
    const miss=pairs.filter(([a,b])=>!A[a][b]&&!A[b][a]);
    const FS=miss.map(([a,b])=>({a,b,ab:Array.from({length:n},(_,x)=>x).filter(x=>A[x][a]&&Far[x].has(b)),ba:Array.from({length:n},(_,x)=>x).filter(x=>A[x][b]&&Far[x].has(a))}));
    for(let u=0;u<n;u++) {
      const M=new Set(miss.filter(([a,b])=>a===u||b===u).map(([a,b])=>a===u?b:a));
      if([...M].some(x=>P[u].has(x)))continue;
      const avoid=new Set([...P[u],u]);
      if(FS.some(f=>f.ab.length&&f.ba.length&&f.ab.some(x=>avoid.has(x))&&f.ba.some(x=>avoid.has(x))))continue;
      const edges=protectedEdges.slice();
      for(const f of FS)if((f.a===u||f.b===u)&&(!f.ab.length||!f.ba.length))edges.push([f.a===u?f.b:f.a,u]);
      const left=new Set(Array.from({length:n},(_,v)=>v)),order=[];
      while(left.size){const v=[...left].find(v=>edges.every(([a,b])=>b!==v||!left.has(a)));assert.notEqual(v,undefined);left.delete(v);order.push(v);}
      const rank=Object.fromEntries(order.map((v,i)=>[v,i]));
      const T=A.map(r=>r.slice());
      for(const f of FS){let ab;
        if(f.ab.length&&f.ba.length)ab=!f.ab.some(x=>avoid.has(x));
        else if(f.ab.length)ab=false;else if(f.ba.length)ab=true;else ab=rank[f.a]<rank[f.b];
        if(ab)T[f.a][f.b]=1;else T[f.b][f.a]=1;
      }
      const RT=reach2(T,u),J=new Set([...RT.first].filter(q=>!R[u].first.has(q)));
      tested++;
      if(J.size>=2)multipleKeepers++;
      if(!P[u].size){assert.equal(J.size,0);assert.deepEqual(RT.second,R[u].second);continue;}
      nonemptyP++;
      const C=boundary(A,P[u]);
      const X=new Set([...boundary(A,C)].filter(q=>!P[u].has(q)));
      const Q=new Set(Array.from({length:n},(_,q)=>q).filter(q=>R[q].second.has(u)));
      const H=new Set([...Q].filter(q=>!C.has(q))),B=new Set([...H].filter(q=>M.has(q)));
      const expected=new Set([...M].filter(q=>!B.has(q)));
      assert.deepEqual(J,expected);
      const Hat=A.map(r=>r.slice());
      for(const q of H)Hat[u][q]=0;
      const E=new Set([...expected,...X]);
      const RHat=reach2(Hat,u);
      for(const q of RHat.second)assert.ok(E.has(q));
      const L=new Set([...E].filter(q=>!RHat.second.has(q)));
      for(const q of J)assert.ok(R[u].second.has(q)||L.has(q));
      for(const y of RT.second)assert.ok((R[u].second.has(y)||L.has(y))&&!J.has(y));
      const originalGap=R[u].first.size-R[u].second.size,tournamentGap=RT.first.size-RT.second.size;
      assert.ok(tournamentGap>=originalGap+2*J.size-L.size);
      if(FS.some(f=>(f.a===u||f.b===u)&&f.ab.length&&f.ba.length))badKeepers++;
    }
  }
  results.push({n,mode:exhaustive?'exhaustive':'fixed-seed-random',graphs:total,tested,nonemptyP,badKeepers,multipleKeepers});
}
console.log(JSON.stringify({seed:'0x31a11ce5',scope:'exhaustive and fixed-seed random oriented graphs; envelopes and exact gap accounting only; no arc minimality or SSNC claim',results},null,2));
