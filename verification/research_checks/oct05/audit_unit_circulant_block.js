'use strict';
// Exhaustive finite check of the elementary internal matching-block lemma.
// Head cycle = successor; opposite pairs missing; consecutive pairs
// originally reverse oriented; every successor must remain far.
const assert=require('node:assert/strict');
const results=[];
for(const k of [2,3,4]) {
  const n=2*k,free=[],base=Array.from({length:n},()=>Array(n).fill(0));
  for(let i=0;i<n;i++)base[(i+1)%n][i]=1;
  for(let a=0;a<n;a++)for(let b=a+1;b<n;b++)
    if(b-a!==k&&!base[a][b]&&!base[b][a])free.push([a,b]);
  let eligible=0;
  for(let mask=0;mask<2**free.length;mask++) {
    const A=base.map(r=>r.slice());
    free.forEach(([a,b],i)=>{if((mask>>i)&1)A[a][b]=1;else A[b][a]=1;});
    let valid=true;
    for(let x=0;x<n&&valid;x++)for(let q=0;q<n;q++)if(A[x][q]&&A[q][(x+1)%n]){valid=false;break;}
    if(!valid)continue;eligible++;
    for(let x=0;x<n;x++) {
      for(let y=0;y<n;y++)assert.equal(A[x][y],Number((y-x+n)%n>k));
      const first=new Set(),second=new Set();
      for(let y=0;y<n;y++)if(A[x][y])first.add(y);
      for(const q of first)for(let y=0;y<n;y++)if(A[q][y]&&y!==x&&!first.has(y))second.add(y);
      assert.equal(first.size,k-1);assert.equal(second.size,k-1);
      assert.deepEqual(second,new Set(Array.from({length:k-1},(_,j)=>(x+j+2)%n)));
    }
  }
  assert.equal(eligible,1);
  results.push({n,freePairs:free.length,graphs:2**free.length,eligibleCirculants:eligible});
}
console.log(JSON.stringify({status:'PASS',scope:'internal matching-block structural lemma only, not the outside module or minimality claims',results},null,2));
