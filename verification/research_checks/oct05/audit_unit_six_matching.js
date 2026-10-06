'use strict';
// Independent abstract root-certificate check. Does not construct or
// verify an all-deficient oriented graph.
const assert=require('node:assert/strict');
function matchings(V) {
  if(!V.length)return[[]];
  const a=V[0],out=[];
  for(let j=1;j<V.length;j++)for(const rest of matchings(V.filter((_,i)=>i!==0&&i!==j)))out.push([[a,V[j]],...rest]);
  return out;
}
function permutations(V) {
  if(!V.length)return[[]];
  return V.flatMap(x=>permutations(V.filter(y=>y!==x)).map(rest=>[x,...rest]));
}
const n=6,perms=permutations([0,1,2,3,4,5]);
let configsSix=0,configsThreeThree=0,rootChecks=0;
for(const E of matchings([0,1,2,3,4,5])) {
  const partner=Array(n);for(const[a,b]of E){partner[a]=b;partner[b]=a;}
  for(const h of perms) {
    if(h.some((v,x)=>v===x||h[v]===x)||h.some((v,x)=>partner[v]!==h[partner[x]]))continue;
    const edgeIndex=new Map(E.map((e,i)=>[e.slice().sort((a,b)=>a-b).join(','),i]));
    const nextEdge=E.map(([a,b])=>edgeIndex.get([h[a],h[b]].sort((a,b)=>a-b).join(',')));
    if(nextEdge[0]===0||nextEdge[nextEdge[0]]===0||nextEdge[nextEdge[nextEdge[0]]]!==0)continue;
    const seen=new Set(),lengths=[];
    for(let x=0;x<n;x++)if(!seen.has(x)){let y=x,k=0;do{seen.add(y);y=h[y];k++;}while(y!==x);lengths.push(k);}
    lengths.sort((a,b)=>a-b);
    const certificates=[];
    for(let mask=0;mask<8;mask++) {
      const indeg=Array(n).fill(0),outdeg=Array(n).fill(0);
      E.forEach(([a,b],i)=>{const s=(mask>>i)&1?b:a,t=s===a?b:a;outdeg[s]++;indeg[t]++;});
      const obstructive=[0,1,2,3,4,5].filter(x=>outdeg[x]===0&&indeg[h[x]]>0);
      certificates.push({mask,obstructive});
    }
    if(lengths.join(',')==='6') {
      configsSix++;
      assert.ok(certificates.some(c=>c.obstructive.length===0));
    } else {
      assert.equal(lengths.join(','),'3,3');configsThreeThree++;
      for(let forcedRoot=0;forcedRoot<n;forcedRoot++) {
        assert.ok(certificates.some(c=>c.obstructive.every(x=>x===forcedRoot)));
        rootChecks++;
      }
    }
  }
}
console.log(JSON.stringify({status:'PASS',scope:'all abstract six-vertex perfect matchings and eligible automorphisms; orientation certificates only',configsSix,configsThreeThree,arbitraryForcedRootCertificates:rootChecks},null,2));
