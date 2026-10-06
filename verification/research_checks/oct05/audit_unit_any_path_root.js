'use strict';
// Finite independent check of the arbitrary prescribed dangerous-leaf
// certificate. This verifies a combinatorial orientation step only.
const assert=require('node:assert/strict');
let exceptionalOrbits=0,forcedLeafChecks=0,orientations=0;
for(let k=2;k<=12;k++)for(const swap of [0,1]) {
  const exceptional=(k%2===1&&swap===0)||(k%2===0&&swap===1);
  const danger=[];
  for(let mask=0;mask<2**k;mask++) {
    const roots=Array.from({length:k},(_,i)=>(mask>>i)&1),D=[];
    for(let i=0;i<k;i++){
      const next=(i+1)%k,hBit=roots[i]^(i===k-1?swap:0);
      if(roots[next]===hBit)D.push(2*i+roots[i]);
    }
    danger.push(D);orientations++;
  }
  if(exceptional) {
    exceptionalOrbits++;
    assert.equal(Math.min(...danger.map(d=>d.length)),1);
    for(let x=0;x<2*k;x++) {
      assert.ok(danger.some(d=>d.length===1&&d[0]===x));forcedLeafChecks++;
    }
  } else assert.ok(danger.some(d=>d.length===0));
}
console.log(JSON.stringify({status:'PASS',scope:'path-component leaf-return-map orientations, k=2..12; not a graph-theoretic SSNC proof',exceptionalOrbits,arbitraryForcedLeafCertificates:forcedLeafChecks,orientations},null,2));
