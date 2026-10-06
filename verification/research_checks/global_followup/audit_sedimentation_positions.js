/* Independently checks the positional/global-score part of the two-family
 * proof. This is a finite auxiliary audit, NOT a verification of SNC.
 * Run: node audit_sedimentation_positions.js
 */
'use strict';
const fs = require('fs');
const path = require('path');
function pop(x) { let n=0; while(x) { x &= x-1; n++; } return n; }
function incoming(out) {
  const inn=Array(out.length).fill(0);
  for(let x=0;x<out.length;x++) for(let y=0;y<out.length;y++)
    if((out[x]>>>y)&1) inn[y]|=1<<x;
  return inn;
}
function second(out,x) {
  let q=0;
  for(let y=0;y<out.length;y++) if((out[x]>>>y)&1) q |= out[y];
  return q & ~out[x] & ~(1<<x);
}
function score(out,L) {
  let s=0;
  for(let i=0;i<L.length;i++) for(let j=i+1;j<L.length;j++)
    s+=(out[L[i]]>>>L[j])&1;
  return s;
}
function dynamic(out) {
  const n=out.length, inn=incoming(out), F=Array(1<<n).fill(0);
  const ends=Array(1<<n).fill(0);
  for(let S=1;S<(1<<n);S++) {
    let best=-1, ee=0;
    for(let v=0;v<n;v++) if((S>>>v)&1) {
      const q=S^(1<<v), z=F[q]+pop(inn[v]&q);
      if(z>best) { best=z; ee=1<<v; }
      else if(z===best) ee|=1<<v;
    }
    F[S]=best; ends[S]=ee;
  }
  return {F,ends};
}
function* optOrders(ends,S,limit) {
  let count=0;
  function* recurse(q,suffix) {
    if(!q) { if(count++<limit) yield suffix; return; }
    if(count>=limit) return;
    for(let v=0;v<31;v++) if((ends[q]>>>v)&1)
      yield* recurse(q^(1<<v),[v,...suffix]);
  }
  yield* recurse(S,[]);
}
let seed=0x05c0de26;
function rng() {
  seed^=seed<<13; seed^=seed>>>17; seed^=seed<<5;
  return (seed>>>0)/4294967296;
}
const tally={tournaments:0,medianOrders:0,equalityFeeds:0,
  positionalChecks:0,singletonMedianEndControl:null};
function audit(out) {
  tally.tournaments++;
  const n=out.length, all=(1<<n)-1, {F,ends}=dynamic(out);
  for(const L of optOrders(ends,all,2000)) {
    tally.medianOrders++;
    const f=L[n-1], O=out[f], G=second(out,f);
    if(pop(O)!==pop(G)) continue;
    tally.equalityFeeds++;
    const B=all&~(O|G|(1<<f));
    const M=L.filter(z=>(B>>>z)&1).concat([f],L.filter(z=>((O|G)>>>z)&1));
    if(score(out,M)!==F[all]) throw Error('Sedimentation changed optimum '+JSON.stringify({out,L,M}));
    for(let z=0;z<n;z++) if(((O|G)>>>z)&1) {
      const old=L.indexOf(z), now=M.indexOf(z);
      const expected=1+L.slice(old+1).filter(b=>(B>>>b)&1).length;
      if(now-old!==expected || now<=old) throw Error('Position identity failed');
      tally.positionalChecks++;
    }
  }
}
for(let n=3;n<=5;n++) {
  const m=n*(n-1)/2;
  for(let mask=0;mask<(1<<m);mask++) {
    const out=Array(n).fill(0); let b=0;
    for(let x=0;x<n;x++) for(let y=x+1;y<n;y++,b++) {
      if((mask>>>b)&1) out[x]|=1<<y; else out[y]|=1<<x;
    }
    audit(out);
  }
}
for(let n=6;n<=9;n++) for(let sample=0;sample<1000;sample++) {
  const out=Array(n).fill(0);
  for(let x=0;x<n;x++) for(let y=x+1;y<n;y++) {
    if(rng()<.5) out[x]|=1<<y; else out[y]|=1<<x;
  }
  audit(out);
}
{
  const out=[8,1,3,6], {F,ends}=dynamic(out);
  if(out.some(x=>!x) || ends[15]!==1 || F[15]!==5) throw Error('Control changed');
  tally.singletonMedianEndControl={outMasks:out,optimumScore:5,medianEndSet:[0],
    meaning:'Sink-free tournament can have a unique global median end; this is not an SNC counterexample.'};
}
const result={status:'PASS',scope:'Auxiliary finite check of global sedimentation and its exact position identity',
  fixedSeed:'0x05c0de26',allTournamentsOrders:'3 through 5',samplesPerOrder6Through9:1000,
  maximumEnumeratedOptimalOrdersPerTournament:2000,...tally};
fs.writeFileSync(path.join(__dirname,'audit_sedimentation_positions.results.json'),JSON.stringify(result,null,2));
console.log(JSON.stringify(result));
