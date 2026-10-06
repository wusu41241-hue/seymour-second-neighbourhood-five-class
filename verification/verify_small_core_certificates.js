"use strict";
// Solver-independent complete verification of the generated integer witnesses.
// This reconstructs incoming patterns using outgoing rows, not generator helpers.
const fs = require("fs");
const path = require("path");
function requireThat(ok, message) { if (!ok) throw new Error(message); }
function decode(n, code) {
  const rows = Array.from({length:n},()=>Array(n).fill(false));
  for (let a=0;a<n;a++) for (let b=a+1;b<n;b++) {
    const trit=code%3; code=Math.floor(code/3);
    if(trit===1) rows[a][b]=true;
    if(trit===2) rows[b][a]=true;
  }
  return rows;
}
const results=[];
for (const n of [1,2,3,4,5]) {
  const source=path.join(__dirname,`incoming_core_certificates_n${n}.json`);
  const artifact=JSON.parse(fs.readFileSync(source,"utf8"));
  const total=3**(n*(n-1)/2);
  requireThat(artifact.n===n && artifact.certificates.length===total,`Incomplete order-${n} certificate coverage`);
  let inequalities=0,largest=0;
  for(let code=0;code<total;code++) {
    const adj=decode(n,code), w=artifact.certificates[code];
    requireThat(w.length===n&&w.every(x=>Number.isSafeInteger(x)&&x>=0)&&w.some(x=>x>0)&&Number.isSafeInteger(w.reduce((s,x)=>s+x,0)),`Bad vector at ${n}/${code}`);
    largest=Math.max(largest,...w);
    for(let mask=1;mask<(1<<n);mask++) {
      let hasCommonOutneighbor=false;
      for(let j=0;j<n;j++) {
        let allPointToJ=true;
        for(let i=0;i<n;i++) if((mask&(1<<i))&&!adj[i][j]) allPointToJ=false;
        if(allPointToJ) hasCommonOutneighbor=true;
      }
      if(!hasCommonOutneighbor) continue;
      let inside=0,externalIncoming=0;
      for(let i=0;i<n;i++) {
        if(mask&(1<<i)) inside+=w[i];
        else {
          let pointsIntoPattern=false;
          for(let j=0;j<n;j++) if((mask&(1<<j))&&adj[i][j]) pointsIntoPattern=true;
          if(pointsIntoPattern) externalIncoming+=w[i];
        }
      }
      requireThat(externalIncoming>=inside,`Inequality failed at n=${n},code=${code},P=${mask}`);
      inequalities++;
    }
  }
  results.push({n,graphs:total,inequalities,maximumIntegerWeight:largest,status:"PASS"});
}
console.log(JSON.stringify({status:"PASS",orders:results,graphs:results.reduce((s,r)=>s+r.graphs,0),inequalities:results.reduce((s,r)=>s+r.inequalities,0),arithmetic:"Exact safe integers only; no solver, numerical tolerance, or imported graph code.",scope:"Complete certificate verification for every labeled oriented CORE of orders one through five. The transfer to arbitrary-order graphs is a separate mathematical theorem."},null,2));
