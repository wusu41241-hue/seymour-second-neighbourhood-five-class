"use strict";
// Independent boolean-adjacency verifier. No generator helpers, LP, SAT or floats.
const fs=require('fs'),path=require('path'),crypto=require('crypto');
function assert(c,m,d){if(!c)throw Error(m+' '+JSON.stringify(d));}
function decode(n,code){const E=Array.from({length:n},()=>Array(n).fill(false));let z=code;for(let a=0;a<n;a++)for(let b=a+1;b<n;b++){const s=z%3;z=Math.floor(z/3);if(s===1)E[a][b]=true;else if(s===2)E[b][a]=true;}return E;}
const counts={cores:0,patterns:0,nonemptyPatterns:0,byOrder:{},nonuniformFive:0,maxWeight:0,maxSumWeights:0},hashes=[];
for(let n=1;n<=5;n++){
 const total=3**(n*(n-1)/2);let rows=null;if(n>=4){const filename='incoming_core_certificates_n'+n+'.json',raw=fs.readFileSync(path.join(__dirname,filename));hashes.push({file:filename,sha256:crypto.createHash('sha256').update(raw).digest('hex')});const table=JSON.parse(raw.toString('utf8'));assert(table.n===n&&table.certificates.length===total,'table coverage',{n});rows=table.certificates;}
 for(let code=0;code<total;code++){
  const E=decode(n,code);let weights;if(rows)weights=rows[code];else{const sink=E.findIndex(row=>row.every(x=>!x));weights=sink>=0?Array.from({length:n},(_,i)=>i===sink?1:0):Array(n).fill(1);}
  assert(Array.isArray(weights)&&weights.length===n&&weights.every(w=>Number.isSafeInteger(w)&&w>=0)&&weights.some(w=>w>0),'invalid density',{n,code,weights});
  counts.maxWeight=Math.max(counts.maxWeight,...weights);counts.maxSumWeights=Math.max(counts.maxSumWeights,weights.reduce((s,w)=>s+w,0));if(n===5&&new Set(weights.filter(w=>w>0)).size>1)counts.nonuniformFive++;
  for(let mask=0;mask<(1<<n);mask++){
   const P=Array.from({length:n},(_,i)=>i).filter(i=>mask&(1<<i));
   if(!Array.from({length:n},(_,j)=>j).some(j=>P.every(i=>E[i][j])))continue;
   const R=Array.from({length:n},(_,i)=>i).filter(i=>!(mask&(1<<i))&&P.some(j=>E[i][j]));
   const rhs=P.reduce((s,i)=>s+weights[i],0),lhs=R.reduce((s,i)=>s+weights[i],0);
   assert(lhs>=rhs,'incoming pattern expansion fails',{n,code,E,weights,P,R,lhs,rhs});counts.patterns++;if(P.length)counts.nonemptyPatterns++;
  }
  counts.cores++;
 }
 counts.byOrder[n]=total;
}
const result={status:'PASS',counts,hashes,scope:'Independent Boolean-matrix reconstruction of every labelled oriented core of orders one through five. Every admissible common-outneighbor pattern and nonnegative integer certificate checked. No floating point optimizer, LP or generator helper. This certifies an arbitrary-order structural class, not full SNC.'};
fs.writeFileSync(path.join(__dirname,'verify_core_pattern_certificates_independent.results.json'),JSON.stringify(result,null,2)+'\n');console.log(JSON.stringify(result,null,2));
