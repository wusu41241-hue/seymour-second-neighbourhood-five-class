"use strict";
// Exhaustive exact small-core pattern certificates. Integer cofactors, no LP library.
const fs=require("fs"),path=require("path");
function pc(m){let r=0;for(;m;m&=m-1)r++;return r;}
function ids(m,n){const a=[];for(let i=0;i<n;i++)if(m&(1<<i))a.push(i);return a;}
function core(out){const n=out.length,full=(1<<n)-1,inc=Array(n).fill(0);
 for(let i=0;i<n;i++)for(const j of ids(out[i],n)){if(i===j||out[j]&(1<<i))throw Error("Not oriented");inc[j]|=1<<i;}
 const patterns=[];for(let P=0;P<=full;P++)if(inc.some(I=>!(P&~I))){let R=0;for(const j of ids(P,n))R|=inc[j];R&=full&~P;patterns.push({P,R,row:Array.from({length:n},(_,i)=>(R&(1<<i))?1:(P&(1<<i))?-1:0)});}return{n,full,inc,patterns};}
function det(A){const n=A.length;if(!n)return 1;if(n===1)return A[0][0];let r=0;for(let j=0;j<n;j++)if(A[0][j])r+=(j%2?-1:1)*A[0][j]*det(A.slice(1).map(row=>row.filter((_,c)=>c!==j)));return r;}
function dot(a,b){return a.reduce((r,v,i)=>r+v*b[i],0);}
function certificate(C){const n=C.n,rows=Array.from({length:n},(_,i)=>Array.from({length:n},(_,j)=>i===j?1:0)).concat(C.patterns.map(p=>p.row));let answer=null;const chosen=[];
 function walk(next){if(answer)return;if(chosen.length===n-1){const A=chosen.map(j=>rows[j]),w=Array.from({length:n},(_,i)=>(i%2?-1:1)*det(A.map(row=>row.filter((_,j)=>j!==i))));const first=w.find(x=>x!==0);if(first===undefined)return;if(first<0)for(let i=0;i<n;i++)w[i]=-w[i];if(w.some(x=>x<0)||rows.some(row=>dot(row,w)<0))return;for(const row of A)if(dot(row,w)!==0)throw Error("Cofactor kernel failure");answer={weights:w,denominator:w.reduce((s,x)=>s+x,0),activeRows:chosen.slice()};return;}
  for(let j=next;j<=rows.length-(n-1-chosen.length);j++){chosen.push(j);walk(j+1);chosen.pop();if(answer)return;}}
 walk(0);return answer;}
const certificates=[],summary={status:"PASS",coresByOrder:{},totalCores:0,totalPatternChecks:0,largestWeight:0,largestDenominator:0,infeasibleCore:null};
for(let n=1;n<=4;n++){let count=0;for(let code=0;code<3**(n*(n-1)/2);code++){let z=code;const out=Array(n).fill(0);for(let i=0;i<n;i++)for(let j=i+1;j<n;j++){const v=z%3;z=Math.floor(z/3);if(v===1)out[i]|=1<<j;if(v===2)out[j]|=1<<i;}const C=core(out),cert=certificate(C);if(!cert){summary.status="INFEASIBLE CORE";summary.infeasibleCore={n,code,out,patterns:C.patterns};break;}certificates.push({n,code,out,...cert});summary.totalCores++;summary.totalPatternChecks+=C.patterns.length;summary.largestWeight=Math.max(summary.largestWeight,...cert.weights);summary.largestDenominator=Math.max(summary.largestDenominator,cert.denominator);count++;}summary.coresByOrder[n]=count;if(summary.infeasibleCore)break;}
fs.writeFileSync(path.join(__dirname,"incoming_pattern_certificates_le4.json"),JSON.stringify({summary,certificates},null,2)+"\n");
fs.writeFileSync(path.join(__dirname,"generate_incoming_pattern_certificates_le4.results.json"),JSON.stringify(summary,null,2)+"\n");console.log(JSON.stringify(summary,null,2));

