"use strict";
const fs=require("fs"),path=require("path");
const src=fs.readFileSync(path.join(__dirname,"audit_global_completion_routes.js"),"utf8").split("const counts=")[0];
const {data}=new Function("require",src+"\nreturn {data};")(require);
function pc(m){let s=0;for(;m;m&=m-1)s++;return s;}
function eta(d,x){let incomingTwo=0;for(let v=0;v<d.n;v++)if(d.two[v]&(1<<x))incomingTwo++;return pc(d.M[x])-1+incomingTwo-pc(d.two[x]);}
let seed=0x51c3c3c3;function random(){seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;return(seed>>>0)/4294967296;}
const counts={graphs:0,copiedVertices:0,fieldIdentityChecks:0};
for(let s=0;s<1000;s++){
 const n=3+s%6,out=Array(n).fill(0);for(let a=0;a<n;a++)for(let b=a+1;b<n;b++)if(random()<.65){if(random()<.5)out[a]|=1<<b;else out[b]|=1<<a;}
 const d=data(out),full=(1<<n)-1,copy=[];
 for(let block=0;block<3;block++)for(let x=0;x<n;x++)copy.push((out[x]<<(block*n))|(full<<(((block+1)%3)*n)));
 const cd=data(copy),minimum=o=>Math.min(...o.map(pc));
 if(copy.length-2*minimum(copy)!==n-2*minimum(out))throw Error("degree defect not preserved");
 if(pc(cd.actual)!==3*pc(d.actual))throw Error("actual-source replication mismatch");
 for(let block=0;block<3;block++)for(let x=0;x<n;x++){
  const v=block*n+x,shift=m=>m<<(block*n);
  const eq={out:copy[v]===(shift(out[x])|(full<<(((block+1)%3)*n))),
   second:cd.two[v]===(shift(d.two[x])|(full<<(((block+2)%3)*n))),
   missing:cd.M[v]===shift(d.M[x]),farIn:cd.P[v]===shift(d.P[x]),
   unprotectedFar:cd.F[v]===shift(d.F[x]),protectedFar:cd.prot[v]===shift(d.prot[x]),
   gap:cd.g[v]===d.g[x],residual:eta(cd,v)===eta(d,x)};
  for(const[k,ok]of Object.entries(eq)){if(!ok)throw Error(JSON.stringify({k,out,copy,x,v}));counts.fieldIdentityChecks++;}
  counts.copiedVertices++;
 }
 counts.graphs++;
}
const result={status:"PASS",seed:"0x51c3c3c3",counts,
 scope:"Checks exact amplification identities on arbitrary fixed-seed graphs of orders three through eight. These are not hypothetical counterexamples; the operation does not preserve arbitrary arc-set minimality."};
fs.writeFileSync(path.join(__dirname,"audit_cyclic_amplification.results.json"),JSON.stringify(result,null,2)+"\n");console.log(JSON.stringify(result,null,2));
