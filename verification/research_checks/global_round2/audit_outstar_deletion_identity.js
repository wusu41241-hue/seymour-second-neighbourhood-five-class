"use strict";
const fs=require('fs'),path=require('path');
function ok(c,m,o){if(!c)throw Error(m+' '+JSON.stringify(o));}
function pc(m){let n=0;while(m){m&=m-1;n++;}return n;}
function ids(m,n){const a=[];for(let x=0;x<n;x++)if(m&(1<<x))a.push(x);return a;}
function data(out){const n=out.length,full=(1<<n)-1,inc=Array(n).fill(0),two=Array(n).fill(0);for(let f=0;f<n;f++)for(const a of ids(out[f],n)){ok(!(out[a]&(1<<f))&&a!==f,'oriented',{out,f,a});inc[a]|=1<<f;two[f]|=out[a];}for(let f=0;f<n;f++)two[f]&=full&~(out[f]|1<<f);return {n,full,inc,two,g:out.map((m,f)=>pc(m)-pc(two[f]))};}
const counts={graphs:0,outstarDeletions:0,localCriticalPositiveSources:0,localCriticalGapTwoSources:0,gapTwoSecondWitnessChecks:0};const explicit=[];
function test(out,recordF=null){const d=data(out);counts.graphs++;for(let f=0;f<d.n;f++){
 const O=out[f],B=d.two[f];let critical=d.g[f]>0;const singleton=[];
 for(let S=O;S;S=(S-1)&O){const X=O&~S;let reachable=0;for(const a of ids(X,d.n))reachable|=out[a];const actual=reachable&d.full&~(X|1<<f),R=S&reachable;let L=0;for(const b of ids(B,d.n))if(!(d.inc[b]&X))L|=1<<b;
  ok(actual===((B&~L)|R),'wrong exact second set',{out,f,S,X,actual,R,L,B});const gap=pc(X)-pc(actual),formula=d.g[f]-pc(S)+pc(L)-pc(R);ok(gap===formula,'wrong gap formula',{out,f,S,gap,formula});counts.outstarDeletions++;if(gap>0)critical=false;if(pc(S)===1)singleton.push({a:ids(S,d.n)[0],lost:pc(L),retargeted:pc(R),newGap:gap});
 }
 if(critical){counts.localCriticalPositiveSources++;if(d.g[f]===2){counts.localCriticalGapTwoSources++;for(const s of singleton)ok(s.lost===0&&s.retargeted===1&&s.newGap===0,'gap two singleton necessary property fails',{out,f,s});for(const b of ids(B,d.n)){ok(pc(d.inc[b]&O)>=2,'gap two head lacks two original witnesses',{out,f,b});counts.gapTwoSecondWitnessChecks++;}for(const a of ids(O,d.n))ok(d.inc[a]&O,'gap two out-neighborhood lacks internal predecessor',{out,f,a});}}
 if(f===recordF)explicit.push({out,vertex:f,originalGap:d.g[f],outNeighbors:ids(O,d.n),secondNeighbors:ids(B,d.n),locallyOutstarCritical:critical,singleton,secondWitnesses:ids(B,d.n).map(b=>({b,witnesses:ids(d.inc[b]&O,d.n)}))});
}}
for(let code=0;code<59049;code++){let c=code;const out=Array(5).fill(0);for(let a=0;a<5;a++)for(let b=a+1;b<5;b++){const v=c%3;c=Math.floor(c/3);if(v===1)out[a]|=1<<b;if(v===2)out[b]|=1<<a;}test(out);}
test([14,20,24,2,0],0);test([30,100,104,112,98,448,1,1,1],0);
const result={status:'PASS',counts,explicit,scope:'Exact deletion identities on all five-vertex oriented graphs. Criticality tested locally at one source, not claimed arc-minimal/all-deficient globally. The two explicit sources satisfy every proper outgoing-star deletion SNP condition but their graphs have Seymour vertices.'};fs.writeFileSync(path.join(__dirname,'audit_outstar_deletion_identity.results.json'),JSON.stringify(result,null,2)+'\n');console.log(JSON.stringify(result,null,2));
