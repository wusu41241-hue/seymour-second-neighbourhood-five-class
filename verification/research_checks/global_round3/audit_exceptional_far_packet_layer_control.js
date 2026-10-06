'use strict';
// A geometry control, not a minimal counterexample or an SNC counterexample.
const fs=require('fs'),path=require('path');
const out=[34,4,24,16,1,2],n=out.length,full=(1<<n)-1;
const ids=x=>Array.from({length:n},(_,i)=>i).filter(i=>(x>>>i)&1);
const pc=x=>ids(x).length;
const inn=Array(n).fill(0);for(let a=0;a<n;a++)for(const b of ids(out[a])){if(a===b||(out[b]&(1<<a)))throw Error('Not oriented');inn[b]|=1<<a;}
const second=(adj,a)=>{let x=0;for(const b of ids(adj[a]))x|=adj[b];return x&~(adj[a]|1<<a);};
const two=out.map((_,a)=>second(out,a)),far=out.map((_,a)=>full&~(out[a]|two[a]|1<<a));
const f=0,P=out.reduce((m,_,a)=>m|((far[a]&(1<<f))?1<<a:0),0);
const boundary=S=>{let x=0;for(const a of ids(S))x|=out[a];return x&~S;};
const C=boundary(P),X=boundary(C)&~P,Q=second(inn,f),H=Q&~C;
const missing=full&~(out[f]|inn[f]|1<<f),B=H&missing;
const E=(missing&~B)|X,L=E&~two[f],eta=pc(missing)-1+pc(Q)-pc(two[f]);
if(P!==34 || C!==4 || Q!==12 || H!==8 || X!==24 || B!==8 || !(X&B))throw Error('Layer control changed');
if(!(L&B) || eta!==2 || pc(out[f])-pc(two[f])!==1)throw Error('Exceptional far head control changed');
const result={status:'PASS',outMasks:out,vertex:f,
  P:ids(P),C:ids(C),secondIn:ids(Q),exceptionalLayer:ids(H),externalSecondLayer:ids(X),
  incoming:ids(inn[f]),missing:ids(missing),exceptionalMissing:ids(B),E:ids(E),L:ids(L),
  originalGap:pc(out[f])-pc(two[f]),residual:eta,allGaps:out.map((_,a)=>pc(out[a])-pc(two[a])),
  meaning:'External second boundary can contain a missing exceptional far head; exceptional head 3 is in E and L through X.',
  scope:'Strong oriented graph, but other vertices have nonpositive gaps. Not all-deficient, not deletion-minimal, not an SNC counterexample; numerical MIN packet estimate is not applied.'};
fs.writeFileSync(path.join(__dirname,'audit_exceptional_far_packet_layer_control.results.json'),JSON.stringify(result,null,2));console.log(JSON.stringify(result,null,2));
