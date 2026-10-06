"use strict";
// Tests retained-arc transfers without a bound on the number of failure sources.
// Original graph definitions only; finite checks are not an SNC proof.
const fs=require("fs"),path=require("path");
function pc(x){let c=0;for(;x;x&=x-1)c++;return c;}
function ids(x,n){const a=[];for(let i=0;i<n;i++)if(x&(1<<i))a.push(i);return a;}
function assert(ok,msg,details){if(!ok)throw Error(msg+JSON.stringify(details));}
function second(o,f){let t=0;for(const a of ids(o[f],o.length))t|=o[a];return t&~(o[f]|1<<f);}
const counts={allFiveGraphs:0,sampledGraphs:0,goodRetentions:0,goodRetentionsWithFourPlusSources:0,
  goodRetentionsWithProtectedFarHeads:0,badRetentionsWithUnitReverseWitness:0,
  badRetentionsWithFourPlusSources:0,newSecondHeadsCases:0};
let control=null;
function audit(o){
  const n=o.length,full=(1<<n)-1,inc=Array(n).fill(0),P=Array(n).fill(0),far=[],two=[];
  for(let f=0;f<n;f++)for(const a of ids(o[f],n))inc[a]|=1<<f;
  for(let f=0;f<n;f++){two[f]=second(o,f);far[f]=full&~(o[f]|two[f]|1<<f);for(const a of ids(far[f],n))P[a]|=1<<f;}
  const protectedFrom=far.map((m,f)=>ids(m,n).reduce((mask,y)=>(o[y]&(1<<f))&&!(inc[y]&~inc[f])?mask|1<<y:mask,0));
  const unprotected=far.map((m,f)=>m&~protectedFrom[f]);
  const missing=[],convenient=Array(n).fill(0),fail=Array.from({length:n},()=>Array(n).fill(0));let sources=0;
  for(let a=0;a<n;a++)for(let b=a+1;b<n;b++)if(!((o[a]>>b|o[b]>>a)&1)){
    const ab=inc[a]&P[b],ba=inc[b]&P[a];fail[a][b]=ab;fail[b][a]=ba;
    missing.push([a,b,ab,ba]);if(!ab)convenient[a]|=1<<b;if(!ba)convenient[b]|=1<<a;
    if(ab&&ba)sources|=ab|ba;
  }
  for(const reverse of [false,true]){
    const rank=Array(n);let left=full,pos=0;
    while(left){let avail=ids(left,n).filter(v=>!(protectedFrom[v]&left));if(reverse)avail.reverse();const v=avail[0];assert(v!==undefined,"acyclic protection",o);rank[v]=pos++;left&=~(1<<v);}
    for(const choice of [false,true]){
      const T=o.slice();
      for(const[a,b,ab,ba]of missing){const forward=ab&&ba?!choice:!ab&&(!!ba||rank[a]<rank[b]);T[forward?a:b]|=1<<(forward?b:a);}
      for(const[a,b,ab,ba]of missing){
        const f=(T[a]&(1<<b))?a:b,q=f===a?b:a,good=!ab||!ba;
        const inverseWitnesses=ids(fail[q][f],n),unitWitness=inverseWitnesses.find(r=>pc(unprotected[r])<=1);
        if(!good&&unitWitness===undefined)continue;
        const Q=T.slice();for(const[u,v]of missing)if(u===f||v===f){const z=u===f?v:u;if(z!==q){Q[f]&=~(1<<z);Q[z]|=1<<f;}}
        const next=second(Q,f),E=(two[f]|unprotected[f])&~(1<<q);
        assert(Q[f]===(o[f]|1<<q),"one retained first neighbour",{o,f,q});
        assert(!(next&~E),"general retained envelope",{o,f,q,good,unitWitness,next,E});
        assert(pc(next)<=pc(two[f])+pc(unprotected[f])-1,"minus-one count",{o,f,q});
        if(good){counts.goodRetentions++;if(pc(sources)>=4)counts.goodRetentionsWithFourPlusSources++;if(protectedFrom[f])counts.goodRetentionsWithProtectedFarHeads++;}
        else{counts.badRetentionsWithUnitReverseWitness++;if(pc(sources)>=4)counts.badRetentionsWithFourPlusSources++;if(!control)control={out:o,f,q,unitWitness,sourceCount:pc(sources),secondBefore:two[f],secondAfter:next};}
        if(next&~two[f])counts.newSecondHeadsCases++;
      }
    }
  }
}
for(let code=0;code<59049;code++){
  let c=code;const o=Array(5).fill(0);
  for(let a=0;a<5;a++)for(let b=a+1;b<5;b++){const d=c%3;c=Math.floor(c/3);if(d===1)o[a]|=1<<b;if(d===2)o[b]|=1<<a;}
  audit(o);counts.allFiveGraphs++;
}
let seed=0x10502026;function random(){seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;return(seed>>>0)/4294967296;}
for(let sample=0;sample<20000;sample++){
  const n=6+sample%6,density=[.35,.55,.7,.85][sample%4],o=Array(n).fill(0);
  for(let a=0;a<n;a++)for(let b=a+1;b<n;b++)if(random()<density){if(random()<.5)o[a]|=1<<b;else o[b]|=1<<a;}
  audit(o);counts.sampledGraphs++;
}
assert(counts.goodRetentionsWithFourPlusSources>0,"must exercise larger source support");
assert(counts.badRetentionsWithFourPlusSources>0,"must exercise bad retained arcs");
const result={status:"PASS",counts,control,seed:"0x10502026",scope:"Two canonical linear extensions and two bad-edge orientation tie choices per graph; all outgoing added good arcs and all added bad arcs with at least one unit-unprotected inverse witness are tested. No graph is assumed to be an all-deficient minimal counterexample."};
fs.writeFileSync(path.join(__dirname,"audit_general_retention.results.json"),JSON.stringify(result,null,2)+"\n");
console.log(JSON.stringify(result,null,2));
