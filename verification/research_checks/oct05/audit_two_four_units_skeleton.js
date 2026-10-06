'use strict';
// Auxiliary finite combinatorial checks, not a graph counterexample search.
// No neighborhood or arc-minimality hypotheses are certified by this script.
const assert = require('assert/strict');
const fs = require('fs');
const path = require('path');
const pairs = [];
for (let x=0;x<4;x++) for(let y=x+1;y<4;y++) pairs.push([x,y]);
const allowed = [];
for(let mask=0;mask<64;mask++) {
  const adj=Array.from({length:4},()=>Array(4).fill(false));
  for(let k=0;k<6;k++) if(mask>>k&1) {const [x,y]=pairs[k];adj[x][y]=adj[y][x]=true;}
  const edges=pairs.filter(([x,y])=>adj[x][y]);
  if(!edges.every(([x,y])=>[0,1,2,3].some(z=>z!==x&&z!==y&&!adj[z][x]&&!adj[z][y]))) continue;
  const degree=adj.map(row=>row.filter(Boolean).length).sort().join('');
  const classes={'0000':'empty','0011':'single_edge','1111':'two_disjoint_edges','0112':'unit_path','0222':'triangle'};
  assert(classes[degree],`Unexpected eligible unit graph ${mask}: ${degree}`);
  allowed.push({mask,edges,type:classes[degree]});
}
const counts={};for(const g of allowed) counts[g.type]=(counts[g.type]||0)+1;
assert.deepEqual(counts,{empty:1,single_edge:6,unit_path:12,triangle:4,two_disjoint_edges:3});

// Forced matching configuration: u=0,a=1,b=2,c=3,d=4,
// hc=a, u->a,c->b, and missing ab,cd,uc.
const sources=[0,1,2,3,4], units=[1,2,3,4];
const missingBase=[[1,2],[3,4],[0,3]];
const config=[];
for (const ha of [0,3,4,5,6]) for(const hb of [0,3,4,5,6])
for(const hd of [0,1,2,5,6]) {
  const h={1:ha,2:hb,3:1,4:hd};
  const base=[[0,1],[3,2],[1,hb],[2,ha],[3,hd],[4,1]];
  const valid=(arcs,missing=missingBase)=> {
    const out=Array.from({length:7},()=>new Set());
    for(const [x,y] of arcs) {
      if(x===y||missing.some(([a,b])=>a===x&&b===y||a===y&&b===x)) return false;
      if(out[y].has(x)) return false;
      out[x].add(y);
    }
    for(const x of units) {
      const y=h[x]; if(out[x].has(y))return false;
      if([...out[x]].some(z=>out[z].has(y)))return false;
    }
    if(out[0].has(2)||[...out[0]].some(z=>out[z].has(2)))return false;
    return true;
  };
  if(!valid(base))continue;
  // cd is BAD: find allowed witnesses among u,a,b with forced unit heads.
  const witness=[];
  for(const [x,y] of [[1,2],[0,1],[0,2]]) {
    for(const [headX,headY] of [[3,4],[4,3]]) {
      if(x!==0&&h[x]!==headX||y!==0&&h[y]!==headY)continue;
      // x points to head of y and vice versa; the tail is missing.
      const arcs=base.concat([[x,headY],[y,headX]]);
      if(valid(arcs,missingBase.concat([[x,y]])))witness.push({tail:[x,y],heads:[headX,headY]});
    }
  }
  if(!witness.length)continue;
  assert.equal(ha,4);assert.equal(hb,3);
  assert(witness.every(w=>w.tail[0]===1&&w.tail[1]===2));
  assert.notEqual(hd,0);
  config.push({ha,hb,hc:1,hd,witness});
}
assert(config.length>0);
const result={claim:'Auxiliary unit witness graph enumeration and forced matching heads only',
  oriented_graph_counterexample:false,all_deficient_graph_search:false,
  unit_graph_counts:counts,unit_graphs:allowed,
  forced_matching_configurations:config};
const destination=path.join(__dirname,'audit_two_four_units_skeleton.results.json');
fs.writeFileSync(destination,JSON.stringify(result,null,2));
console.log(JSON.stringify({passed:true,unit_graph_counts:counts,matching_configurations:config.length,
  allowed_hd:[...new Set(config.map(x=>x.hd))],results_file:destination}));
