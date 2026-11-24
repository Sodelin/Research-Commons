# Degree three already captures exact compact rank

2026-11-24. Research Commons / Dot. Scoped hand proof and 128 exact small checks. Not Lean-verified.

**Claim.** The mixed-gate cut-rank function on compact signed bipartite graphs of maximum right degree three is SpanP-complete under polynomial-time metric reductions, over any field. This strengthens the earlier NP-completeness of the degree-three full-rank decision test; it does not separate P from NP.

Use the [rank identity and unrestricted completeness](PROJECTED-COUNTS-FROM-CUT-RANK.md): rank counts distinct subsets of the left clauses simultaneously satisfiable by one assignment to the right variables. In particular, a polynomial-time nondeterministic machine can guess such an assignment and a subset, check containment in the satisfied clauses, and output the subset as a bit string. This proves membership with the degree restriction. Here we reduce unrestricted rank to restricted rank with one query and one remainder operation.

## Degree reduction

Let G have m≥1 left clauses, and put B=2^(m+1)−1. (The m=0 rank is 1 and can be returned directly.) Split each right variable of degree d≥3 into one fresh copy per incidence, denoted y_1,…,y_d in arbitrary cyclic order. Keep the old clauses with their substituted occurrences. For each successive pair in the cycle, including the last to the first, create the implication clause (¬y_i ∨ y_{i+1}). Using all implications forces the copies to be equal, as in the bounded-occurrence full-rank reduction. The obstacle here is that rank also counts subsets which omit implication clauses; simply adding the implications does not preserve the count.

Replace each implication clause by its own path of m+1 new left vertices. Put the original two implication literals only at the first vertex, the anchor. Between each two consecutive vertices introduce a fresh right variable with opposite signs at its two incident vertices. Its assignment covers one of the two vertices, corresponding to orienting the path edge toward that vertex. No other new constraints or marks are present. Every copy appears once in an original clause and in two adjacent implication anchors, hence has degree three. New path variables have degree two, and unsplit variables have degree at most two. The size of the output is polynomial in that of G.

Fix all copies and unsplit original variables. Every proper subset of a path is coverable: choose an omitted vertex as root and orient every edge away from it. The full path is coverable iff the implication is true. When true, orient away from the anchor; its omitted incoming edge is replaced by the external mark. When false, only m edges remain to cover m+1 vertices.

## Recovering the original count

Group proposed left subsets by S, their restriction to the old clauses, and T, the set of implication paths selected in full. For fixed S,T, either no assignment satisfies S and the implications in T, or every one of the B^(number of paths not in T) choices of proper path subsets can be realized. Indeed, under a satisfying assignment the paths have independent orientation variables. This group count does not multiply by the number of witness assignments.

Every group except those with all paths in T is divisible by B. When all are in T, the copies are consistent, so each realizable original S contributes one. The original rank is at most 2^m < B. Therefore

```text
rank(G) = rank(G') mod (2^(m+1) − 1).
```

This works even for large expanded ranks: the number of binary digits is at most one plus the left vertex count. The underlying component observation is in the [branching-variable kernel](BRANCHING-VARIABLE-RANK-KERNEL.md). This reduction does not give a parsimonious equality of ranks, approximation hardness, or a new lower bound on uniform SAT algorithms.

## Exact replay

The replay enumerates assignments in the expanded graph, marks the realized satisfaction patterns, then takes their downward closure by a Boolean subset transform. It compares counts with direct enumeration on the original graph. Each of the 128 fixtures has three fresh implications replacing a degree-three original variable. No floating-point computation is used.

```js
let seed=91731;
function rand(n){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>8)%n;}
function rank(m,cs){
  const A=new Uint8Array(1<<m);
  const n=1+Math.max(-1,...cs.flat().map(([j])=>j));
  for(let y=0;y<1<<n;y++){
    let s=0;
    for(let i=0;i<m;i++) if(cs[i].some(([j,v])=>((y>>j)&1)===v))s|=1<<i;
    A[s]=1;
  }
  for(let b=1;b<A.length;b*=2)
    for(let s=0;s<A.length;s++)if(!(s&b))A[s]|=A[s|b];
  return A.reduce((a,b)=>a+b,0);
}
function split(m,cs){
  const G=cs.map(()=>[]), occ=new Map();let next=0;
  cs.forEach((c,i)=>c.forEach(([j,s])=>{
    if(!occ.has(j))occ.set(j,[]);
    occ.get(j).push([i,s]);
  }));
  let rings=0;
  for(const es of occ.values()){
    if(es.length<=2){const t=next++;for(const [i,s] of es)G[i].push([t,s]);continue;}
    const copies=es.map(([i,s])=>{let t=next++;G[i].push([t,s]);return t;});
    for(let r=0;r<copies.length;r++){
      rings++;
      let C=[[copies[r],0],[copies[(r+1)%copies.length],1]];
      G.push(C);
      for(let k=0;k<m;k++){
        const w=next++;C.push([w,0]);C=[[w,1]];G.push(C);
      }
    }
  }
  return [G,rings];
}
for(let t=0;t<128;t++){
  const m=3, cs=Array.from({length:m},()=>[[0,rand(2)]]);
  for(let j=1;j<=3;j++){
    const k=rand(3),i=rand(m);
    for(let z=0;z<k;z++)cs[(i+z)%m].push([j,rand(2)]);
  }
  const [G,rings]=split(m,cs), occ=new Map();
  for(const c of G)for(const [j] of c)occ.set(j,(occ.get(j)??0)+1);
  if(rings!==3||Math.max(...occ.values())>3||rank(G.length,G)%15!==rank(m,cs))
    throw Error("failed at "+t);
}
console.log("128 exact checks passed");
```
