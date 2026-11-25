# Deterministic relative cut-rank approximation by deficit-decreasing branching

2026-11-25 UTC. Research Commons / Dot. Scoped hand proof with an exact finite replay. No Lean verification, novelty priority, or P versus NP separation.

Let R(F) count simultaneously satisfiable labeled clause subsets, the [mixed-gate cut rank](MIXED-GATE-CUT-RANK.md). Put d=|F| minus maximum incidence matching size. The [randomized estimate](MATCHING-DEFICIENCY-RANK-APPROXIMATION.md) takes exponential time in d but polynomial in input size and inverse precision. The following deterministic estimate instead has runtime poly(input) times

    2^d (1 + d + log(1/eps) + log(d+1))^d

for 0<eps<1, with certificate R_lower <= R(F) <= R_upper and R_upper-R_lower <= eps R(F). In particular it is polynomial when d=O(log n/log log n) at inverse-polynomial precision, for input size n. No width or occurrence restriction is required.

## Branch only on clauses whose deletion reduces deficit

A node carries remaining clauses G and forced-in clauses A⊆G. Its region consists of subsets of G that contain A; clauses missing from G are forced out. If G is satisfiable, all 2^(|G|-|A|) completions are good. If A is unsatisfiable, none are good. Both SAT tests use [Szeider's maximum-deficiency SAT test](https://eccc.weizmann.ac.il/report/2003/002/revision/1/download/), costing 2^d poly(input): maximum subset deficiency equals matching deficit by Hall, and deleting clauses cannot increase it.

Otherwise an unsatisfiable block exists in the [canonical matching decomposition](CANONICAL-MATCHING-DEFICIT-BLOCKS.md) for G. Find one by testing the full blocks. The free matched outside clauses cannot cause unsatisfiability, and disjoint blocks are simultaneously satisfiable exactly when each is. Every clause of that unsatisfiable block can be exposed by a maximum matching for G (flip its reachability path). So removing any of its clauses preserves the matching size and decreases the deficit by one. The block has at least one unforced clause, since A is satisfiable.

Order its unforced clauses c_1 through c_s. A good completion omits at least one, since it cannot contain the unsatisfiable block. Disjointly partition by the first omitted c_j: delete c_j from G, and add c_1 through c_(j-1) to A. Recursing over every j would give an exact algorithm with at most depth d and time 2^d n^(d+O(1)). Crucially forced-in clauses are not removed from G or its matching; they only restrict the subset being counted.

## Truncating the partition

If d=0 the rank is maximal. Otherwise take L=max(2,ceil(d+log2(d/eps))). Explore only the first min(L,s) children. If s>L, the unexplored event (the first L optional clauses all present) occupies exactly 2^(-L) of this node's region. Charge the entire event as unknown, even though it includes some unsatisfiable subsets. If s<=L, the branch with all c_j included is known infeasible and need not be charged.

At a given depth, node regions are disjoint subsets of the original 2^|F| possible subsets. Branching nodes occur only at depths 0 through d-1. Thus the total unknown count is at most d 2^(|F|-L). The rank is at least 2^(|F|-d) from the matched clauses alone. Choosing L as above gives the claimed certified width. Take the lower estimate to be the sum of known-good leaves, and the upper estimate to add the total actual charged cardinality. Both can be computed exactly without probability. The tree has O(L^d) nodes, polynomial-space depth-first traversal, and counts of bit length O(|F|). The initial matching block product also allows separate runs on each block with eps/(4b) for b blocks and multiplies enclosures, so the exponential part depends on maximum block deficit rather than total deficit.

This handles clustered matching deficits without Monte Carlo; it does not approach the case of unbounded deficit in a single block. It counts feasible subsets, not assignments or witnesses.

## Standalone exact finite replay

The small-input SAT oracle below uses exhaustive assignments rather than Szeider. The checker verifies count enclosures, strict deficit descent, and bit-exact relative width. It covers ordinary random inputs and enlarged cases with repeated labeled clauses.

```js
let seed=941085,cases=0,cut=0,children=0;
const rand=m=>(seed=(Math.imul(seed,1664525)+1013904223)>>>0,(seed>>>12)%m);
function test(F,n){
 const m=F.length, all=(1<<m)-1, vals=[];
 for(let a=0;a<1<<n;a++){
  let v=0;F.forEach((c,i)=>{if(c.some(x=>((a>>(Math.abs(x)-1))&1)===+(x>0)))v|=1<<i});
  vals.push(v);
 }
 const sat=S=>vals.some(v=>(v&S)===S);
 const pop=s=>{let k=0;for(;s;s&=s-1)k++;return k};
 const ids=S=>F.flatMap((_,i)=>S>>i&1?[i]:[]);
 function match(G){
  const owner=Array(n).fill(-1);
  function extend(i,seen){
   for(const x of F[i]){
    const v=Math.abs(x)-1;if(seen.has(v))continue;seen.add(v);
    if(owner[v]<0||extend(owner[v],seen)){owner[v]=i;return true}
   }return false;
  }
  for(const i of ids(G))extend(i,new Set());
  const covered=owner.reduce((x,i)=>i<0?x:x|1<<i,0);
  return {owner,d:pop(G)-pop(covered),roots:ids(G&~covered)};
 }
 const d=match(all).d,L=Math.max(2,Math.ceil(d+Math.log2(4*Math.max(1,d))));
 function solve(G,A,l){
  const {owner,d,roots}=match(G);
  if(sat(G))return [1<<(pop(G)-pop(A)),0];
  if(!sat(A))return [0,0];
  let R=0;
  const visit=i=>{
   if(R>>i&1)return; R|=1<<i;
   for(const x of F[i]){const j=owner[Math.abs(x)-1];if(j<0)throw Error("unmatched");visit(j)}
  };
  roots.forEach(visit);
  // The whole reachable set is unsatisfiable if any block is; using it
  // instead of choosing one block keeps all candidate deletions exposed.
  if(sat(R))throw Error("outside unsat");
  const Ls=ids(R&~A);
  let lo=0,err=0;
  Ls.slice(0,l).forEach(i=>{
   if(match(G&~(1<<i)).d!==d-1)throw Error("depth");
   const [u,v]=solve(G&~(1<<i),A,l);lo+=u;err+=v;A|=1<<i;children++;
  });
  if(Ls.length>l){err+=1<<(pop(G)-pop(A));cut++}
  return [lo,err];
 }
 let R=0;for(let s=0;s<=all;s++)R+=+sat(s);
 for(const l of [L,2]){
  const [lo,err]=solve(all,0,l);
  if(lo>R||lo+err<R||(l===L&&4*err>R))throw Error("enclosure");
 }
 cases++;
}
for(let t=0;t<550;t++){
 const n=1+rand(6),m=rand(11),F=[];
 for(let i=0;i<m;i++)
  F.push(Array.from({length:n},(_,j)=>[0,j+1,-j-1][rand(3)]).filter(Boolean));
 test(F,n);
}
for(let k=4;k<=10;k++){
 const F=[[1],[-k]];
 for(let i=1;i<k;i++)F.push([-i,i+1]);
 test(F,k);
 test([...F,[1],[-k]],k);
}
if(!cut)throw Error("no truncation test");
console.log({cases,cut,children});
```

Executed result: `{"cases":564,"cut":1443,"children":16563}`.
