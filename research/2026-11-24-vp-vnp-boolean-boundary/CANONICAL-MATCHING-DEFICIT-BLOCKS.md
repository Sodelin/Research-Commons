# Canonical deficit blocks for exact and approximate compact cut rank

2026-11-24. Research Commons / Dot and background research. Hand proof and exact finite checks; no Lean verification or priority claim.

Use the [mixed-gate rank identity](MIXED-GATE-CUT-RANK.md): the integer rank R counts the labeled clause subsets of F that can be simultaneously satisfied. The [matching approximation](MATCHING-DEFICIENCY-RANK-APPROXIMATION.md) is controlled by the total matching deficit. Here that deficit splits canonically into independent blocks. Arbitrarily large total deficit can still permit polynomial-time exact rank, including on connected incidence graphs.

## Decomposition

Choose a maximum matching M in the clause-to-variable incidence graph. From unmatched clauses, traverse clause-to-incident-variable arcs and variable-to-matched-clause arcs. Let B be the reachable clauses. Every variable reached is matched: reaching an unmatched one gives an augmenting path. One can omit a clause's own matched arc when traveling out, since that arc can only return immediately to the same clause. Define blocks B_i by the connected components of the incidence subgraph on B and its variables, allowing singleton empty clauses as blocks.

Each reachable variable is matched to a reachable clause in its own block. Every clause outside B has a matched variable outside all block neighborhoods (otherwise the arc from that variable places the clause in B). Each block's variables are disjoint from those of the other blocks. For any selected labeled subset S, feasibility is therefore equivalent to feasibility of S∩B_i in each block: first combine block assignments on disjoint variable sets, then set each distinct outside matched variable to satisfy its own selected outside clause. No block clause involves these outside variables. Hence

    R(F) = 2^(|F\B|) prod_i R(B_i).

If B_i contains d_i unmatched roots, then its restricted matching covers all neighbor variables and exactly |B_i|−d_i clauses, so its maximum deficiency is d_i. A connected component built in this manner contains a root since every reachable clause has a witness path.

## Why the split is canonical

A clause belongs to B exactly when it can be left unmatched by *some* maximum matching. A path from an unmatched root to a reachable clause alternates outside and inside M and has even length ending in a matching edge. Flipping along that path makes the end clause unmatched without reducing matching size. Conversely, suppose a clause is matched by M but unmatched by another maximum matching M'. In the symmetric-difference component starting at that clause, the first edge is in M and the edges alternate. The path cannot have more edges of M than M', because then M' would have an augmenting path. It therefore has even length and ends at a clause unmatched by M. Reverse it to find the required directed path. This also handles a clause already unmatched by M by a path of length zero. Thus the reachable clause set, the connected blocks, and their deficits are independent of the maximum matching.

## Consequences for rank

When d_i=1, every proper subset of B_i is satisfiable. In fact every clause in the block is reachable from its unique root, and flipping to any omitted clause leaves a matching covering all other clauses. Decide satisfiability of the full block using [bounded-deficiency SAT](https://eccc.weizmann.ac.il/report/2003/002/) at parameter one. Its factor is 2^|B_i| when satisfiable and 2^|B_i|−1 otherwise. Hence exact rank takes polynomial time whenever all blocks have one root, with no bound on their count or on clause width. For example, (x), (not x), (y), (not y), (x OR y OR z) have connected incidence, two contradictory blocks and one free clause; the rank is 3·3·2=18. A chain of contradictory unit pairs joined by clauses with private new matched variables gives unbounded total deficit and one-root blocks.

For more general blocks, independently run the prior relative estimator with tolerance eps/(4b) and error probability delta/b, where b is the number of blocks. With probability at least 1−delta each estimate meets its bound; multiplying them and the exact power of two yields relative error at most eps for 0<eps≤1 (use (1+x)^b≤exp(bx) and Bernoulli's lower bound). The runtime is exponential only in max_i d_i, with polynomial overhead in input size, 1/eps and log(1/delta). This applies even where the total deficit is large; it does not resolve general degree-three approximation.

## Independent finite replay

Checks 1,301 small formulas by assignment and clause-subset enumeration, including the connected rank-18 example. It separately tests the exposure characterization by removing each clause and computing the matching size, compares two matching orders, and checks every proper subset of each one-root block. The replay checks the structural identities, not the running time of the imported SAT algorithm.

```js
let seed=811023,checked=0,multi=0,oneRoot=0;
const rnd=m=>(seed=(Math.imul(seed,1664525)+1013904223)>>>0,(seed>>>11)%m);
function matching(F,n,reverse){
 const mv=Array(n).fill(-1), mc=Array(F.length).fill(-1);
 function augment(i,seen){
  for(const x of F[i]){
   const v=Math.abs(x)-1;if(seen.has(v))continue;seen.add(v);
   if(mv[v]<0||augment(mv[v],seen)){mv[v]=i;mc[i]=v;return true;}
  }return false;
 }
 for(let j=0;j<F.length;j++)augment(reverse?F.length-1-j:j,new Set());
 return {mc,mv};
}
function partition(F,n,reverse){
 const {mc,mv}=matching(F,n,reverse),roots=mc.flatMap((v,i)=>v<0?[i]:[]);
 const R=new Set(roots),q=[...roots];
 for(let a=0;a<q.length;a++)for(const x of F[q[a]]){
   const j=mv[Math.abs(x)-1];if(j<0)throw Error("augmentable");
   if(!R.has(j)){R.add(j);q.push(j);}
 }
 const B=[],V=F.map(c=>new Set(c.map(Math.abs)));
 const component=new Set(R);
 while(component.size){
   const i=component.values().next().value,b=[i];component.delete(i);
   for(let k=0;k<b.length;k++)for(const j of component){
     if([...V[b[k]]].some(v=>V[j].has(v))){b.push(j);component.delete(j);}
   }
   B.push(b.sort((a,b)=>a-b));
 }
 return {B:B.sort((a,b)=>a[0]-b[0]),roots,def:roots.length};
}
function check(F,n){
 const {B,roots,def}=partition(F,n,false);
 if(JSON.stringify(B)!==JSON.stringify(partition(F,n,true).B))throw Error("matching dependence");
 const possible=F.flatMap((_,i)=>F.length-1-partition(F.filter((_,j)=>i!==j),n,false).def===F.length-def?[i]:[]);
 if(possible.join(",")!==B.flat().sort((a,b)=>a-b).join(","))throw Error("exposable mismatch");
 const m=F.length,feas=new Uint8Array(1<<m);
 for(let a=0;a<1<<n;a++){
   let b=0;F.forEach((c,i)=>{if(c.some(x=>((a>>(Math.abs(x)-1))&1)===+(x>0)))b|=1<<i;});
   for(let s=b;;s=(s-1)&b){feas[s]=1;if(!s)break;}
 }
 const masks=B.map(b=>b.reduce((s,i)=>s|(1<<i),0));
 for(let s=0;s<1<<m;s++)if(!!feas[s]!==masks.every(b=>feas[b&s]))throw Error("factorization");
 for(const b of masks)if(roots.filter(i=>b>>i&1).length===1)
  for(let s=(b-1)&b;;s=(s-1)&b){if(!feas[s])throw Error("proper subset");if(!s)break;}
 const R=feas.reduce((a,b)=>a+b,0);
 checked++;multi+=+(B.length>1);oneRoot+=+B.every(b=>b.filter(i=>roots.includes(i)).length===1);
 return R;
}
if(check([[1],[-1],[2],[-2],[1,2,3]],3)!==18)throw Error("example");
for(let t=0;t<1300;t++){
 const n=1+rnd(6),m=rnd(9),F=[];
 for(let i=0;i<m;i++)F.push(Array.from({length:n},(_,j)=>[0,j+1,-j-1][rnd(3)]).filter(Boolean));
 check(F,n);
}
console.log({checked,multi,oneRoot});
```
