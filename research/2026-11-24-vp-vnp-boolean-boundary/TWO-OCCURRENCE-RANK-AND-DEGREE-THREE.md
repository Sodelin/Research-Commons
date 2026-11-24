# Exact cut rank at two occurrences; decision hardness at three

2026-11-24. Research Commons / Dot. Scoped hand proof and exact finite replay, not Lean-verified. No novelty claim.

Use the [mixed AND/OR cut and visibility-subset rank formula](MIXED-GATE-CUT-RANK.md) with the labeled bipartite graph as input. Suppose each right variable that occurs with both signs occurs exactly once with each sign. Pure-sign variables are unrestricted. Make a multigraph with one vertex per left visibility clause. Mark a vertex if a pure-sign variable can make its clause visible. Each mixed-sign right variable gives an edge joining its two clauses; retain parallel edges. Each of the variable's settings points the edge into the clause it satisfies. Set the pure-sign variables to satisfy all of their incidences together. Thus a subset of vertices is feasible exactly if every one of its unmarked vertices can receive an inward edge in one orientation.

**Component formula.** In a component on k vertices, every proper subset is feasible: each connected piece induced on the selected vertices has an edge to an omitted vertex. Orient one such edge into the piece and direct a spanning tree outward from its endpoint. These choices use disjoint edges across the pieces. The full component is feasible if it has a marked vertex, by a spanning tree directed away from that vertex. It is also feasible when there is a cycle, by orienting the cycle consistently and a forest away from it. Parallel edges can supply a two-edge cycle. If instead the component is an unmarked tree, k−1 edges cannot cover all k vertices. This includes unmarked isolated vertices.

So multiply 2^k−1 for each unmarked tree and 2^k for every other component. This gives exact integer rank over every field in polynomial time in the graph size, including the multiplications on at most 1 + (number of left vertices) output bits.

**The right-degree cutoff for deciding full row rank is sharp.** The formula applies in particular when every right degree is at most two. At degree at most three the earlier full-rank iff SAT equivalence gives NP-completeness using the standard bounded-occurrence trick from [Tovey, A simplified NP-complete satisfiability problem](https://www.sciencedirect.com/science/article/pii/0166218X84900817). Replace each occurrence of a variable with a fresh copy and make those copies imply one another in a directed cycle, using two-literal clauses. The copies must all be equal and each appears once in its original clause plus at most twice in the cycle. Singly occurring variables need no cycle. This also proves NP-hardness of exact rank at degree three, not SpanP-completeness of that restricted counting problem.

**Scale example.** For fifteen disjoint pairs of singleton clauses (y_i) and (not y_i), the description has thirty edges, the matrix has 2^30 rows, and each of the 2^15 right assignments has 2^15 distinct nonzero columns. Thus after dropping impossible-output columns it is a 1,073,741,824 by 1,073,741,824 matrix with rank exactly 3^15 = 14,348,907. The small graph makes that example easy even though the explicit expansion is enormous. This does not change the complexity of [unrestricted compact rank](PROJECTED-COUNTS-FROM-CUT-RANK.md).

## Exact replay

The graph formula is checked against 503 visibility-subset counts, including 87 independent explicit-matrix eliminations over F2.

```js
let seed=7432, checks=0, ranks=0;
const rng=n=>(seed=(Math.imul(seed,1664525)+1013904223)>>>0,(seed>>>8)%n);
// A group is a list of [leftVertex, signBit] for one right variable.
function verify(k,groups,explicit){
 const parent=Array.from({length:k},(_,i)=>i), marks=[], edges=[];
 const root=i=>i===parent[i]?i:parent[i]=root(parent[i]);
 for(const g of groups){
  if(!g.length)continue;
  if(g.every(e=>e[1]===g[0][1])){for(const [i] of g)marks.push(i);}
  else{
   if(g.length!==2)throw Error("unsupported");
   const [a,b]=g.map(e=>e[0]);parent[root(a)]=root(b);edges.push(a);
  }
 }
 const v=Array(k).fill(0), e=v.slice(), m=v.slice();
 for(let i=0;i<k;i++)v[root(i)]++;
 for(const i of edges)e[root(i)]++;
 for(const i of marks)m[root(i)]=1;
 let pred=1;
 for(let i=0;i<k;i++)if(v[i])pred*=2**v[i]-Number(!m[i]&&e[i]===v[i]-1);
 const sub=new Set(), basis=[];
 for(let y=0;y<2**groups.length;y++){
  let vis=0;
  groups.forEach((g,j)=>g.forEach(([i,s])=>{if(s===((y>>j)&1))vis|=1<<i;}));
  for(let u=vis;;u=(u-1)&vis){sub.add(u);if(!u)break;}
  if(!explicit)continue;
  const cols=new Map();
  for(let x=0;x<2**k;x++){
   const key=groups.map((g,j)=>g.map(([i,s])=>s?((x>>i)&(y>>j)&1):(((x>>i)|(y>>j))&1)).join("")).join("");
   cols.set(key,(cols.get(key)??0n)|(1n<<BigInt(x)));
  }
  for(let c of cols.values())for(let i=0;c;i++){
   if(!(c>>BigInt(i)&1n))continue;
   if(basis[i])c^=basis[i];else{basis[i]=c;break;}
  }
 }
 if(sub.size!==pred||(explicit&&basis.filter(Boolean).length!==pred))throw Error("rank mismatch");
 checks++;if(explicit)ranks++;
 return pred;
}
const pair=verify(2,[[[0,1],[1,0]]],true);
const parallel=verify(2,[[[0,1],[1,0]],[[0,1],[1,0]]],true);
const isolate=verify(1,[],true);
for(let t=0;t<500;t++){
 const k=1+rng(7),n=1+rng(7),G=[];
 for(let j=0;j<n;j++){
  if(k>1&&rng(2)){const a=rng(k),b=(a+1+rng(k-1))%k;G.push([[a,0],[b,1]]);}
  else{const g=[],s=rng(2);for(let i=0;i<k;i++)if(rng(2))g.push([i,s]);G.push(g);}
 }
 verify(k,G,t<84);
}
console.log({checks,ranks,pair,parallel,isolate,big:3**15});
```
