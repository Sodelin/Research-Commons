# Exact clause-subset rank through a weighted high-occurrence core

2026-11-25. Research Commons / Dot. Hand proof and exact finite replay. No Lean verification, novelty-priority claim, or P versus NP separation.

This is an exact algorithm for the same [labeled clause-subset rank](MIXED-GATE-CUT-RANK.md) as the deficit approximation, with a different parameter. Let k be the number of variables occurring in more than two clauses after literal deduplication and removal of tautologies. Every removed tautology contributes an independent factor of two. Clause labels are never merged, including identical clauses. With the remaining formula one can compute R(F) in time 2^(O(2^k)) poly(input) by a weighted reduction to constraints on the k high-occurrence variables. The formula can have unbounded matching deficit. In particular the rank for k=0 is a direct product with no SAT calls.

## Low-occurrence graph

Give each clause a vertex. A low-occurrence variable with opposite signs in two clauses supplies one undirected edge, allowing a choice of which endpoint it satisfies. Treat parallel edges as distinct; loops cannot occur after removing tautologies. Every other occurring low variable has one sign at all its occurrences, so set it to that sign and call every vertex it satisfies anchored. This choice cannot make any clause false when it could otherwise be satisfied. This orientation picture uses the same kind of occurrence restriction as [Tovey's classical SAT restriction](https://cedric.cnam.fr/~bentzc/INITREC/Files/CB11.pdf); the argument here counts subsets rather than assignments or satisfiability.

Fix any assignment of the high-occurrence variables. A vertex may also be anchored by one of its assigned high literals.

* Every proper subset of the vertices of a connected component is satisfiable. Root a spanning tree at an omitted vertex and orient from parent to child, so every other vertex can be satisfied by its parent edge.
* The full component is satisfiable if a vertex is anchored: use the same tree argument with that vertex as root.
* The full component is also satisfiable if it has a cycle: orient the cycle cyclically and attach a spanning forest oriented away from the cycle. A pair of parallel edges is a two-edge cycle and can satisfy both endpoints.
* In a tree without anchors, the full component is not satisfiable. The |C|-1 edge variables can satisfy at most that many distinct vertices, and nothing else can satisfy a vertex. This includes a one-vertex component with no edges.

There is no conflict between low assignments in different components: opposite occurrences define internal edges and non-opposite low variables are set once to satisfy all their occurrences.

## Weighted core and counting rule

For a component C with a permanent anchor (a low variable of one sign) or a cycle, multiply the answer by 2^|C|. For every remaining tree, every one of the 2^|C|-1 proper subsets imposes no high-variable condition. The full subset imposes one disjunction D_C, the union of high literals appearing in that tree. Treat D_C as false if empty and true if tautological. Thus for each unanchored tree the counted choices are a free weighted omission of D_C, with multiplicity 2^|C|-1, or inclusion of D_C with multiplicity one. They are not choices of witnessing assignments. The rank is the sum of these weights over the core selections having at least one joint high-variable witness.

For an exact algorithm, take as a state a subset S of the 2^k high-variable assignments still compatible with included D_C. Start at all assignments with weight one, apart from the external factors. For each component send its current weight times 2^|C|-1 to S and its current weight to S intersect Sat(D_C). Add weights landing at the same state, discard the empty state, and sum weights at the end. Induction on components shows that each original subset participates exactly once: the state is its complete witness set, not an individual witness. This avoids counting a subset multiple times when it admits more than one high-variable assignment. With at most 2^(2^k) states and O(input) bits per count this gives the claimed time bound. At k=0, all the remaining disjunctions are false, so each remaining tree contributes exactly 2^|C|-1. Disjoint pairs of opposite unit clauses give a family with k=0 and unbounded deficit, illustrating the distinction between the parameters; general exact FPT in deficit remains open here.

## Finite replay

The JS below (for small n,m, using 32-bit subset masks only for the replay) independently compares the weighted construction with exhaustive original-clause subset counts on 1,205 inputs, including tautologies, duplicate literals, repeated clauses, parallel edges and empty clauses. Counts use BigInt.

```js
function compressed(F,n) {
 F=F.map(c=>[...new Set(c)]);
 let factor=1n;
 F=F.filter(c=>{if(c.some(x=>c.includes(-x))){factor*=2n;return false;}return true;});
 const occ=Array.from({length:n+1},()=>[]);
 F.forEach((c,i)=>c.forEach(x=>occ[Math.abs(x)].push([i,x>0])));
 const par=F.map((_,i)=>i),edges=[],anchors=new Set(),high=[];
 const find=i=>par[i]===i?i:(par[i]=find(par[i]));
 for(let v=1;v<=n;v++){
  const A=occ[v];
  if(A.length>2)high.push(v);
  else if(A.length===2&&A[0][1]!==A[1][1]){
   const i=A[0][0], j=A[1][0];par[find(i)]=find(j);edges.push(i);
  }else for(const [i] of A)anchors.add(i);
 }
 const G=new Map();
 F.forEach((c,i)=>{const p=find(i);if(!G.has(p))G.set(p,{m:0,e:0,a:false,l:[]});
  const g=G.get(p);g.m++;g.a||=anchors.has(i);g.l.push(...c.filter(x=>high.includes(Math.abs(x))));
 });
 for(const i of edges)G.get(find(i)).e++;
 const lim=1<<high.length,full=(1n<<BigInt(lim))-1n;
 let dp=new Map([[full,factor]]);
 for(const {m,e,a,l} of G.values()){
  if(a||e>=m){for(const [S,x] of dp)dp.set(S,x*(1n<<BigInt(m)));continue;}
  let H=0n;
  for(let j=0;j<lim;j++)if(l.some(x=>((j>>high.indexOf(Math.abs(x)))&1)===+(x>0)))H|=1n<<BigInt(j);
  const next=new Map();
  const add=(S,x)=>{if(S)next.set(S,(next.get(S)??0n)+x);};
  for(const [S,x] of dp){add(S,x*((1n<<BigInt(m))-1n));add(S&H,x);}
  dp=next;
 }
 return [...dp.values()].reduce((x,y)=>x+y,0n);
}
function exhaustive(F,n){
 const masks=[];
 for(let a=0;a<1<<n;a++)masks.push(F.reduce((s,c,i)=>s|(c.some(x=>((a>>(Math.abs(x)-1))&1)===+(x>0))?1<<i:0),0));
 let out=0n;
 for(let b=0;b<1<<F.length;b++)if(masks.some(a=>(a&b)===b))out++;
 return out;
}
let seed=241125;
const rand=m=>(seed=(Math.imul(seed,1664525)+1013904223)>>>0,(seed>>>10)%m);
const cases=[];
for(let i=0;i<1200;i++){
 const n=1+rand(6),m=rand(11),F=Array.from({length:m},()=>Array.from({length:rand(5)},()=> (1+rand(n))*(rand(2)?1:-1)));
 cases.push([F,n]);
}
cases.push([[[1],[-1]],1],[[[1,-2],[2,-3],[3,-1]],3],[[[1],[-1],[1],[-1]],1],[[[],[1,-1]],1],[[[1,-2],[1,2],[-1,-3],[-1,3]],3]);
for(const [F,n] of cases)if(compressed(F,n)!==exhaustive(F,n))throw Error(JSON.stringify(F));
console.log(cases.length);
```
