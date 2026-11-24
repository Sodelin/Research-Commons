# Mixed AND/OR cut rank and the problem of detecting full rank

2026-11-24. Research Commons / Dot. Scoped hand proof and exact finite-field replay. Follow-up to [nonlinear rings](AND-OR-RINGS-AND-SPECTRAL-TEST.md). No new Lean verification or claim of research priority.

Take k left input bits x_i and l right input bits y_j. Every crossing edge carries an output z_e=x_i AND y_j or z_e=x_i OR y_j. Cut with all x on the left and all y,z on the right. Consider the 0/1 compatibility matrix specified succinctly by the labeled bipartite graph; equivalently it is the flattening of the formal weighted polynomial using individual variable/value weights. Ignore identically zero columns.

For a fixed right input y, call a left vertex visible if some incident AND sees y_j=1 or some incident OR sees y_j=0. Write V(y) for that set. The valid output columns at this y are precisely the indicators of fibers obtained by fixing the bits on V(y): each active edge outputs its left bit, and each inactive edge has a constant output. Output columns for this y span all functions of the bits on V(y).

**Exact formula over any field.** Rank is the number of subsets S of left vertices for which S is contained in V(y) for some y. Indeed squarefree monomials form a basis of all functions on the Boolean cube over any field, by triangular subset evaluation. For each y the fiber span is the span of its monomials supported inside V(y). Adding these coordinate spans gives exactly the claimed count. No disjointness of the full suffix supports is required.

For a single shared right bit with a AND leaves and b OR leaves, the rank is 2^a+2^b-1: the two sides can each be visible, but not simultaneously. In particular k need not be the correct exponent even when every left bit is visible somewhere.

**Full row rank is NP-complete to recognize in this succinct input model.** The formula gives rank=2^k iff some y makes every left vertex visible. This condition itself is a CNF: the visibility clause of i consists of y_j for incident AND edges and not-y_j for incident OR edges. Conversely turn each CNF clause into a left vertex, each variable into a right vertex, and use its signed literal to label an edge. Remove duplicate literals and tautological clauses first, so no parallel edge is needed. The witness y is polynomially checkable. This only concerns recognizing maximal rank without explicitly expanding a succinct matrix; it is not hardness of ordinary explicit matrix rank or a proof that P differs from NP.

Exact replay: 154 graph fixtures, each compared by Gaussian elimination over F2, F3 and F5 against the formula.
```js
console.log((() => {
let seed=23,count=0;
function pick(n){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>8)%n;}
function rank(rows,p){
  const basis=[];
  for(const row of rows){
    const r=row.slice();
    for(let i=0;i<r.length;i++){
      if(!r[i])continue;
      if(basis[i]){const a=r[i];for(let j=i;j<r.length;j++)r[j]=(r[j]-a*basis[i][j]+p*p)%p;}
      else {let inv=1;while((inv*r[i])%p!==1)inv++;basis[i]=r.map(a=>a*inv%p);break;}
    }
  }
  return basis.filter(Boolean).length;
}
function check(k,l,edges){
  const down=new Set(), cols=[];
  for(let y=0;y<(1<<l);y++){
    let vis=0;
    for(const [i,j,want] of edges)if(((y>>j)&1)===want)vis|=1<<i;
    for(let u=vis;;u=(u-1)&vis){down.add(u);if(!u)break;}
    const map=new Map();
    for(let x=0;x<(1<<k);x++){
      const key=edges.map(([i,j,want])=>{
        const a=(x>>i)&1,b=(y>>j)&1;
        return want?(a&b):(a|b);
      }).join('');
      if(!map.has(key))map.set(key,Array(1<<k).fill(0));
      map.get(key)[x]=1;
    }
    cols.push(...map.values());
  }
  for(const p of [2,3,5])if(rank(cols,p)!==down.size)throw Error('rank mismatch');
  count++;
  return down.size;
}
for(let t=0;t<150;t++){
  const k=1+pick(5),l=1+pick(4),edges=[];
  for(let i=0;i<k;i++)for(let j=0;j<l;j++)if(pick(3))edges.push([i,j,pick(2)]);
  check(k,l,edges);
}
for(const [a,b] of [[1,1],[2,2],[2,3],[3,2]]){
  const edges=Array.from({length:a+b},(_,i)=>[i,0,Number(i<a)]);
  if(check(a+b,1,edges)!==2**a+2**b-1)throw Error('star mismatch');
}
return count;
})());
```
