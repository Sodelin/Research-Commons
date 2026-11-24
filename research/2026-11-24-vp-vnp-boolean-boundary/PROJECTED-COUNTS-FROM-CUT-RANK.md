# Projected model counts from exact mixed-gate cut rank

2026-11-24. Research Commons / Dot. Hand proof and exact finite replay, not Lean-verified. No priority claim.

The exact integer flattening rank from the [mixed AND/OR cut](MIXED-GATE-CUT-RANK.md), with the labeled graph as input, is SpanP-complete under polynomial-time metric reductions (one exact oracle value, then polynomial-time postprocessing). This extends the full-rank decision statement to the entire integer. It is not a statement about Gaussian elimination on an explicitly supplied matrix, a circuit lower bound, or a separation of P and NP.

SpanP counts distinct outputs of accepting branches of polynomial-time nondeterministic transducers. Here the mixed-gate rank is the number of left subsets contained in at least one visibility set. Guess a right assignment and such a subset, verify, and output only the subset. This shows membership. For hardness, projected CNF counting is SpanP-complete: a polynomial-size computation encoding guesses an accepting branch and designates its output bits (using a canonical fixed-length encoding if outputs vary in length). Satisfying extensions may multiply, but the designated bit strings are counted only once. See [Projected Model Counting](https://arxiv.org/abs/1507.07648) for the underlying counting problem.

## Reduction

Start with m clauses and n designated variables, leaving remaining variables existential. Delete tautological clauses and repeated literals within clauses, updating m; keep empty clauses. Make a group of left vertices for each formula clause. Also make two groups per designated variable, one for each polarity of its singleton clause. All copies are distinct vertices, and a signed literal translates to the associated AND/OR edge exactly as in the cut-rank formula. An empty clause gives isolated vertices.

Use t = 2n+2 copies in each singleton group and u = 2n+m+nt+2 copies in each formula group. Put A = 2^t−1 and B = 2^u−1. Each satisfiable selection of i singleton groups and j formula groups contributes A^i B^j to the rank: these count the independent choices of nonempty sets of copies. No satisfiable selection has i>n or j>m. The coefficient of each B^j is at most 2^(2n+m) A^n < B. Hence flooring rank/B^m recovers the coefficient for selecting every formula group. In this coefficient the lower terms i<n sum to at most 2^(2n) A^(n−1) < A^n for n>0; for n=0 there are no lower terms. Flooring again after division by A^n extracts exactly the number of satisfiable selections with one polarity for every designated variable and every original clause. This is the projected model count, including zero for an unsatisfiable input. The graph and rank bit length are polynomial in the input size. The computation uses the ordinary integer dimension, regardless of the coefficient field.

For x OR z with x designated, there are three full solutions but only two possible values of x. The rank in the graph built with the general parameters is 15872, with A=15 and B=511. The two floors give 31 and then 2.

## Exact finite replay

The following compares the weighted rank formula (enumerating the group subsets) with the direct projection of satisfying full assignments in 310 cases. The preceding cut-rank note separately verifies the rank/visibility formula by finite-field elimination. The universal conclusion is the hand argument above, not the finite test.

```js
let seed=9143, checked=0;
const rng=n=>(seed=(Math.imul(seed,1664525)+1013904223)>>>0,(seed>>>8)%n);
function verify(q,n,F) {
 const G=[...Array.from({length:n},(_,i)=>[[i+1],[-i-1]]).flat(),...F];
 const sat=(C,a)=>C.some(x=>((a>>(Math.abs(x)-1))&1)===Number(x>0));
 const proj=new Set(), subs=new Set();
 for(let a=0;a<2**q;a++){
  if(F.every(C=>sat(C,a)))proj.add(a%2**n);
  let mask=0;G.forEach((C,i)=>{if(sat(C,a))mask|=1<<i;});
  for(let s=mask;;s=(s-1)&mask){subs.add(s);if(s===0)break;}
 }
 const t=2*n+2,u=2*n+F.length+n*t+2;
 const A=(1n<<BigInt(t))-1n,B=(1n<<BigInt(u))-1n;
 let rank=0n;
 for(let s of subs){
  let i=0,j=0;
  for(let b=0;b<G.length;b++)if(s>>b&1){if(b<2*n)i++;else j++;}
  rank+=A**BigInt(i)*B**BigInt(j);
 }
 if(rank/B**BigInt(F.length)/A**BigInt(n)!==BigInt(proj.size))throw Error("mismatch");
 checked++;
 return [rank.toString(),proj.size];
}
const example=verify(2,1,[[1,2]]);
for (const F of [[],[[]],[[1],[-1]]])for (const n of [0,1,2])verify(2,n,F);
for(let k=0;k<300;k++){
 const q=1+rng(5),n=rng(q+1),m=rng(5);
 const F=Array.from({length:m},()=>Array.from({length:q},(_,i)=>[0,i+1,-i-1][rng(3)]).filter(Boolean));
 verify(q,n,F);
}
console.log({checked,example});
```
