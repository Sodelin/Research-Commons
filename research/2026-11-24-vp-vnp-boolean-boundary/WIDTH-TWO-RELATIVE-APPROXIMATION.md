# Width-two cut rank: relative approximation is hard, additive density estimation is easy

2026-11-24. Research Commons / Dot and background research. Hand proof with exact finite checks; no Lean verification or priority claim.

For the [mixed-gate cut rank](MIXED-GATE-CUT-RANK.md) the compact input is a signed clause-variable incidence graph and the rank is the number R of labeled clause subsets jointly satisfiable. At width two, [maximal rank is decidable by 2-SAT, while exact rank is #P-complete even with at most three occurrences per variable](WIDTH-TWO-EXACT-RANK.md).

Here, still at width two but **without the occurrence cap**, a relative factor-two estimate would imply P=NP if deterministic, or RP=NP if randomized with bounded error. On these hard examples, full rank is trivially false. This strengthens the [earlier width-three approximation gap](COMPACT-RANK-APPROXIMATION-GAP.md). It does not establish the bounded-occurrence approximation result.

## Reduction from Independent Set

Take a graph G with n≥1 vertices and m edges, and a size threshold 1≤k≤n. Independent Set is the complement-graph version of [Karp’s CLIQUE problem](https://www2.seas.gwu.edu/~simhaweb/champalg/tsp/papers/KarpOriginal.pdf). Give each vertex v L=n+5 labeled copies of the unit clause x_v, and each edge uv t=Ln+3 labeled copies of the binary clause ¬x_u∨¬x_v. Put W=2^L−1 and B=2^t. This explicit compact incidence graph has polynomial size, even with all copies supplied.

If S is the set of vertices for which at least one unit copy is selected, there are W^|S| choices of those unit copies. An edge with both endpoints in S has no selectable copies. Every other edge has B choices, independently: assigning exactly S true certifies simultaneous feasibility. If e(S) is the number of edges within S, the exact identity is

    R/B^m = Σ_(S⊆V) W^|S| / B^e(S).

The total contribution of nonindependent S is ≤(1+W)^n/B=1/8. If α(G)≥k, a single independent S contributes at least W^k. If α(G)<k, all independent terms together contribute at most 2^n W^(k−1), so the total is strictly below W^k/8 (use W=2^(n+5)−1 and k≥1). Consequently an estimate in [R/2,2R] separates the cases using the threshold B^m W^k/2. All normalizations and comparisons have polynomial bit length. For randomized estimation, amplify each decision and use the standard vertex-deletion self-reduction to find an independent k-set; verifying the returned set makes this one-sided. If G has an edge, the full clause set always includes a contradicted negative edge clause when all units are selected. Thus maximal rank supplies no useful decision bit on these instances.

## Additive estimation of the rank fraction

If a width-two input has M labeled clauses, test independent uniform subsets using 2-SAT. The success fraction estimates R/2^M to additive ε with failure probability δ using O(ε⁻² log(1/δ)) samples, by Hoeffding's inequality. This guarantee can say almost nothing about a tiny relative rank. Even n disjoint pairs of opposite units have fraction (3/4)^n, because exactly three of the four subsets of each pair are feasible. This tractable additive estimate is compatible with relative hardness.

## Finite exact check

The replay checks 5,405 gap comparisons on all 1,099 labeled simple graphs with one to five vertices. It tests the weighted identity's consequences, not the complexity conclusion or the incidence-to-matrix identity.

```js
let graphs=0, tests=0;
for(let n=1;n<=5;n++){
 const U=[];for(let i=0;i<n;i++)for(let j=i+1;j<n;j++)U.push((1<<i)|(1<<j));
 const W=(1n<<BigInt(n+5))-1n,B=1n<<BigInt(n*(n+5)+3);
 for(let g=0;g<1<<U.length;g++){
   const E=U.filter((_,i)=>g>>i&1),m=E.length;
   let R=0n,alpha=0;
   for(let s=0;s<1<<n;s++){
     let k=0;for(let x=s;x;x&=x-1)k++;
     const e=E.filter(z=>(s&z)===z).length;
     if(e===0)alpha=Math.max(alpha,k);
     R+=W**BigInt(k)*B**BigInt(m-e);
   }
   for(let k=1;k<=n;k++){
     const Q=W**BigInt(k)*B**BigInt(m);
     if(alpha>=k?R<Q:8n*R>=Q)throw Error('gap');
     tests++;
   }
   graphs++;
 }
}
console.log({graphs,tests});
```
