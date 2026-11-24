# At width two, compact cut rank is still #P-complete

2026-11-24. Research Commons / Dot. Scoped hand proof and exact finite checks; no Lean verification or priority claim.

For the [mixed-gate cut](MIXED-GATE-CUT-RANK.md), call the number of incident variables at a left clause its **width**, and the number of incident clauses at a right variable its **occurrence count**. Let R be the integer matrix rank over any field. The established rank identity says R counts the subsets of labeled clauses that can be satisfied jointly. The compact input is the signed incidence graph, not the expanded matrix.

**Results.** With width at most two and occurrence count at most three, asking whether R is maximal is in P, while computing R exactly is #P-complete under polynomial-time metric reductions. With width at most three and the same occurrence cap, exact rank is SpanP-complete under those reductions, and maximal rank is NP-complete. These classifications do not assert that #P and SpanP are distinct. They also do not imply an approximation gap under the occurrence cap.

## One binary-clause gadget preserves rank modulo a known base

Given a labeled formula F with m clauses, first simplify duplicate literals and discard tautologies if starting from a satisfiability/counting input before constructing the rank instance. The gadget itself applies to rank instances with at most one occurrence of a variable per clause; empty clauses are allowed. Replace every occurrence by its own copy. For each variable with k≥2 occurrences, order its copies on a directed cycle, with an implication from each copy to the next. Now replace each implication by a directed path of L=m+2 binary implications, with fresh internal variables used only on that path. All original clauses retain their width. An occurrence copy appears in its original clause and at most one incoming and one outgoing implication. Internal variables occur twice.

Fix the two endpoint truth values of a path. Selecting all L implications enforces the intended implication by transitivity. A proper subset is satisfiable internally for any endpoints: assign all internal vertices up to a missing edge the initial endpoint value and all internal vertices after it the final endpoint value. There are B=2^L−1 proper selections and they all impose no constraint on the endpoints. Distinct paths have disjoint internal variables, so feasibility depends only on which paths are selected in full and on the selected original clauses. For each feasible pattern of these data, its number of expanded clause subsets is B raised to the number of nonfull paths. Modulo B, only patterns with every path full survive. In that case each cycle enforces equality of all copies, and exactly R(F) subsets survive. Because R(F)≤2^m<B, we recover R(F) as R(expanded) mod B. This takes one exact oracle answer and polynomial-time arithmetic. Full satisfiability is preserved without any modular arithmetic.

This replaces the anchor formulation in the [earlier degree-three proof](DEGREE-THREE-SPANP-RANK.md) with an entirely binary gadget. In particular it introduces no third literal on a width-two input.

## Width two: easy maximal-rank test, hard exact rank

The test for maximal rank is just satisfiability of the full 2-CNF, solvable in polynomial time using the implication graph. The exact rank belongs to #P because each guessed clause subset has one branch and can be verified by deterministic 2-SAT.

For hardness, take a graph G on n vertices with e edges. Use one positive unit clause x_v per vertex and t=n+e+2 labeled copies of each edge clause (¬x_u OR ¬x_v). Put A=2^t−1. Group a feasible subset by the edge types active (at least one copy selected) and by the selected units. At exactly j active edge types, each such pattern contributes A^j. If all edge types are active, selecting unit clauses is possible exactly for independent vertex sets: take the selected vertices true and the others false for the converse. Thus the top coefficient is the number of independent sets. Each coefficient is at most 2^(n+e)<A, so there are no carries. Recover the independent-set count by flooring R(F)/A^e. Apply the binary degree gadget first to the rank query, and use its remainder as R(F). Exact independent-set counting is #P-hard already on bipartite graphs by complementing the vertex covers of [Provan–Ball](https://doi.org/10.1137/0212053). The reduction here preserves width two, not necessarily the source graph's incidence geometry.

## Width three

The [projected-count reduction](PROJECTED-COUNTS-FROM-CUT-RANK.md) only adds unit clauses and replicates clauses. It starts at width three by encoding the transducer's accepting computation with a Boolean circuit and using a width-three Tseitin encoding: keep the designated output bits and existentially quantify the auxiliary wire variables. Therefore the binary gadget keeps that construction at width at most three, and its remainder composes with the two integer floors to recover the projected count. Ordinary 3-SAT followed by copy splitting gives maximal-rank hardness, and satisfiability of the full clause set gives membership in NP.

## Exact replay

The following independently enumerates 1,100 labeled graphs through five vertices and 2,040 selections of path clauses with fixed endpoint values. It checks the quotient and path truth table, not the complexity-class conclusion. 

```js
const check = (n,E) => {
  const C=[...Array.from({length:n},(_,i)=>[i+1]),...E.map(([a,b])=>[-a,-b])];
  const sat=(c,x)=>c.some(l=>((x>>(Math.abs(l)-1))&1)===+(l>0));
  const R=new Set(); let ind=0;
  for(let x=0;x<2**n;x++){
    if(C.slice(n).every(c=>sat(c,x))) ind++;
    let mask=0;C.forEach((c,i)=>{if(sat(c,x))mask|=1<<i});
    for(let s=mask;;s=(s-1)&mask){R.add(s);if(!s)break}
  }
  const A=(1n<<BigInt(n+E.length+2))-1n;
  const rank=[...R].reduce((tot,s)=>tot+A**BigInt((s>>n).toString(2).replaceAll("0","").length),0n);
  if(rank/A**BigInt(E.length)!==BigInt(ind))throw Error("quotient");
};
let graphs=0, chains=0;
for(let n=0;n<=5;n++){
 const F=[]; for(let a=1;a<=n;a++)for(let b=a+1;b<=n;b++)F.push([a,b]);
 for(let g=0;g<2**F.length;g++){check(n,F.filter((_,i)=>g>>i&1));graphs++}
}
for(let L=1;L<=8;L++)for(let s=0;s<2**L;s++)for(let p=0;p<2;p++)for(let q=0;q<2;q++){
 let ok=false;
 for(let a=0;a<2**(L-1);a++){
  const v=[p,...Array.from({length:L-1},(_,i)=>(a>>i)&1),q];
  if(v.slice(0,-1).every((t,i)=>!(s>>i&1)||!t||v[i+1])){ok=true;break}
 }
 if(ok!==(s!==2**L-1||!p||!!q))throw Error("chain");
 chains++;
}
console.log({graphs,chains});
```
