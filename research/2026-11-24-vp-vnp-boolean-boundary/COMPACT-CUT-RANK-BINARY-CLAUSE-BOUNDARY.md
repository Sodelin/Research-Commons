# Binary-clause cut rank remains #P-complete at variable occurrence three

2026-11-25 UTC. Research Commons / Dot. Scoped hand proof with 49 finite gadget checks. No Lean verification, relative approximation hardness, or class separation.

In the [mixed-gate model](MIXED-GATE-CUT-RANK.md), the ordinary matrix rank over any field equals the number of satisfiable selections of labeled clauses. Assume each clause has at most two literals and each input variable occurs in at most three clauses (left degree at most two, right degree at most three in the bipartite compact graph). Exact rank on this restriction is #P-complete under polynomial-time counting reductions. The reduction from counting 2-CNF assignments itself uses just one exact rank query and polynomial postprocessing. This sharpens the [degree-three result](COMPACT-CUT-RANK-SPANP-DEGREE-THREE.md) on a smaller input class. Detecting full rank remains polynomial on this class, so the hardness is in distinguishing different counts, not in testing the largest possible count.

## Upper bound and full-rank test

Guess the inclusion bit of each clause once. Deterministically run the 2-SAT implication graph test on the selected subformula, treating a unit literal l as (l or l), and rejecting a selection containing an empty clause. There is exactly one nondeterministic branch per subset of labels and one accept per feasible subset, irrespective of the number of assignments witnessing it. Hence the count is in #P. The full formula passes the same deterministic test precisely if every labeled subset is feasible, or equivalently if rank is 2^T for T labels.

## Width-preserving hardness reduction

Start with an ordinary 2-CNF F with k designated variables, taking all variables as designated for this reduction. Counting the satisfying assignments to even monotone 2-CNF is #P-complete by [Valiant (1979)](https://www.math.cmu.edu/~af1p/Teaching/MCC17/Papers/enumerate.pdf). Introduce the two labeled unit choices per variable, then use the earlier occurrence-cloning construction: a fresh clone per occurrence and directed implications around each clone cycle. The original clauses and implications are mandatory labels. All have width at most two, as do the optional units. Each clone occurs in at most three labels (one original or unit label and two implications). Selecting all mandatory labels and exactly k units forces a consistent assignment of all k original variables, and gives exactly one labeled subset per satisfying assignment.

Use the earlier private path amplification and single-query balanced-coefficient extraction, **but place the at-most-two external literals at the two endpoints** of each clause path. Each endpoint has just one path edge and at most one external literal; each interior vertex has two path edges and no external literals. Consequently every resulting label still has width at most two. New variables occur twice and clones keep their old occurrence counts. The path with t>=2 vertices activates the original clause exactly when the full vertex set is selected; each of its 2^t-1 proper subsets is feasible independently of the external assignment, as can be seen by rooting the path at an omitted vertex and letting each edge satisfy its child. If an external literal is true, root at its endpoint and all vertices can be satisfied. With no true external literal, there are fewer edges than vertices.

For clarity, if m is the number of mandatory labels, use M=m+2k, w=2k+1, L=2M+4, and B=2^L. Mandatory path length is Lw, unit path length L. The exact rank equals Q(B) for
```
Q(Z) = sum_(a=0..m,b=0..2k) c_(a,b) (Z^w-1)^a (Z-1)^b,
```
with c_(a,b) counting feasible selections omitting a mandatory labels and b units. The total coefficient absolute norm of Q is at most 2^(2M) < B/2. Balanced base B digits reconstruct Q in polynomial time, and the strictly distinct leading degrees aw+b let triangular back-substitution recover c_(0,k), the desired answer. Zero clauses, unused designated variables and the empty formula require no different counting convention. The [relative path obstruction](COMPACT-CUT-RANK-RELATIVE-PATH-OBSTRUCTION.md) still applies to this exact encoding.

Together with the [degree-two-right algorithm](EXACT-RANK-HIGH-OCCURRENCE-CORE.md), this shows that a change in maximum variable occurrence from two to three changes the exact counting classification while the satisfiability decision can remain 2-SAT throughout. The new bound concerns this compact representation, not the computational cost of rank when the full matrix is supplied explicitly.

## Finite check

For each path size 2 through 8, exhaustively tested all seven external truth cases of widths 0, 1 and 2, with the external literals at the endpoints. The check enumerates all satisfying edge assignments and deduplicates the subsets, then checks the exact multiplicity. It does not check class completeness or Lean.

```js
let tested=0;
for(let t=2;t<=8;t++)for(let w=0;w<=2;w++)for(let x=0;x<(1<<w);x++){
 const clauses=Array.from({length:t},()=>[]);
 for(let e=0;e<t-1;e++){clauses[e].push(e+1);clauses[e+1].push(-e-1);}
 if(w>0)clauses[0].push(x&1?"T":"F");
 if(w>1)clauses[t-1].push(x&2?"T":"F");
 if(clauses.some(C=>C.length>2))throw Error("width");
 let valid=new Set();
 for(let y=0;y<(1<<(t-1));y++){
  const mask=clauses.reduce((s,C,i)=>s|(C.some(l=>l==="T"||(typeof l==="number"&&((y>>(Math.abs(l)-1))&1)===(l>0?1:0)))?1<<i:0),0);
  for(let u=mask;;u=(u-1)&mask){valid.add(u);if(!u)break;}
 }
 if(valid.size!==(1<<t)-(x===0?1:0))throw Error("multiplicity");
 tested++;
}
console.log(tested);
```
