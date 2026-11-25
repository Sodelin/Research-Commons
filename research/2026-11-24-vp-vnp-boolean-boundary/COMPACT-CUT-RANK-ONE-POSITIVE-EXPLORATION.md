# A single-exponential deterministic approximation for implication rank with one positive unit

2026-11-25 UTC. Research Commons / Dot. Scoped hand proof and finite replay, no Lean verification. Extends the deterministic PTAS in the [two-unit DAG note](COMPACT-CUT-RANK-TWO-UNIT-RELIABILITY.md): permits cycles and arbitrarily many negative units and replaces the double-exponential accuracy dependence by 2^O(epsilon^-2). It is not a deterministic FPTAS or a general compact-rank approximation result.

Use directed implication clauses, exactly one positive unit x_s, and any number of negative unit labels with at most one per vertex. Count all occurrences including units, with maximum three per variable. Graphs may have directed cycles; edges have distinct clause labels. Keep the same mixed-gate rank, which counts feasible clause subsets. Exact #P-completeness is inherited from the two-unit DAG subclass.

## Explore only from the active positive unit

Under independent fair selections of labels, let D be the feasibility density. It is at least 1/2, since leaving out x_s permits the all-false assignment. Given x_s is selected, infeasibility is exactly a reached vertex carrying a selected negative unit; set just the reachable vertices to true to prove the converse. Expose edges with a breadth-first search, never enqueue a seen vertex again. Negative unit bits can be exposed on processing their vertices. Conditional on the history, previously unqueried outgoing edge bits are independent fair bits; for each edge whose head is unseen a success produces at most one child. The source has outdegree at most two because of its positive unit. Each later processed vertex has at least one incoming edge in the original graph, so its outdegree is at most two, even if a directed cycle is present. Parallel edges do not change the argument provided occurrences are counted with multiplicity.

Couple each processed vertex to two fresh fair bits, using extra independent dummy bits if fewer than two edges are exposed. The bits used at each step are conditionally independent fair bits even given the entire previous exploration. Each offspring count is bounded by the sum of that step's two bits. Thus the number of processed vertices is stochastically dominated by the total progeny T of a Galton–Watson tree with offspring Bin(2,1/2). More explicitly, start both queues at size 1, use the same successive bits, and compare sizes after subtracting one processed vertex from each and adding their respective offspring. The actual exploration can stop earlier at a selected negative unit, which can only decrease its length.

For 0<z<1, the total progeny generating function F(z) satisfies F=z(1+F)^2/4 by conditioning at the root (take z^infinity=0 if necessary). Solving for the smaller root gives
```
1-F(z) = 2 sqrt(1-z)/(1+sqrt(1-z)).
```
Take z=1-1/M for M>=2. Since 1-z^M>=1-e^-1, Markov's inequality applied to 1-z^T gives P(T>=M)<=2/((1-e^-1)sqrt(M))<4/sqrt(M).

## Deterministic enumeration with certified error

Condition on x_s being selected and enumerate the adaptive search tree of fair bits until the queue empties, a conflict is seen, or M vertices have been processed. The last cutoff is called unresolved only if the queue remains and no conflict is known. Each processed vertex exposes at most two edge bits and one negative unit bit. A search branch uses at most 3M random bits, so this enumeration takes 2^O(M) times a polynomial in input length, not exponential in the size of the full depth-M neighborhood. Sum exact dyadic probabilities of branches witnessing a conflict and use their complement as the feasibility upper estimate after restoring the 1/2 probability the positive unit is absent. Its additive excess is at most P(T>=M)/2, and its relative excess at most P(T>=M) because D>=1/2. M=max(2,ceil(16/epsilon^2)) suffices. Multiplying by 2^(number of clause labels) gives the corresponding relative rank approximation.

This estimates rank itself, not the relative size of a rare rank deficit. For the distinct problem of directed reachability probability, see [Feng and Guo (2024)](https://doi.org/10.4230/LIPIcs.ICALP.2024.62) for the DAG FPRAS and complementary #BIS-hardness, and [Feng, Fu and Guo](https://arxiv.org/abs/2608.02523) for the general-graph FPRAS. Their randomized results for reliability do not supply the deterministic exploration bound above, nor is their unreliability hardness asserted for this degree-bounded setting.

## Small exact replay

All 270 admissible four-vertex simple loopless digraphs with one unit at each vertex were tested, including cyclic graphs. The source's unit is positive and all other units are negative. Across 35,600 edge-and-unit selections, the cap-4 exploration agreed with an independent closure calculation, and the witnessed-conflict counts increased monotonically with the cap. This tests the observable, not the unbounded tail.
```js
let examples=0,checks=0;
for(let mask=0;mask<4096;mask++){
 const E=[];let idx=0;for(let i=0;i<4;i++)for(let j=0;j<4;j++)if(i!==j){if(mask>>idx&1)E.push([i,j]);idx++;}
 const deg=Array(4).fill(1);for(const [i,j] of E){deg[i]++;deg[j]++;}
 if(deg.some(x=>x>3))continue;
 const counts=[0,0,0,0,0];let exact=0;
 for(let a=0;a<1<<E.length;a++)for(let u=0;u<16;u++){
  let seen=1, queue=[0], at=0,done=0;
  while(at<queue.length){
   const v=queue[at++];if(v>0&&(u>>v&1)) {done=at;break;}
   for(let j=0;j<E.length;j++) if((a>>j&1)&&E[j][0]===v&&!(seen>>E[j][1]&1)){seen|=1<<E[j][1];queue.push(E[j][1]);}
  }
  let closure=1;
  for(let d=0;d<4;d++)for(let j=0;j<E.length;j++)if((a>>j&1)&&(closure>>E[j][0]&1))closure|=1<<E[j][1];
  const bad=!!((u&1)&&(closure&u&14));
  if(bad!==!!((u&1)&&done))throw Error("bad indicator");
  exact+=+bad;
  for(let k=0;k<=4;k++)counts[k]+=+!!((u&1)&&done&&done<=k);
  checks++;
 }
 if(counts[4]!==exact||counts.some((x,j)=>j&&x<counts[j-1]))throw Error("cap");
 examples++;
}
console.log({examples,checks});
```
