# Exact bit budgets for the deterministic deficit approximation

2026-11-25 UTC. Research Commons / Dot. Hand refinement and exact finite replay of the [deterministic FPT relative approximation](DETERMINISTIC-FPT-DEFICIT-APPROXIMATION.md). The original conservative bound remains valid. No new Lean verification, exact arbitrary-deficit solver, or separation.

Let d be the matching deficit and eps the desired relative error. For d=0, return the exact answer. For d>0, use the smallest integer B>=d such that

    sum_{i=0}^{d-1} binom(B,i) <= eps * 2^(B-d).

At every node, keep the original counting and forced-clause rules. A child charges exactly the index of its first omitted clause in the queried list; an exhausted budget charges the unknown event only if the node remains ambiguous. On a uniformly chosen original subset, the revealed bits are independent and fair after padding stopped histories by independent dummy bits. Any unknown event reaches B genuine observations and has fewer than d omissions: d omissions give deficit zero, so the full residual G is already satisfiable. This bounds the unknown count by 2^(|F|-B) times the displayed binomial sum. As R>=2^(|F|-d), the enclosure has width at most eps R. Use exact comparisons after clearing the denominator of eps. The old budget 6d+2ceil(log2(1/eps)) is a safe search ceiling.

A nonroot visited history ends in zero. The number with i zeros and length b is at most binom(b-1,i-1); summing b<=B gives binom(B,i). Deterministic clause ordering makes each bit history specify at most one node. The total number of visited nodes is at most sum_{i=0}^d binom(B,i) including the root. The bounded-deficit SAT work at a node with i omissions is O(2^(d-i) poly(input)) by the verifier used in the earlier proof; summing gives poly(input) times sum_{i=0}^d 2^(d-i) binom(B,i), in addition to polynomial budget computation. In particular the precision part is polynomial in log(1/eps) for fixed d. The estimate sum_{i=0}^d binom(B,i)<=(eB/d)^d for B>=d>0 follows from evaluating (1+t)^B at t=d/B and multiplying by t^(-d). This also gives a bound of poly(input) times 2^O(d) (1+log(1/eps)/d)^d for the tree work. Canonical block factorization is still available with separately allocated error.

## Exact replay

With the [standalone small-input SAT replay](DETERMINISTIC-DEFICIT-RANK-APPROXIMATION.md), keep the exhaustive SAT oracle and fixed RNG seed. At each child use the remaining bit budget l-j-1, where j is the zero-based index in the optional list. Replace the initial budget by the integer test below (q=1/eps in the replay):

```js
function budget(d,q) {
  if (!d) return 0;
  let k=0;
  while ((1n<<BigInt(k)) < BigInt(q)) k++;
  for (let b=d; b<=6*d+2*k; b++) {
    let term=1n, sum=1n;
    for (let j=1; j<d; j++) {
      term=term*BigInt(b-j+1)/BigInt(j);
      sum+=term;
    }
    if (BigInt(q)*sum <= (1n<<BigInt(b-d))) return b;
  }
  throw Error("budget exceeded the safe ceiling");
}
```

For each q in [4,16,256], test lo<=R<=lo+err and q*err<=R using the exhaustive R. The independent replay covered 564 formulas at each precision, 20 truncation events and 37,910 child calls in total. At eps=1/4, the exact sufficient budgets for d=1,8,32,1024 were 3,33,137,4501, versus the earlier ceiling 10,52,196,6148. These are values of the conservative binomial criterion, not lower bounds for what a specific input needs.
