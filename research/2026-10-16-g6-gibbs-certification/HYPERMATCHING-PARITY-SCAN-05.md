# Parity-scan upper bound for the constructed hypermatching family
Date: 2026-10-16. Prepared by dot for Nolan.
Status: elementary hand corollary; independently checked at statement/proof level by the reviewer of HYPERMATCHING-INDEPENDENT-REVIEW-04. No execution, Lean verification or novelty claim. Separate from the unchanged lower-bound candidate.

Use exactly the family and parameter t=4epsilon/sqrt(m), n=qm, q>=3, in [the reviewed lower-bound candidate](https://github.com/Sodelin/Research-Commons/blob/baacfd78289f1b1b6c922eb172d5e32c206cdef3/research/2026-10-16-g6-gibbs-certification/HYPERMATCHING-CANDIDATE-03.md). The promise here is KNOWN uniform null versus any of those signed q-block alternatives, with known q and t. This is not an upper bound for arbitrary two-unknown Gibbs states.

Measure N independent copies in the computational basis. For every q-element subset S of [n], compute the empirical mean of the parity product of its coordinates. Reject uniformity if any absolute empirical mean exceeds t/2.

Under the null every such mean has expectation zero. Under an alternative each planted block e has expectation s_e t. For a mean of N independent variables in [-1,1], Hoeffding gives
  Pr(|empirical mean - true mean| >= t/2) <= 2 exp(-N t^2/8).
There are B=binom(n,q) tested subsets. By a union bound, taking
  N >= (8/t^2) log(2B/delta)
makes every empirical mean accurate to less than t/2 simultaneously with probability at least1-delta. On that event the test accepts the null and rejects every constructed alternative. A tie at t/2 can be handled either way, since the success event uses strict estimation error.

This uses N TOTAL copies of the single unknown source. A second uniformly mixed reference need not be queried. Computational cost for direct enumeration is O(N q binom(n,q)) elementary parity operations, plus counters; streaming memory is O(binom(n,q)) counters. For FIXED q and constant error this gives O_q(n log n/epsilon^2) samples and polynomial enumeration time. It is not an efficient-all-k claim.

Together with the reviewed lower bound, the restricted uniform-versus-hypermatching experiment has Theta_q(n log n/epsilon^2) constant-error copy complexity for sufficiently large n and the stated coefficient/temperature admission. The lower holds even for collective measurements; this upper uses only computational-basis measurements. The matching rate belongs to this hard family, not to general P1. The general two-unknown, noncommuting k-local Gibbs minimax question remains OPEN.
