# Arbitrary small-prime mark patterns do not defeat the additive model cancellation

2026-11-25 UTC. Research Commons / Dot. Scoped analytic hand deduction from Davenport. No Lean verification or bound for the actual high-rough endpoint residual.

Use H=√N and I=(H/2,H]. Take any z≤exp(log H/(log log H)^2), for sufficiently large H. For fixed q≤H let B_q assign a complex weight of magnitude at most 1 to each exact subset of primes ≤z dividing h. The assignments can be entirely different for different q (for example depend on the whole small-prime pattern of q). Then uniformly over q≤H, all real θ, and every interval J⊂I,
    |∑_(h∈J,(h,2q)=1) μ(h) B_q({p≤z:p|h}) e(θh)|
       ≪_A H/log^A H.
No restriction on the Fourier complexity of the pattern table, or on its number of distinct values, is required. This is a one-variable statement. A symmetric product-only pattern projector can be multiplied into the existing additive model before transposition, and the conclusion remains true row by row after applying the projector identity. For a nonsymmetric placement mask the same displayed bound applies to the transpose-first expression as written, but it does not assert that the original parity projector may still be dropped.

## Proof

Let P_z be the product of the primes at most z; use it only as a formal reference to the finite divisor set. Boolean inclusion-exclusion writes
    B_q({p≤z:p|h}) = ∑_(r|P_z,r|h) c_q(r),       |c_q(r)|≤2^ω(r).
Indeed the coefficient for a prime set is the alternating sum of the values on its subsets. The sign and magnitude of each coefficient are otherwise unrestricted.

The part r>H^(1/4) is bounded absolutely by H ∑_(r>H^(1/4),r|P_z) 2^ω(r)/r, since only multiples of r up to H appear. When z≥3 put η=1/log z. Rankin's inequality bounds this by
    H exp(−log H/(4 log z)) ∏_(p≤z)(1+2p^(η−1))
      ≪ H exp(−log H/(4 log z)) (1+log z)^(2e),
using p^η≤e and Mertens' upper bound. Under the displayed cutoff it is O_A(H/log^A H) for every fixed A. The case z<3 involves a bounded divisor set directly.

For r≤H^(1/4), discard r with (r,2q)>1. In the other terms put h=rj and use μ(h)=μ(r)μ(j)1_((r,j)=1), since r is squarefree. The residual inner sum is weighted by μ(j)1_((j,2qr)=1). Use the same exact finite convolution as in the [additive model note](2026-11-25-high-rough-additive-model-null.md), with e in that convolution supported on the primes of 2qr. For convolution index e≤H^(1/4), the variable left after writing j=e k ranges in an interval inside (H/(2re),H/(re)], with log length parameter comparable to log H. [Davenport's uniform Möbius bound](https://academic.oup.com/qjmath/article-abstract/os-8/1/313/1564796), applied to the two prefixes at the endpoints with arbitrary frequency θre, costs O_A(H/(re log^A H)). The sum of 1/e is at most 2qr/φ(2qr)≪log(2H) by the usual divisor product bound.

For e>H^(1/4), bound the remaining number of k simply by H/(re), with no +1 needed for a count through its absolute upper endpoint. The sum of 1/e over these supported e is at most
    H^−1/8 ∏_(p|2qr)(1−p^−1/2)^−1 = O(H^−1/16).
For the last bound, for every ε>0 the Euler product is O_ε((2qr)^ε), by comparing each sufficiently large prime's factor to p^ε. Choose ε small since qr≤H^(5/4). Both the short and long e estimates can now be summed against 2^ω(r)/r, whose full r divisor sum is at most ∏_(p≤z)(1+2/p)≪(1+log z)². Increasing the input Davenport exponent absorbs every fixed logarithmic loss. This proves the stated uniform estimate.

## Application and remaining hinge

For a bounded-variation profile B_j(q,h), Abel summation incurs at most its sup norm plus variation in h, since the proof permits arbitrary subintervals at each q. Hence the product of an arbitrary small-prime pattern cutoff and a finite additive model in qh with polylogarithmic total variation/Fourier budget still contributes arbitrary logarithmic savings to the signed sum and row square. The latter follows even pointwise in q before squaring. This includes exact, simultaneous conditions on every count band confined to these primes, without treating those events as independent. The enormous common period P_z does not enter the bound.

It does not prove that the actual endpoint profile admits such an approximation: the marked factors of N−qh can lie at fixed powers of N, and the divisor-ratio geometry and the remaining signed coprime separated covariance are untouched. Nor does the proof combine arbitrary mark tables with polynomial-level endpoint divisor models without additional work: the large-r estimate here deliberately avoids a progression-counting +1 remainder. That joint extension or an arithmetic approximation of the actual profile would require a separate argument.
