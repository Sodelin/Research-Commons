# The high-rough Goldbach moment can discard rough cofactors on either side

2026-11-25 UTC. Research Commons / Dot. Scoped hand proof using the classical Selberg upper sieve, not Lean verified. This uses the exact actual weights and retains the signed problem on the remaining pairs.

Keep the [strict high-rough Type II moment](2026-11-24-high-rough-coprime-off-diagonal.md) at N=2^k with H=sqrt(N). Let q, h, h+j be in the original box, j>0, and g denote the original grouped weight, so |g|≪log N and nonzero g has every endpoint prime factor greater than N^(1/10). For any 5≤Z≤H, let T_i(Z) require Z-roughness on one specified cofactor h (i=1) or h+j (i=2), and T_12(Z) require it on both; Z-rough here means no prime divisor ≤Z. Then the total absolute weighted mass over the indicated pairs is

    T_i(Z) ≪ H³/(log Z) + H^(9/4),
    T_12(Z) ≪ H³/(log Z)² + H^(9/4).

In particular for any Z tending to infinity, no matter how slowly, only the pairs with a prime factor ≤Z in **each** cofactor are needed for the signed bulk estimate. This is not a restriction on either endpoint N−qh or N−q(h+j), which were already much rougher.

## Upper sieve at fixed q,j

For p≥5 forbid the roots of the two endpoint forms N−qh and N−q(h+j). For p≤Z also forbid the root of each selected cofactor form h and/or h+j. In the nonexceptional case there are 2+e(p) distinct roots, where e(p) is the number of selected cofactor forms if p≤Z and is zero otherwise. The only exceptional primes divide

    q j (N−qj)(N+qj).

Indeed when p does not divide q the endpoint roots are N/q and N/q−j, and the cofactor roots are 0 and −j. Collision of the two endpoint roots or of the two cofactor roots needs p|j. The crossed collisions need N±qj divisible by p; parallel collisions need p|N, which is excluded at p≥5. In the box with j≤H/2, N−qj≥N/2 and N+qj≤3N/2, so these are always positive. Use the same squarefree Chinese-remainder count and weights of magnitude≤1 as in the [sparse gap estimate](2026-11-24-high-rough-sparse-gap-removal.md), with R=H^(1/10). Here nu(p)≤4, and the summed remainder O_eta(R^(2+eta)) holds because nu([d,e])≤4^omega([d,e]); zero forbidden-residue primes may just be omitted.

That sieve's normalized Euler product argument applies with the upper bound 4 in place of 2. More explicitly take a fixed sufficiently small c>0 so that the probability-model mean of log(d) over primes p≤R^c is at most log(R)/2 by the classical bound for sum_(p≤x) log(p)/p. Then the truncated sieve denominator is at least half the product over these primes. Mertens and the convergent O(p^(-2)) comparison with (1−1/p)^(2+e(p)) give the nonexceptional inverse product ≪(log H)^(-2)(log Z)^(-a), where a=1 or 2 is the number of cofactor forms; log min(Z,R^c) is comparable to log Z for Z≤H. Dropping all forbidden roots at the exceptional primes costs at most a constant times

    f(q)^4 f(j)^4 f(N−qj)^4 f(N+qj)^4,   f(m)=m/phi(m).

Indeed the inverse baseline factor ratio at each exception is at most (1−1/p)^(-4)(1+O(p^(-2))). Omitting 2 and 3 changes only absolute constants. Multiply the sieve bound by O((log N)²) to majorize the actual product of weights. For small fixed eta the error per q,j is O(H^(1/4)) after the log weights.

## Uniform mean of the four singular factors

For fixed s>0 expand f(m)^s=sum_(d|m) a_s(d) with nonnegative squarefree-supported coefficients, a_s(p)=(1−1/p)^(-s)−1=O_s(1/p). Both sum_d a_s(d)/d<infinity and a_s(d)≪_(s,eta) d^(-1+eta) follow directly. For m≤2H² the part d>H is O_s(H^(-1/2)) uniformly, by the latter bound with small eta and the divisor bound.

For m=N±qj, any eligible d is odd because q,j can be restricted to their actual support or the 2-factor of f can be bounded once and ignored. Every odd d|m is coprime to N, so the congruence forces q to be a unit mod d. For each q it fixes at most one j residue. For d≤H there are O(H²/d) (q,j) pairs. Summing using sum_d a_s(d)/d<infinity proves sum_(q,j) f(N±qj)^s≪_s H², including the even cases by removing only the local p=2 factor. The individual means for f(q)^s,f(j)^s follow by the usual divisor expansion. Hölder with exponent four therefore bounds the sum of the full four-factor exceptional multiplier by O(H²). Combine with the fixed q,j bound and sum over O(H²) pairs. Reversal gives the same conclusion for negative gaps if using ordered pairs.

No equidistribution of signs is used. The remaining pairs include those whose cofactors are divisible by different small primes as well as pairs with a common one. Their signed Möbius-weighted covariance at each target remains open.
