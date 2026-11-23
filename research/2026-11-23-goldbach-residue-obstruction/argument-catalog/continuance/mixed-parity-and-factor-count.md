# Mixed-parity cancellation and a wider factor-count saving

Fourth proof pass; hand arguments, no Lean verification. These are results on proper subsets, not a proof of Goldbach.

## Mixed parity cancels exactly on common support

In the [rough long-divisor expansion](rough-residual-and-norm-limit.md), write m=qh and n=dℓ with m+n=N. Keep all four factors in the original interval (√N/2,√N], both products squarefree and coprime to N, and require BOTH products to satisfy the roughness and middle-count filters. The original strict h cutoff then holds, and both original and swapped d exceed the short-divisor cutoff for large N. Restrict to mixed parity μ(m)μ(n)=−1.

The map (q,h,d,ℓ)↦(d,ℓ,q,h) is an involution of this common support. The transformed weight is −μ(ℓ)μ(q) log ℓ log h, equal to the original weight multiplied by μ(m)μ(n), and thus the total is exactly zero. This cancels the two mixed orientations together, not each separately. It is not the double reflection already used on odd–odd parity: this time the two products exchange roles. If A is the indicator of original mixed support, one may write the sum on a swap-invariant ambient domain as one half of Σ W(x)(A(x)−A(Tx)); the terms left are exactly the asymmetric mask boundary (including failures of the factor window or a filter on the swapped products), which this identity does not yet bound. Even–even does not flip under this swap.

## Actual-prime region with fixed numbers of large factors

In the original actual-prime sum, require a fixed positive number of primes above Z on each of q and h. The product of all remaining factors on each side has primes in the original intermediate interval J and has size N^o(1) by the upper factor-count cutoff; no other factors are allowed in this class. The squarefree condition makes the two remaining factor products disjoint in primes. Write j=k(qh) for the number of intermediate primes.

On each side single out the largest prime above Z; it is at a polynomial scale because its number of peers is fixed and the intermediate product is N^o(1). For fixed values of the other factors, count the largest prime on the q-side by the ordinary prime upper bound, then sieve the largest prime on the h-side together with the endpoint N−qh by the same two-form upper sieve as in the [one-large-prime case](third-pass-two-boundaries.md). The remaining large primes cost at most a fixed power of log log N in reciprocal sums, and their local sieve corrections are bounded (they exceed Z). For example for one large prime r on q and two s<t on h, sum 1/s over Z<s≤√(√N); the t interval stays at polynomial scale uniformly. Proper prime powers, small endpoints and prime bases dividing N have negligible weight by the divisor bound as before. After the log²N weight cap this gives N/log N times a fixed power of log log N and the j-th coefficient of
```
∏_{p∈J}(1+2 g(p) u/p),
```
where g is the two-form correction from the previous note. The 2 assigns the prime to one side or the other, and squarefreeness precludes using it twice. This coefficient is at most (Σ_{p∈J}2g(p)/p)^j/j!. For J=(exp(L^.10),exp(L^.99)] with L=log N, the sum in parentheses is 1.78 log L+O(1). Stirling gives a cost L^[c(1+log(1.78/c))+o(1)] for j=c log L with c bounded away from zero. Whenever the exponent is below 1 by fixed slack, the actual contribution is o(N) even in absolute value. The numerical roots of equality are 0.4019042664 and 3.6899200058. This gives larger low and high margins **in this fixed-large-factor shape only**; the central count band and shapes with an unbounded number of large factors are not covered. Summing O(log L) admissible count values does not consume a fixed power saving.
