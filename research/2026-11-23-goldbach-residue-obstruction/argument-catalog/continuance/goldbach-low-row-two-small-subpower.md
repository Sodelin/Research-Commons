# The truncated low row with two small primes and one subpower prime

Unconditional pointwise hand estimate on a restricted slice, not a Goldbach proof. Keep the original strict moving cutoff, the full pre-grouping low-modulus row q < Q, and its progression model. Use the definitions and uniform endpoint reductions of [the centered low-modulus row](goldbach-low-modulus-completion-and-short-lanes.md), equations (1) and (5). This is that row, not the unmatched A02 row or the central divisor bracket.

Fix N = 2^k, L = log N and Q = N^(1/4). After the earlier negligible endpoint trims, write m = N - n > N^(3/4), odd squarefree, and retain exactly two prime factors p < r < Q below Q, with p ≤ Y ≤ sqrt(Q) and pr ≥ Q. Put h = m/(pr); it is Q-rough. On this slice the entire divisor support below Q is {1,p,r}; equality pr = Q is still excluded. Therefore

    D_Q(m) = log(m) - log(m/p) - log(m/r) = -log(h).

The centered grouped coefficient from (1) is μ(m) Λ(N-m)(log(h)+S), up to the uniformly negligible model approximation. Here S is the singular-series constant on this target family. The coefficient is adverse only for h prime: h ≥ 2 since pr < Q² and m > N^(3/4), and h < N/Q = Q³, so it has at most two prime factors; μ(m)=μ(h). We can bound absolute weights on both signs without using this last simplification.

Fix a = pr. By the same two-form Selberg upper bound as (5), h Q-rough and N-ah prime > N^(1/20) occur at most O(N/(pr L²)) + N^(1/10+o(1)) times. The local factors at p and r are bounded absolutely (both are odd). Multiplying by O(L²) bounds the weighted charge. There are at most Q² candidate (p,r), so the floor errors total N^(3/5+o(1)), including log factors. For the main term, r is in [Q/p,Q). Since p ≤ sqrt(Q), Chebyshev and partial summation on this interval give

    sum_{Q/p ≤ r < Q, r prime} 1/r ≪ (1+log p)/L.

Consequently the reciprocal sum of the retained (p,r) is O((1+log Y)/L), using sum_{p ≤ Y}(1+log p)/p ≪ 1+log Y. Including earlier trims and model centering, the absolute grouped contribution is

    O(N(1+log Y)/L) + o(N),

uniformly for 2 ≤ Y ≤ sqrt(Q), with the model margin unchanged. In particular it is o(N) for any fixed subpower cutoff log Y = o(log N). This is a complementary case to the earlier small **product** lane, since here the product is at least Q. It does not cover both small primes of polynomial size, three or more primes below Q, or give the missing joint signed lower bound.

A separate finite integer replay verifies the exact strict support and high-factor count for 1,557 selected prime-tested squarefree endpoints at four powers of two (the smallest support is empty). No Lean verification, and the replay does not certify the asymptotic estimate.
