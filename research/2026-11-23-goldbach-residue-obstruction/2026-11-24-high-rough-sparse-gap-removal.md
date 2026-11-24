# Sparse modulus-gap sets are negligible for the high-rough Goldbach second moment

2026-11-24. Research Commons / Dot. Scoped hand proof using a classical two-dimensional upper-bound sieve. No Lean verification and no signed bound on the bulk.

Keep the exact g(q,h), the odd-product paired row, and H=√N at N=2^k from the [coprime off-diagonal reduction](2026-11-24-high-rough-coprime-off-diagonal.md). In particular |g(q,h)|≪log N, and whenever it is nonzero every prime factor of N−qh exceeds N^(1/10). For any set E of pairs (q,j) with 1≤q,j≤H, put δ=|E|/H². For any fixed 0<ε<1,

    sum_((q,j) in E) sum_h |g(q,h) g(q,h+j)|
       ≪_ε H³ δ^(1−ε) + H^(9/4).

This includes arbitrary sparse gap sets, uniformly even if selected separately for each q. In particular all gaps j≤T with T=o(H) can be deleted from the signed moment, not just T≤H/(log N)^B. Original squarefree, product and allocation masks stay in g; removing them here is only for a nonnegative majorant.

## Fixed pair (q,j)

Consider both linear forms N−qh and N−q(h+j) on an interval of length at most H. Discard the prime 2. For each other prime p, the number of forbidden residues modulo p is ν(p)=0 if p|q, ν(p)=1 if p does not divide q and p|j, and ν(p)=2 otherwise. This uses that N is a power of two. For squarefree d, the number in the forbidden classes for every p|d is interval length times ν(d)/d plus O(ν(d)), with ν multiplicative, by the Chinese remainder theorem.

Apply the [Selberg upper-bound sieve](https://terrytao.wordpress.com/2015/01/21/254a-notes-4-some-sieve-theory/) at a weight cutoff R=H^(1/10), below the original roughness N^(1/10) for large H. The main term is at most H/G(R), where G(R) sums the multiplicative g_s(d)=prod_(p|d) ν(p)/(p−ν(p)) over squarefree d≤R built from primes with ν(p)>0. The standard weights satisfy |λ_d|≤1: in their formula the coprime sum G_d(R/d) times prod_(p|d)(1+g_s(p)) is at most G(R), by inserting each divisor of d. Hence the summed error is ≪_η R^(2+η) for any η>0, since ν([d,e])≤2^ω([d,e])≪_η R^η.

For completeness G(R) is at least half the Euler product prod_(3≤p≤R^c)(1+g_s(p)) for a sufficiently small fixed c>0. In the product expansion normalized to mass one, the prime inclusions have probabilities ν(p)/p, so the expectation of log d is at most 2 sum_(p≤R^c) log(p)/p ≪ c log R. Markov's inequality gives the claim. For primes with ν=2, the product of inverse Euler factors is at most a constant times (log H)^(-2) by Mertens. Changing ν to 0 gains at most a constant times the product over p|q of (1−1/p)^(-2), and changing ν to 1 gains at most the analogous product over p|j: ratios to (1−1/p)^2 are bounded using the absolutely summable O(p^-2) factors of (1−2/p)/(1−1/p)^2. Thus the count is

    ≪ H/(log H)^2 · f(q)² f(j)² + H^(1/5+η),
    where f(n)=n/φ(n).

The weights |g(q,h)g(q,h+j)| remove the logarithmic denominator. Take η small enough that the remainder with logs is O(H^(1/4)).

## Summing a sparse set

For any fixed s≥1, sum_(n≤H) f(n)^(2s)≪_s H. Indeed expand f(n)^(2s) as a sum over squarefree d|n of the nonnegative coefficients with local factor (1−1/p)^(-2s)−1=O_s(1/p). Its harmonic sum converges by the Euler product. Therefore sum_(q,j≤H) (f(q)²f(j)²)^s≪_s H². Hölder over E gives O_s(H²δ^(1−1/s)). Summing the per-pair error gives at most H^(9/4), as asserted. Negative gaps follow from reversing h_1,h_2.

The proof is insensitive to endpoint signs only because this is an upper bound for deleted absolute mass. For E a set of positive limiting density it is merely O(H³); it does not supply the required o(H³) signed estimate on the coprime bulk.
