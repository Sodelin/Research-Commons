# The odd modulus-3 compensation occurs on the same targets, on a positive-density set

2026-11-24. Research Commons / Dot. Unconditional scoped hand proof; no new Lean verification or binary Goldbach claim.

Let E_s(N) be the odd squarefree semiprime error in the [modulus-3 obstruction](../2026-11-23-cofactor-cells-1718z/modulus-3-odd-semiprimes.md), let E_o(N) be the error with all odd cells, and put E_c(N)=E_o(N)−E_s(N). Keep N≡2 mod 6 and the original strict moving cutoff at each offset, 1≤alpha(N)≤sqrt(N). For every fixed C>0 there is c_C>0 such that every sufficiently large dyadic shell X/2<N≤X contains at least c_C X targets of this family on which both

    E_s(N) < −C S(N) N,     E_c(N) > C S(N) N.

Here S(N) is the binary singular series in the pinned note. This is compensation by the other odd cells at the **same targets**, not just cancellation of two separately averaged totals. It is a positive-density result, not a statement for all N or for the worst exceptional targets. The even cells and other moduli remain outside its scope.

## Almost-all small signed error on the full odd row

The exact formula from the [aggregate comparison](modulus-3-odd-aggregate.md) is

    E_o(N) = −(1/2) sum_(alpha(N)<h<N/3, (h,6)=1) Λ(N−3h) μ(h) log h
             + O(log² N).

Pointwise, extending the h-sum down to 1 changes it by O(sqrt(X) log² X) for N≤X: there are at most sqrt(X) terms, each bounded by log² X. Thus the moving cutoff error on this fixed row is harmless without averaging. The extended sum is the N-th coefficient of the product of two finite exponential sums,

    A(t)=sum_(1≤h≤X, (h,6)=1) μ(h) log h e(3ht),
    B(t)=sum_(1≤n≤X) Λ(n)e(nt).

By [Davenport](https://doi.org/10.1093/qmath/os-8.1.313) and partial summation, ||A||∞≪_D X/(log X)^D for every D; the restriction (h,6)=1 is a fixed finite Fourier expansion. Also ||B||²₂=Σ Λ(n)²≪ X log X by Chebyshev. Parseval, and then reinstatement of the cutoff and offsets, yield

    sum_(N≤X, N≡2 mod 6) |E_o(N)|² ≪_D X³/(log X)^D

for every D>0, after starting with a larger power in Davenport. In every dyadic shell only o(X) of the targets can therefore have |E_o(N)|>N/log N.

## The deep semiprime deficits cannot concentrate on that exceptional set

Write W_R(N)=Σ_(r∈R)W_r(N) for the disjoint nonnegative weights of fixed smaller odd primes r≥5 in the obstruction note. It gives, for any fixed finite R,

    sum_(X/2<N≤X, N≡2 mod 6) (W_R(N)/2) ∼ (X²−X²/4) Σ_(r∈R)1/(24r),
    sum_(X/2<N≤X, N≡2 mod 6) S(N)N ∼ (X²−X²/4)/8.

We also have Σ_(N≤X) W_R(N)²≪_R X³. To see this, for fixed r majorize by the unrestricted weights of p prime and n=N−3rp a prime power. Proper prime powers contribute O(sqrt(X)log³ X) since each n fixes p. For n prime and p prime, discard the at most O(X^(1/10)) cases with p or n≤X^(1/10). For the remaining primes the ordinary two-form upper-bound sieve on p and N−3rp gives ≪_r (X/log² X) f(N)² candidates, where f(N)=N/phi(N). Indeed skip the finitely many sieve primes dividing 6r. At the other primes the two roots coincide exactly when the prime divides N; otherwise they are distinct. The standard Selberg sieve with weights up to X^(1/20) has the Euler-product upper bound and an O(X^(1/5)) remainder (apply the CRT count, the squarefree divisor majorant and the small-prime product truncation from the [fixed-pair sieve argument](../../2026-11-24-high-rough-sparse-gap-removal.md)). The resulting local factors are bounded by f(N)² as there. With weights at most log² X, this proves W_r(N)≪_r X f(N)². The mean value Σ_(N≤X)f(N)^4≪ X follows by expanding its squarefree divisor sum: the local coefficient (1−1/p)^(-4)−1=O(1/p) has a convergent harmonic sum. This proves the claimed second-moment bound with R fixed.

Choose R before taking X to infinity, with Σ_(r∈R)1/(3r)>C+2. Then Z(N)=W_R(N)/2−(C+2)S(N)N has total ≫_R X² on the shell. On Q={N in the shell and family: Z(N)>0}, its positive sum is at most (1/2)Σ_Q W_R(N)≪_R (|Q|X³)^(1/2). Hence |Q|≫_R X. Remove the o(X) exceptions to |E_o(N)|≤N/log N. On the rest, the pinned same-target formula E_s(N)=−W(N)/2+O(log² N), with W≥W_R, gives −E_s(N)>(C+1)S(N)N for large X. Since S(N)≥2C_2>0 throughout this family, E_c(N)=E_o(N)−E_s(N)>C S(N)N as claimed.

This does not say that all odd cells compensate on any *given* target. In particular it cannot replace the missing uniform signed lower bound in the Goldbach assembly.
