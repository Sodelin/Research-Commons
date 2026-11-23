# Second proof pass: sharper boundaries for three Goldbach approaches

Hand deductions on the same square-root block and with the original support. They do not close the bulk residual or constitute a Lean check. See [first pass](three-proof-attacks.md) and [GRH-expanded short-divisor cutoff](grh-short-divisor-range.md).

## A. Strong prime Fourier peaks can be removed by amplitude, not just location

Let H=√N, L=log N, and let A_q(ξ) be the exact row kernel from the first pass. With the Dirichlet GRH input, that row argument gives sup_ξ |A_q(ξ)| ≪ H exp(−cL^(1−β)) for a fixed c>0, where β<1 is the upper intermediate-prime exponent. The exact count mask and logarithmic weight cost only powers of L and can be absorbed by reducing c.

Write F(ξ)=Σ_{n<N}Λ(n)e(nξ). Let E be the set on which |F|≥N exp(−cL^(1−β)/2). By Parseval and Σ Λ(n)²≪NL, one has ∫_E|F|≪ L exp(cL^(1−β)/2). Multiplying by the uniform row bound shows that the projection onto E contributes exponentially little on the L^(1−β) scale to each row (relative to H). Consequently removing E changes the full squared row norm by O_A(H³/L^A) for every A, by Cauchy–Schwarz and the trivial full row bound. This works regardless of where the peaks lie. The remaining Fourier amplitudes can still be much larger than √N; this is not a bound for the remaining energy. Dirichlet GRH supplies a zero-free half-plane for the [Baker–Harman input](https://doi.org/10.1112/jlms/s2-43.2.193).

## B. Thin prime-endpoint strips can be trimmed from the second moment

In the two-form upper sieve for the off-diagonal moment, additionally restrict one prime endpoint N−qh_i to any fixed interval of length N/L^(2+ε). At fixed h₁,h₂ this restricts q to an interval of length O(H/L^(2+ε)). The same residue sieve gives a count O(H L^(−4−ε)(1+log L)² + N^(1/10)L) in this interval; the second term is the uniform sieve remainder. After the L⁴ weight cap and O(H²) ordered h-pairs, the cost is O(H³ L^(−ε)(1+log L)² + N^(11/10)L⁵)=o(H³). The globally negligible exceptional prime endpoints are unchanged; the diagonal is handled as in the first pass. Thus single thin transition strips can be removed to smooth a proof without controlling the far, small-gcd bulk.

## C. A slice where the long-divisor remainder vanishes exactly

Let D=exp(L^(1−β)/32), n=N−qh and a_D(n)=∏_{p|n, p≤D}p. If a_D(n)≤D, every contributing short squarefree divisor of n is precisely a divisor of a_D(n). The short weight then equals log n for a_D=1, log p for a_D=p, and zero for a_D with at least two primes: expand Σ_{d|a_D} μ(d) log(n/d) and pair divisors. In the last case n is not a prime power, so Λ(n)=0 and therefore the long-divisor remainder vanishes exactly. The threshold is literal d≤D and does not need rounding assumptions.

For a quantitative slice take y=exp(L^θ) with 0<θ<1−β and n free of primes in (y,D]. Then a_D=a_y. Rankin with η=1/log y gives #{n≤N:a_y(n)>D}≪N exp(−log D/log y): expand the product ∏_{p≤y,p|n}p^η, and bound the resulting ∏_{p≤y}(1+(p^η−1)/p) by O(1) using p^η−1≪η log p and the standard bound Σ_{p≤y}log p/p≪log y. The raw weight at fixed n is at most L²τ(n)τ(N−n). By Cauchy–Schwarz twice and τ(n)^4≤d₁₆(n), the exceptional total is O_A(N/L^A) for every A. Thus the slice with no intervening prime and at least two small primes is negligible. With exactly one such prime p the residual is −log p except on p-powers, where it is zero. For y-rough n with no prime in (y,D], the residual is Λ(n)−log n. That last expression includes the hard rough-prime correlation and is not proved small. The slice with a prime in (y,D] is also not estimated here.
