# The full odd modulus-3 row cancels in aggregate

Elementary application of classical quantitative Möbius cancellation. This is a hand argument, not a Lean check or a statement about the pointwise Goldbach error.

The [odd-semiprime obstruction](../2026-11-23-cofactor-cells-1718z/modulus-3-odd-semiprimes.md) applies to the even targets N≡2 (mod 6). Keep its modulus q=3 and strict cutoff, but include **all odd cells** h, not just semiprimes. Assume 1≤α(N)≤sqrt(N). The same off-diagonal estimate is O(log² N): in the two comparison-only positions n is a multiple of 2 or 3, and each power can appear at most once per offset. The diagonal contribution to the discrepancy is therefore

    E_all_odd(N) = −(1/2) sum Λ(N−3h) μ(h) log h + O(log² N),

where the sum has α(N)<h<N/3 and gcd(h,6)=1. This restriction keeps the odd cells, and the omitted h divisible by 3 have zero diagonal weight.

Sum over N≤X, N≡2 (mod 6). Removing the lower cutoff adds only h≤sqrt(X), costing O(X^(3/2) log X) in absolute value, because for each h the possible Λ weights sum to O(X). Reindex by n=N−3h. All odd h coprime to 6 give the same condition n≡5 (mod 6); conversely this condition puts N in the required class. Thus the diagonal aggregate is

    −(1/2) sum_{n≤X, n≡5 mod 6} Λ(n) · sum_{h≤(X−n)/3, gcd(h,6)=1} μ(h) log h + o(X²).

The inner sum is o(X) uniformly for the included n. To justify it, let M(t)=sum_{m≤t} μ(m) and use the classical M(t)=O_A(t/(log t)^A) for any fixed A. The restricted Möbius function μ(h)1_{gcd(h,6)=1} is μ convolved with the indicator of integers of the form 2^a3^b: this cancels the Euler factors at 2 and 3. Split its partial sum at 2^a3^b≤sqrt(t). The small terms use the bound on M and the convergent sum of reciprocals, giving O_A(t/(log t)^A); each large term is bounded trivially by sqrt(t) and there are O(log² t) of them. Partial summation inserts log h, still giving o(t), hence o(X) uniformly over t≤X. Summing against Λ costs O(X). It follows that

    sum_{N≤X, N≡2 mod 6} E_all_odd(N) = o(X²).

The stronger separate result and this aggregate result are consistent: the isolated odd-semiprime error can exceed any fixed negative budget on infinitely many targets, but the signed diagonal terms with odd Ω(h), including prime cells, offset the negative diagonal terms **in aggregate**. Summation does not show that the compensating terms occur on the same targets, and this proof does not constrain the even cells or other moduli.

For the classical quantitative input, see Montgomery–Vaughan, *Multiplicative Number Theory I: Classical Theory*, Chapter 6 (PNT error bounds and the Möbius mean), and [Kedlaya's notes on quantitative PNT inputs](https://kskedlaya.org/18.785/errorbounds.pdf). The cutoff and sign reductions here are specific to the linked comparison.
