# A cross-factor strip bound for the rough Goldbach divisor expansion

Work with the original short-square-root block q,h∈(H/2,H] for H=√N, original cutoffs and middle count, and the [rough long-divisor sum](rough-residual-and-norm-limit.md). Set m=qh and n=dℓ=N−m; n has no prime factor at most Y. As previously justified, impose (m,N)=1 with arbitrary logarithmic savings. The absolute weight of any tuple is at most (log N)².

Let c,C be fixed positive constants with c<C. Retain d∈[cH,CH] and require h/d∈E, where E is a union of at most B intervals of total length w. Then this part of the sum has absolute mass
```
O_{c,C}(N (log N)^2 / log Y · (w + B/H)).
```
This is independent of the parity of either product. In particular for h/d within η of 1, the mass is O(N (log N)²(η+H^−1)/log Y). One can take η=log Y / ((log N)² a(N)) for any a(N)→∞ and obtain o(N).

Proof: d is Y-rough, so the one-dimensional upper sieve used in [the double-reflection bound](double-reflection-long-divisors.md) gives O(H/log Y) possible d in [cH,CH]. For a fixed d, the number of integers h obeying h/d∈E is at most dw+B (intervals may first be made disjoint). Because gcd(m,N)=1 implies gcd(m,n)=1, any h with a solution is coprime to d. Thus qh≡N mod d is one residue class for q, allowing O(1+H/d)=O_c(1) choices in the original interval, and ℓ is then uniquely determined. Count tuples and multiply by the weight cap. The proof discards restrictions only when taking an upper bound; it does not extend the declared support of the sum.

The same bound holds for any pairing of one factor of m and one factor of n, with the factor of n at scale H: fix the two factors being compared and solve for the other m-factor in one residue class. It covers thin strips, including mixed and even parity, not broad intervals of separation or the bulk cancellation. These are hand bounds, not Lean or a proof of Goldbach.
