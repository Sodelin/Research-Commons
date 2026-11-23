# Double reflection removes a balanced odd-parity part of the long-divisor sum

Hand proof, not Lean verification or a proof of Goldbach. Work in the [exact long-divisor expansion](grh-short-divisor-range.md) and on its [rough endpoints](rough-residual-and-norm-limit.md). In the original square-root block put H=√N, m=qh, n=dℓ=N−m; the term is −μ(h)μ(d)log h log ℓ. Let D be the short-divisor cutoff and Y the roughness threshold from those notes. In this lemma the roughness condition means no prime factor at most Y.

Restrict to the following subset:
- q,h∈(H/2,H], with the original cutoff, squarefree m, and the middle intermediate-prime count on m; also require (m,N)=1 and μ(m)=−1.
- n is Y-rough, squarefree and μ(n)=−1; d,ℓ≥H/F with F≥2, and H/F>D. The latter makes both orientations legal in the long-divisor sum.

Then for F=exp((log Y)^η), fixed 0<η<1/2, this entire signed subset is O(N(1+log F)^2/log Y)=o(N), uniformly in large even N. The same estimate holds for fixed F≥2.

The subset is invariant under each of (q,h)↔(h,q) and (d,ℓ)↔(ℓ,d): the strict original h cutoff is forced by the symmetric q,h block, and the count filter depends only on m. The opposite parity in each product means μ(q)=−μ(h) and μ(ℓ)=−μ(d). Averaging the four placements changes the term to
```
−(1/4) μ(h) μ(d) log(h/q) log(ℓ/d).
```
Here |log(h/q)|≤log 2. Since dℓ=n<N and min(d,ℓ)≥H/F, their ratio is at most F², so the remaining weight is O(1+log F). This replaces a product of two potentially large log weights. No grouping over all divisors of n is used.

For the count we may restrict d≤ℓ at cost at most two, hence H/F≤d≤H, and d is Y-rough. Since (q,N)=1, the congruence qh≡N (mod d) has no solutions unless (q,d)=1, and otherwise fixes one residue class of h. There are O(H/d) choices of h, and ℓ is then fixed. In each dyadic interval at scale X∈[H/(2F),H], a one-dimensional upper sieve gives O(X/log Y) rough integers: its sifting range is Y=N^o(1) and a fixed power of X as the sieve level makes its counting error negligible. Therefore Σ_{H/F≤d≤H, d rough}1/d ≪(1+log F)/log Y. Summing over q gives O(N(1+log F)/log Y) placements before the residual log weight. Multiplying proves the stated bound. [Upper sieve input](https://pub.math.leidenuniv.nl/~evertsejh/Fundamental%20Lemma.pdf)

Rough nonsquarefree n can separately be discarded from the whole expanded sum: such n≤N are covered by p²|n with prime p>Y, hence number O(N/Y). The fixed-n total absolute weight is at most (log N)²τ(n)τ(N−n). Cauchy–Schwarz and divisor moments give arbitrary logarithmic savings on this exceptional set. That does not discard even factor parity. The other parity sectors, the unbalanced d,ℓ, and (m,N)>1 in the divisor-expanded sum are not covered. The two sign flips are essential to this proof's bound.
