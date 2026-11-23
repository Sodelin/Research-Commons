# Three proof checkpoints

These are scoped elementary hand arguments, not Lean-checked declarations or solutions of Goldbach, twin primes, or any further RH conjecture.

## Goldbach: large prime overlap between modulus and cofactor

In the [centered cofactor-cell split](square-divisor-cells.md), use d for the modulus and k=floor((N−n)/d)≥1 for the cell. Retain cells for which some prime p≥Z divides both d and k, with integer Z≥2. At the actual progression point N−n=dk, so μ(N−n)=0, even when both d and k are individually squarefree. The centered model need not vanish. For each p|d the number of cells is at most floor(N/(dp)), and each cell costs at most d(log N)²/φ(d) as before. Counting overlaps by an upper bound, the total over d≤Q≤N is at most
$$N(\log N)^2\sum_{p\ge Z}\frac{1}{p}\sum_{\substack{d\le Q\\p\mid d}}\frac{1}{\varphi(d)}.$$
Here 1/φ(d)≤τ(d)/d and τ(pm)≤2τ(m); the inner sum is at most 2(1+log Q)²/p. Since the sum of 1/p² for p≥Z is at most 1/(Z−1), the contribution is O(N(log N)^4/(Z−1)). The bound is uniform in N and survives the original moving cutoff. It covers a repeat split across the two factors, not just a square inside k. Small overlaps and coprime squarefree semiprime cofactors are not controlled by this argument. An exact fixture checked the underlying counting inequality in 37,683 cases.

## Twin primes: exact condition on the restricted list

Let C(X) be a finite candidate set of primes p≤X with Ω(p+2)≤2, counting prime factors with multiplicity. Write c=|C(X)|, L=sum over C(X) of λ(p+2), M=sum of μ(p+2), and S=count of partners that are prime squares. Then λ=μ+1_(prime square) on this list, so the number of twin prime pairs on it is exactly (c−L)/2=(c−M−S)/2. This follows from the two signs on the candidate carrier; it extends neither sign criterion to unrestricted partners. If c→∞, a uniform upper bound L≤(1−ε)c for fixed ε>0 suffices; full sign balance is stronger than needed. On a list with c≫X/log² X, even the crude S≤sqrt(X+2) gives S=o(c). Large lists must be supplied independently, and none of these identities estimates the restricted sum. The [Lü–Wang–Wu preprint](https://arxiv.org/abs/2610.20242) concerns all shifted primes, not this restriction. The pointwise sign identity was also checked on 2,034 integers with at most two prime factors.

## RH/GRH proof reading: cost of rescaling a good window

Abstract the interval arithmetic in the [RH proof-reading notes](../../../2026-11-23-rh-proof-reading). Suppose the original estimates hold on arbitrarily late windows [W,W^B]. Fix a≥1 and 1<b<B, and use x=ax′. To fit the entire new window [aW,(aW)^b] into the scaled old window [aW,aW^B] requires exactly W^(B−b)≥a^(b−1), or W≥a^((b−1)/(B−b)). In particular B=2, b=3/2 needs W≥a for this endpoint condition alone. If the same transport also needs (x′)^u≥x^v for fixed u>v>0, a sufficient uniform condition is W≥a^(v/(u−v)); this second requirement can easily be stronger (u=401, v=400 gives a^400). The endpoint claim was checked in 7,500 integer cases by squaring both sides. This separates geometric and analytic duties in the existing window argument. It is not a change to the Lean proof and says nothing about transporting the underlying estimates to nonabelian L-functions.
