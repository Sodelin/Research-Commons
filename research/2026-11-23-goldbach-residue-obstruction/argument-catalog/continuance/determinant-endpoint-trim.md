# Trimming small additive endpoints in the Goldbach long-divisor sum

This is an absolute hand bound with the original support. It is not a determinant cancellation theorem or a proof of Goldbach.

Let n=dℓ=N−qh in the exact long-divisor expression with weights −μ(h)μ(d) log h log ℓ, and let L=log N, H=√N. For a fixed n the sum of the absolute weights over admitted placements is at most L²τ(n)τ(N−n): both products have at most their divisor count many ordered factorizations. No squarefreeness, roughness, support filter or cutoff needs to be enlarged in the claimed result.

For 2≤X<N, Cauchy–Schwarz and Σ_{m≤t}τ(m)²≪t(1+log t)³ give absolute mass at most
```
O(L^5 sqrt(XN))
```
on 1≤n≤X. In detail, bound Σ_{n≤X}τ(n)² by O(XL³), and Σ_{n≤X}τ(N−n)² by the full initial bound O(NL³). The divisor moment follows from the pointwise comparison τ²≤d₄ and the summatory upper bound for d₄, by successive harmonic sums. Taking X=N/L^B for B>10 gives o(N), and B can be chosen for any prescribed logarithmic saving. This conclusion is unconditional in the expanded expression; using a particular GRH cutoff elsewhere in the full argument is separate.

## Why this helps test the determinant approach

For each dyadic box with d and ℓ on scales D and V, after this trim the product DV is at least a fixed multiple of N/L^B and at most a fixed multiple of N. In the smooth version of the relation qh+dℓ=N, put q=Eq′, ℓ=Fℓ′ and g=gcd(E,F). The variables in Bettin–Chandee's Corollary 1 have scales M₁≈H/E, M₂≈V/F, N₁≈(F/g) D, N₂≈(E/g) H. The geometry factor of the corollary is therefore H²/(DV)+DV/H², bounded by a fixed log power on the remaining boxes regardless of the relative sizes of d and ℓ. The reflected negative ℓ′ variable requires checking the proof of the corollary rather than just its positive-variable statement. [Primary determinant estimate](https://arxiv.org/abs/1502.00769)

This only controls the geometry factor. The sizes D,H in the analytic error, and the full weight of all arithmetic masks, must still be accounted for separately. In particular the theorem is asymmetric in which variables carry the Möbius signs. Trimming small n does not justify swapping those variables or treating the entire long-divisor sum as bounded.
