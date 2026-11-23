# Extending the Goldbach determinant argument away from equal factors

Hand deduction using the [fixed-box proof](determinant-fixed-box.md), the [absolute small-endpoint trim](determinant-endpoint-trim.md), and the determinant formulation of [Bettin–Chandee, Corollary 1 and its Poisson proof in §9](https://arxiv.org/pdf/1502.00769). This is a bound for a proper part of the exact expansion, not Lean verification or a proof of Goldbach.

## Claim

Keep the full original q,h block, its count and coprimality masks, and n=N−qh=dℓ on the original Y-rough support with Y=exp((log N)^θ), θ fixed in (0,1). Keep the exact sharp lower cutoff d>short cutoff, with the cutoff used in the prior notes. Let H=√N and L=log N. The entire signed contribution with d≤H^(41/40) is O_A(N/L^A) for every fixed A, without splitting by parity. The signed coefficients are still on h and d, not h and ℓ.

## Dyadic reduction and mask errors

Partition the d,ℓ ranges into O(L²) dyadic boxes with d≈D, ℓ≈V, preserving sharp d cutoffs in the arbitrary coefficient. Boxes with DV<N/L^B have n≤4N/L^B and may be removed together by the endpoint trim, with B chosen for the desired saving. In retained boxes DV is between N/L^B and N up to absolute factors, V≥H^(39/40)/L^B, and q,h≈H. Smooth the edges of q and ℓ at inverse-logarithmic relative width inside each box. The q,h exceptional pair count is O(N/L^B′+H), and the d,ℓ count is O(DV/L^B′+D); use the sparse-pair divisor moments of the fixed-box proof with B′ sufficiently large. The same five divisibility expansions and truncation R=H^ρ, ρ=1/2000, apply. For the ℓ-roughness truncation, Rankin at scale V gives the same proportion bound because the cutoff on the omitted prime product is still H^ρ; multiply the exceptional ℓ count by O(D) possible partners. Bounds for the other truncations involve only the unchanged q,h sizes. At all steps actual weights and absolute mask multiplicities are bounded by fixed divisor moments, not pointwise powers of N.

## Determinant estimate

Use E=lcm(a²,b₀b₁,e), F=f, g=gcd(E,F), the same separate masks on h,d, and g|N. The determinant after substitution is q′·((E/g)h)+ℓ′·((F/g)d)=N/g. In §9 of Bettin–Chandee, for the plus equation parametrise with x=ℓ′·((F/g)d) and use the product of smooth weights g_smooth(x/n₁) f((N/g−x)/n₂), where n₁=(F/g)d, n₂=(E/g)h. Poisson is along the same single progression for x, so the reciprocal modes differ at most in the sign of their phase from the minus equation. The supports, derivative bounds and integration-length estimates used in §9 are unchanged with N/g−x in place of x+Δ. This justifies the plus-sign variant, not a substitution that silently translates Δ by a variable.

The geometry ratio M₁N₂/(M₂N₁)+its reciprocal is O(L^B) here, since M₁∼H/E, M₂∼V/F, N₁∼FD/g, N₂∼EH/g. Scaled dyadic intervals can be partitioned or smoothly covered by O(1) comparable supports. The coefficient norms, including the log weight, are at most O(H^½ L) and O(D^½), not the norms of dense sequences of length EH or FD. Corollary 1 therefore yields an error bounded by
```
L^C (HD)^(17/20) (H+D)^¼ (EF)^(7/20) max(E,F)^¼ (HV)^ε
```
with an additional arbitrarily small exponent from the corollary and groupable log factors. For D≤H it is at most H^(39/20+3.35ρ+O(ε)) times logs. For H<D≤H^(41/40), its base H exponent is at most 39/20+11/400=1.9775, before 3.35ρ+O(ε). At most H^(5ρ) mask choices and H^ρ for the count-expansion coefficient leave a power saving with the stated ρ and sufficiently small ε. No lower bound of polynomial size on D is needed for these estimates; the original short cutoff is simply in its arithmetic coefficient.

The main term has the same lattice factor 1/lcm(E,F), multiplied by O(H/D) and by a smooth normalized q-integral with polylogarithmic size and total variation in h. The log bound on the geometry ratio gives that variation uniformly. The h-sum is bounded by the original masked Möbius prefix estimate at scale H. Summing O(D) values of d cancels H/D and the reciprocal Euler summation across masks remains polylogarithmic. Thus the main term is O_A(N/L^A), and logarithmically many boxes and exact count coefficient extractions are harmless.

## Remaining gap

After the negligible small-endpoint trim, the theorem reaches ℓ≥H^(39/40)/L^B for the covered d orientation, but this is not a theorem for all tuples with ℓ above that threshold. Larger d leaves the range justified by this power budget; swapping it with ℓ moves μ to a different variable and can break the smooth-coefficient interface. The separate small-ℓ sieve reaches only subpolynomial ℓ and has its own cofactor or parity qualifications. The middle between these regions remains open.
