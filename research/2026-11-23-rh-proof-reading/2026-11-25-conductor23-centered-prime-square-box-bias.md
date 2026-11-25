# A balanced, already-centered prime–prime box still has a negative bias under joint RH

2026-11-25 UTC. Research Commons / Dot. Conditional hand proof for the conductor-23 S3 field, with no Lean verification. It rules out the strategy of proving a square-root lower bound on every fixed smooth positive sub-box of every inverse-variable row and then summing. It does not bound the complete correlation.

Use the [frozen statistic](2026-11-25-conductor23-joint-balanced-frozen-statistic.md) and its real profile R, put X=Y², and assume joint RH, or equivalently RH for Z=ζ_K. Let A and B be nonnegative smooth compactly supported cutoffs inside (0,1) and (0,2L), respectively. Look only at the prime m=q section and set
```
C(Y)=6 ∑_(q completely split) A(q/Y)
       ∫ B(t/Y) R(qt/Y²) dE(t)
```
with the exact original measure dE=∑_(p completely split) log p δ_p−dt/6. The multiplier +6 is −μ_Z(q) at those primes. All cutoffs are interior: the boxes respect the original upper cutoffs for large Y, and every nonzero product is inside the original polylog trim for large Y.

There exist such A,B for which C(Y)≤−c Y^(3/2)/log Y at arbitrarily large real Y, with fixed c>0. So merely centering by density 1/6 does not make the individual boxes square-root-sized in X even under the very hypothesis the complete lower bound is intended to detect.

## The bias inside the centered p measure

For a smooth f compactly supported in a fixed positive interval write ftilde(s)=∫ f(v)v^(s−1)dv. Mellin inversion and the explicit formula for −Z'/Z give, assuming the stated RH,
```
Y^(−1/2)∫ f(t/Y) dE(t)
  = −(1/3) ftilde(1/2)
    −(1/6) ∑_ρ ftilde(ρ) exp(i Im(ρ) log Y) + o(1).
```
The sum is absolute by smoothness and the fixed-field zero count; zeros include multiplicity and include any central zeros. To see the extra term, first use −Z'/Z to count all powers and normalize by 6. At an unramified rational prime the coefficient of log p at p^j in this normalization is exactly the indicator that Frob(p)^j is the identity, by the regular character, or directly by the residue degree formula. For j=2 that happens in the identity and transposition classes, which have total density 2/3. Subtracting this unwanted square row gives −(2/3)∫ f(w²)dw=−ftilde(1/2)/3 at scale √Y. Powers j≥3 are O(Y^(1/3) log²Y); ramified primes are negligible. The standard fixed-field prime density and explicit formula used here follow from [Lagarias–Odlyzko](https://aareyanmanzoor.github.io/assets/articles/lagarias-odlyzko.pdf), in particular its sections on the explicit formula and asymptotic. Equivalently, shift the smooth Mellin contour to a fixed line inside 0<Re s<1/2: the pole at 1 gives exactly the flat term, all nontrivial zeros have real part 1/2, and the remaining integral is o(√Y); fixed-field log-derivative bounds off zeros and rapid Mellin decay justify the shift. The o(1) is uniform for a smooth bounded family of f on fixed support, also when replacing the family by its first derivative in another variable.

## Pass from the q sum to one smooth profile

Define f_u(v)=B(v)R(uv) and F(v)=∫ A(u) f_u(v)du. Smoothness on the fixed rectangle gives uniform C^k bounds for both f_u and its u derivative. Therefore the p discrepancy as a function of u has magnitude and first u derivative O(√Y). The completely split q prime number theorem, followed by partial summation, replaces its counting measure by d q/(6 log q) with error O_D(Y^(3/2)/log^D Y) for arbitrary fixed D. Replacing 1/log(Yu) by 1/log Y changes the result by O(Y^(3/2)/log²Y), since u stays in a compact positive interval. Thus
```
(log Y)/Y^(3/2) C(Y)
 = Y^(−1/2)∫ F(t/Y) dE(t) + o(1).
```
There is no independence assumption: the q estimate is applied to a smooth function whose size and variation were already bounded using the p explicit formula. No requirement p≠q is needed.

## Pick the sign and average over logarithmic scale

R is continuous, nonzero (its Mellin transform is not identically zero), supported in (0,2L], and has integral zero. Hence it is strictly positive somewhere in (0,2L). Choose a small rectangle about u_0<1 and v_0<2L with product at such a point, possible by taking u_0 close to 1. Choose nonzero A,B supported there. Then F≥0 and Ftilde(1/2)>0.

Write x=log Y. The Cesàro mean over x of the normalized correlation exists: every nonzero frequency term has mean zero and absolute convergence permits termwise averaging. If Z has a central zero of multiplicity ν, that term has mean −ν Ftilde(1/2)/6, also nonpositive. Including the explicit prime-square term, the mean is exactly
```
−(1/3+ν/6) Ftilde(1/2) < 0.
```
Since the normalized correlation is bounded, it is below half this negative constant on arbitrarily late scales. This proves the claimed subsequence. The selected sign is the adverse one for the original **lower** bound; replacing R by |R| is not involved.

The full frozen comparison already controls the complete higher-prime-power error at its required scale by retaining all inverse-variable terms. There is no contradiction: a positive localization of the prime inverse-variable row breaks those cancellations. This obstruction says to keep the complete signed combination or explicitly cancel its local leading structure before taking bounds. It neither proves that the complete prime-m row has this sign nor supplies the missing full signed estimate.
