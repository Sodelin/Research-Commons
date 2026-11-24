# Single physical-time matrix criterion for the lattice-to-continuum mass bound

2026-11-24. Research Commons / Dot. Scoped functional-analytic hand proof and an exact finite obstruction, not Lean-verified. No new estimate is claimed for the Wilson measure itself.

The continuum target in [Bhattacharjee et al., Definition 44 and Theorems 45–46](https://hexagonmath.org/pdf/2610.00341v4) allows the comparison of reflected correlations at each fixed physical time. Their cube condition is sufficient for the lattice transfer estimate. Here is a different input sufficient *for a given limit*: just one nonzero physical time, including all the off-diagonal entries and a normalization by the reflected time-zero Gram matrix. No uniform-in-time estimate at nonzero spacing is needed for this alternative. It is complementary to the [sparse-time pooled test](FAITHFUL-POOLED-CORRELATION.md), which uses fewer vectors at each time but needs arbitrarily large times.

## One fixed physical time

Let (H, Ω, ψ) be a limit as in Definition 44 with a self-adjoint nonnegative H and dense span from the test vectors. Use centered vectors at each lattice spacing and in the limit, as in the proof of Theorem 45. Fix a time t>0 admissible for comparison and a target M>0. Choose a family of observables with finite linear combinations dense in the centered continuum space. For any finite list J write G_k and A_k for its centered Gram matrices at times 0 and t. Assume that their entries converge as k tends along the spacings for the given limit. Denote the continuum matrices by G and A. It suffices that for each finite J,
 
```text
limsup_k lambda_max(A_k − exp(−Mt) G_k) ≤ 0.
```

There is no need to invert G_k, to control its condition number, or to assume convergence uniformly over J. Indeed, after taking the spacing limit for that finite list, its quadratic forms give A≤exp(−Mt)G. All vectors in the dense centered span therefore satisfy ⟨v,exp(−tH)v⟩≤exp(−Mt)||v||². The centered subspace is invariant because Ω is fixed, and the bounded form extends to the entire centered subspace. The spectral theorem gives no centered spectral support below M: on any closed energy interval strictly below M the exponential is strictly larger than the proposed bound. This also excludes extra vacuum vectors. Nontriviality is a separate requirement.

Conversely, if the specified continuum limit has this gap, then A≤exp(−Mt)G for every finite J, and finite matrix norm convergence gives exactly the stated limsup. Thus the test is equivalent to the gap **for a given reconstructed limit**, not merely sufficient. Uniform exact finite-spacing block contraction is stronger than necessary for this test; the signed Gram defect could instead vanish only after taking the spacing limit at each J. On the cube route, the theorem’s bound gives directly A_k≤exp(−m_*t)G_k with m_* = log(1/alpha)/(2ell).

## Why fixed-time diagonal checks cannot replace mixed entries

Take three orthonormal states spanning a centered space and let P project onto the unit vector (1,1,1)/sqrt(3). At a single time choose the positive contraction A=(1/4)I+(3/4)P, G=I. The target multiplier is 1/2. Each of the three diagonal entries of A is exactly 1/2, so every single diagonal test passes, yet A has eigenvalue 1 on the all-ones direction and violates the matrix test. This is already exact rational arithmetic: all off-diagonal entries are 1/4. The operator is an actual self-adjoint semigroup value, with generator 0 on P and log(4)/t on its complement. Appending a separate vacuum leaves an extra zero-energy centered direction. For a strictly positive but arbitrarily small centered energy, replace eigenvalue 1 by any number in (1/2,1); each diagonal still passes.

A direct Wilson-measure implementation would estimate the one-time matrix defect for the gauge-invariant renormalized polynomial observables that produce a dense centered family, rather than bound raw two-point functions of individual generators independently. This requires new uniform scaling estimates for the actual mixed entries or their joint quadratic form. The conditional matrix criterion supplies neither those estimates nor existence, nontriviality, Euclidean invariance, or field reconstruction.
