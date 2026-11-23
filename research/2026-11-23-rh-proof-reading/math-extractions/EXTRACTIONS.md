# Two reusable pieces from recent proof libraries

23 November 2026. Source-pinned reading and a hand-derived special-case estimate. This note does not claim historical novelty or a local Lean check.

## 1. Navier–Stokes: stable recovery of weights on separated bumps

In the released Navier–Stokes library, [expIntervalMomentMatrix_det_ne_zero](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/ExponentialMomentMatrix.lean#L28-L50) proves invertibility for distinct real exponents and positive masses in strictly separated intervals. A combination with zero integral against each positive measure has a zero in each interval; a nonzero combination of n distinct real exponentials cannot have n distinct zeros. The bump version permits continuous, nonnegative, nonzero bumps. This is recovery of coefficients in a declared finite basis, not recovery of arbitrary measures.

### A quantitative special case

Suppose exponents are equally spaced, a_i=a_0+i d for i=0,...,n−1 and d>0, and intervals [l_j,u_j] satisfy u_i<l_j whenever i<j. Restrict each positive measure to its interval and assume positive finite mass. Fix T≥max_j u_j and let z(t)=exp(d(t−T)). Put c_j=∫ exp(a_0 t)dμ_j>0. Define the probability measure dν_j=exp(a_0 t)dμ_j/c_j and normalized matrix A_ij=∫ z(t)^i dν_j(t). The original moment matrix is diag(exp(i d T)) A diag(c_j).

By multilinearity in the columns and Fubini,
```
det A = ∫ ... ∫ ∏_{i<j} [z(t_j)−z(t_i)] dν_0(t_0)...dν_{n−1}(t_{n−1}).
```
This is the ordinary Vandermonde identity pointwise. Therefore
```
det A ≥ ∏_{i<j} [z(l_j)−z(u_i)] > 0.
```
All entries are between zero and one. The operator norm is at most the Frobenius norm, hence at most n, and multiplying singular values gives
```
σ_min(A) ≥ ∏_{i<j} [z(l_j)−z(u_i)] / n^(n−1).
```
Thus noise of Euclidean norm η in the *normalized* observation changes the recovered normalized coefficient vector by at most η n^(n−1) divided by the same separation product. The unnormalized error must account for row and column scaling. The estimate deteriorates as intervals crowd together; it is neither an optimal constant nor a claim for arbitrary exponents. The argument is classical Vandermonde mathematics, packaged here as a quantitative counterpart to the pinned lemma.

For two bumps with normalized transformed supports z in [1/5,2/5] and [3/5,4/5], the rows are [1,1] and [m₁,m₂] for the two means. The determinant is m₂−m₁≥1/5, independent of the precise shape of either bump. Calibration still requires knowing the two means; the interval information alone gives a worst-case bound, not the exact inverse.

## 2. SAT: greedy progress without a deduplicated candidate stream

[HashGreedy.scan_contraction](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashGreedy.lean#L123-L165) distinguishes the reference family from a stream whose coverage is sufficient. Suppose each currently surviving positive-weight object survives at most two thirds of the reference rows, and each reference row appears at least once in a stream whose scores are correct. Then choosing the least surviving mass in the stream keeps at most two thirds of the mass. It does not need distinct stream entries or a prescribed order. The proof averages over the reference family, not the possibly skewed stream; the minimum over the stream is no greater than that over the reference family.

An elementary robust variant: if scores on the stream differ from true mass by at most η and selection exactly minimizes the scores, then the selected true mass is at most (2/3) times the incoming mass plus 2η. Compare the selected score to a reference minimizer and apply one η on each side. This error floor matters if repeated until exactly zero; approximate scores alone do not guarantee exact termination. A completely missing reference family member also breaks the original proof unless a replacement coverage theorem is supplied.

The referenced result is a source-level observation, not evidence of new complexity bounds or of this variant being new. For the release's formally covered time bound versus the sharper manuscript estimate, see the [formalization scope note](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/docs/378.md). Neither version claims polynomial time from subexponential time.
