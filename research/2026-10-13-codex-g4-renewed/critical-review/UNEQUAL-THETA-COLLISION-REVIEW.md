# Independent review: leading unequal theta collision

Reviewer: Codex critical-review lane, 13 October 2026. Hand review only.

Reviewed [UNEQUAL-LEADING-THETA-COLLISION.md](../chronology/continuation-1837z/UNEQUAL-LEADING-THETA-COLLISION.md),
SHA256 `0387d43c7e27a4e33a1a8525844246135163ffa9441a7064677177f31c20476a`.

**Hand acceptance as a failure diagnostic for identification from leading
theta modulation alone.** It does not equate complete diagonals or source
laws and is not a negative witness for finite forcing.

Expanding the exact arm hazard at `k=qn+x`, with `q=b/(a+b)`, gives the
claimed quadratic, linear and offset terms, including `delta x`.
Stirling's binomial tilt contributes exactly
`x[h+log((1-q)/q)]`; completing the square gives the stated eta and
prefactor. At the rational q used in the construction, each residue class
has a fixed shifted lattice. Concavity bounds the binomial ratio by an
exponential linear in the offset, uniformly in large n, while the strict
Gaussian bounds the tails. Thus the residue-class dominated-convergence
justification for the stated leading asymptotic is sufficient.

The displayed parameters give `q=1/4`, `delta=t/2` and eta values zero
and one half, with all exposures positive and coins interior. In the
double theta sum, the substitution `r=j+k`, `s=j-k` is a bijection onto
integer pairs of the same parity. The squared terms are exactly the
two squares written in the proof. Reflection equates the even-s and
odd-s sums, producing the same positive constant C for every r. This
proves the theta multiplication identity without an asymptotic step.

At `x=n/4`, its remaining theta factor is the equal-arm factor with
exposure and bias both `t/2`, as stated. It is constant along each
arity-parity subsequence. Consequently the adjacent-ratio criterion on
both parities cannot by itself identify the individual unequal cells.
The note explicitly preserves the unequal powers of n and all other
normalizations, so no equality stronger than the leading modulation is
implied. Additional saddle coefficients or another legal invariant remain
necessary for the proposed cancellation route.

The algebra is hand checked; no numerical, Lean, or Rust verification is
claimed. Historical novelty of the classical theta identity is not claimed.
