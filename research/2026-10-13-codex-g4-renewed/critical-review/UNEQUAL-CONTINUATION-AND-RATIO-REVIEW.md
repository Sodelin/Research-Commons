# Independent review: unequal-cell continuation and equal-product ratios

Reviewer: Codex critical-review lane, 13 October 2026. Hand audit within
the collaborating team. No numerical or formal verification.

Reviewed submissions:

- [UNEQUAL-CELL-CONTINUATION-GATE.md](../chronology/continuation-1837z/UNEQUAL-CELL-CONTINUATION-GATE.md),
  SHA256 `1f2b76484f817cd106baa06009ed8cea8bb9dbb8f423f99927ce66396b00e8b7`.
- [EQUAL-PRODUCT-ADJACENT-RATIO.md](../chronology/continuation-1837z/EQUAL-PRODUCT-ADJACENT-RATIO.md),
  SHA256 `9265735c0babb06884048d6677404f671dc80301056aab65a5a111b2b162cdaf`.

**Hand acceptance of both stated lemmas and their explicitly conditional
consequences.** Neither identifies all unequal cells or supplies a finite
forcing theorem for unequal-arm targets.

## Unequal-cell diagnostic

Direct expansion with `a=t+delta`, `b=t-delta`, `k=m+S` gives the arm
hazard `t(m^2-m+S^2)+delta(2m-1)S`. Relative to the centered fair
binomial law, routing adds `hS-2m log cosh(h/2)`. Thus the displayed
affine-bias formula is exact. Joint holomorphy in bias of the heat-kernel
and finite Taylor subtraction makes its affine-bias continuation
meromorphic, with no poles outside the negative half-integer lattice.
Residues may cancel; that is allowed in the statement.

For `z=x+iy`, the complex bias shifts the real heat-kernel argument by
`2 delta y` and its imaginary part by `h+delta-2 delta x`. Periodicity
and the real Gaussian bound give exactly the claimed Gaussian bound
in x, uniform in y for x nonnegative. The nearest-integer summand to
`S=-delta m/t` lies in the binomial support because `|delta|<t` and
has probability at least `2^(-2m)`. It gives the stated matching lower
quadratic logarithmic growth. This establishes genuine growth of order
`exp(delta^2 m^2/t)` when the arm exposures differ, rather than merely
a loose upper estimate.

The function `exp(c z^2) sin(pi z)` is nonzero, vanishes at every integer,
and satisfies the asserted Gaussian-in-x bound after maximizing
`-c y^2+pi |y|`. Thus the listed growth and meromorphic-location
properties alone do not determine the interpolation. This is an
analytic obstruction to directly reusing the proved Carlson estimate,
not a source-valid rival or an impossibility result for G4. COMMON's
finite exposure-difference/coin palette does not fix the remaining arm
baseline, so it does not justify canceling these unequal factors.

## Adjacent equal-product ratio

Adding two fair Bernoulli increments gives the exact positive-tilt
formula `U_(m+1)/U_m = 1/2 + exp(-t) E_* cosh(h-2tS)/2`.
It implies the lower bound `exp(-t/2)`. The upper bound follows from
the inherited exact uniform diagonal transport estimate with index
`n=2m+2`; the normalization contributes precisely `exp(-2mt-2b)`.
The transport provider's common-parity binomial reweighting proof was
also inspected, including its stochastic dominance of the squared
centered count. No asymptotic parameter restriction is required.

For a fixed strict cell, the central-binomial normalization, pointwise
ratio limit for each integer offset, and summable Gaussian domination
give `U_m ~ C(t,h)/sqrt(pi m)` with positive finite C. Therefore its
adjacent ratio tends to one. The exact uniform bounds dominate the
absolute logarithm of that ratio by `t/2+2b`. Their summability permits
the countable dominated-convergence step and proves the product ratio
limit. In particular this conclusion does not interchange an
uncontrolled large-arity asymptotic with an infinite product.

Finally a positive continuous torus signature F, bounded away from zero
on its orbit closure, has continuous quotient `F(Tx)/F(x)`. If this
quotient tends to one along the forward orbit, every point of that
rotation orbit closure is reached as a limit along indices tending to
infinity, so the quotient is identically one there. Density of each
rotation orbit in its closure then makes F constant. The prefactor
`m^gamma` and multiplicative `1+o(1)` have adjacent ratios tending to
one and do not alter the implication. The conclusion remains
conditional on proving the separate finite unequal saddle
representation; it does not rule out aliases or theta-product identities.

These statements concern correctness and exact scope. Historical
novelty is not certified, and no Lean or Rust status is asserted.
