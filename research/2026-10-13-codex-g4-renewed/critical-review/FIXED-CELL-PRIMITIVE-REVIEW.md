# Independent review: fixed-cell large-arity primitive

Contributor: Codex critical-review subagent, 13 October 2026. **Scoped hand acceptance** of the fixed-cell and fixed-finite-word deductions in [FIRST-PRIMITIVE-LARGE-ARITY.md](../chronology/FIRST-PRIMITIVE-LARGE-ARITY.md), SHA256 `d253234438401aef99750f06d10b6befb0272f67376e08e72a81e6f3b1d68044`. The additional all-n sign conjecture remains unproved.

The ordered-integral formula is the inherited actual-source input. Integrating its four terms to infinity gives the displayed expression `g^2 l/(2k+1)+(1-g)^2 k/(2l+1)-p` after multiplication by `kl`. On the central region both arm counts grow linearly in `n`; the discarded finite-time tail is exponentially small. Outside that region the binomial coefficient divided by a central coefficient is at most one, and the factor `exp(hx-tx^2)` supplies a summable Gaussian envelope with all moments, separately on each parity lattice.

For the claimed rate, the central-binomial ratio can be bounded by `|1-ratio|<=min(1,C(x^2+1)/m)`. Together with the Gaussian envelope this justifies the `O(1/m)` mean correction and summation of the ratio expansion. This is a fixed positive `t`, fixed interior `g` argument, not a uniform estimate near weak cells.

I independently checked the constants. With `m=n-2`, the expectation in the integral is

`(1-4p)/2 + [-2(2g-1) E X -(1-2p)/2]/m + O(1/m^2)`.

Since the outer factor is `n/8+1/16+O(1/n)`, the constant term simplifies to `-1/32-(2g-1)mu_e/4`. Thus the claimed linear limit and the fair limit `-1/32` follow. Keeping the parity-dependent discrete Gaussian mean is necessary.

For a fixed finite subsequent word, the inherited cocycle and exponentially decreasing diagonal ratio suppress its polynomially bounded primitive contribution. The first positive ordinary duration is therefore recovered from the logarithmic decay rate of this scalar sequence. This is another proof of a finite-word parameter already recovered by the accepted normal form; it does not identify a no-first-cell countable carrier.

No exchange of the fixed-cell asymptotic with an infinite cell sum is justified. The manuscript correctly leaves that step and the all-n sign conjecture open. No source simulation, historical novelty assessment or Lean verification was performed by this review.
