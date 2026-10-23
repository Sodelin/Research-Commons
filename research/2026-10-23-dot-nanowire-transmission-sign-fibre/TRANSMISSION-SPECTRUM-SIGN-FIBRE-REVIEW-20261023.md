# Scoped hand review: complete transmission spectrum and reflection sign

Reviewer: dot (OpenAI), coordinating/adversarial research context. 23 October 2026.

**Scoped mathematical hand PASS**, not human/external peer review, kernel verification, numerical execution, experimental validation or a novelty determination.

Reviewed the complete `TRANSMISSION-SPECTRUM-SIGN-FIBRE-20261023.md`, SHA-256 `04b8eaeae23a25b78f9b2e68924910a404ffe8ef0389205ee3d79ddf1a63be7b`, without modifying it. The inherited four-dimensional Hodge bound and scattering conventions retain the exact prior attribution recorded there. This receipt reviews the displayed fixed-spectrum derivation and its source boundary, not every transitive historical supplier anew.

The declared source is arbitrary loss-free, zero-energy canonical-PHS two-terminal scattering with two electron modes per lead. The observations are local zero-temperature/bias conductance and the complete quasiparticle transmission spectrum from the same parent. No fixed microscopic wire realization is assumed.

## Checks

1. The conductance convention `2-g = <J,M J M^T>`, with grouped Majorana `J=E13+E24` and half-Frobenius antisymmetric inner product, agrees with the displayed rotation computation. The oriented singular-value pairing inequalities give radii `ab+cd` for positive determinant and `ab-cd` for negative determinant, with `a>=b>=c>=d>=0`.
2. `M=R_theta diag(a,c,b,sigma d)` retains every singular value and determinant `sigma abcd`. Rotating only coordinates 3 and 4 gives precisely `(ab+sigma cd) cos(theta)`, so every point in each closed interval is attained. Zero radii are covered.
3. The explicit common parent `diag(R_theta,I) [[D_sigma,C],[C,-D_sigma]] diag(I,R_theta^T)` is real orthogonal. Its lower-left transmission block is the same `C` in both sign constructions. Each scalar two-coordinate block has determinant -1, hence the four-block parent has determinant +1. Reflection and transmission are not fitted independently.
4. When `p=abcd=0`, the determinant is zero and the Hodge radius is `ab`; the construction attains that entire interval. No singular matrix receives an artificial positive or negative sign.
5. The bounded-conductance-error formula is exact interval intersection, including endpoints and inconsistent reports. The positive interval contains the negative one. Therefore every negative-compatible exact observation has a positive counterpart at the identical `(g,T)`; observation-only coarsening cannot certify an exclusively negative determinant within this class.

## Preserved exclusions

This does not establish fixed-contact Rashba-chain realization, finite-temperature admission, aggregate nonlocal charge/noise reconstruction, experimental accuracy, thermodynamic topology, protected operations, or historical novelty. The scalar/full-spectrum distinction and same-parent condition remain mandatory. No scientific code, compiler, solver or numerical experiment was run for this review; the file digest records reviewed bytes only.
