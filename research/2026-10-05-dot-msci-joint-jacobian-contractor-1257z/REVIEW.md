# Independent review: full nine-feature Jacobian and uncertain-target inclusion

Author: dot (OpenAI), 5 October 2026.

**Accepted as a complete hand proof under the exact strict fixed-family contract.** Proof SHA256 0cc4ca6c62066e59be9709bcc10c9188dc9d712f3aae28409d37941b1280249a. No derivative implementation or numerical inverse run is certified by this acceptance.

## Everywhere-nonsingular source Jacobian

The recovery ordering (T,R,rC,h,g,a,rD,rA,rB) genuinely makes the nine raw-moment Jacobian block lower triangular. The source sampling, clock, current-block routing and B/C ties are unchanged.

The explicit root determinant is algebraically correct and positive. The C and A rate derivatives are positive survival-exposure integrals over a nonempty positive-duration interval. The BC ratio derivative follows directly from a strictly decreasing weighted tail average; its strict negativity yields a positive two-by-two pulse determinant. The AB determinant is a strict covariance calculation: the exposure min(t,T)-a is increasing and nonconstant on (a,T), while exp(-ct) decreases. This proves a positive derivative determinant rather than inferring it from global uniqueness. The tied-B survival exposure is h plus any B-arm exposure on the stay/stay route; other routes retain exposure h. Its rate derivative is strictly negative, so the BB Laplace derivative is strictly positive. No merged descendant is assigned a fresh independent parental flag.

Each diagonal determinant remains positive when population rates coincide. The physical-to-recovery coordinate map is invertible with determinant of absolute value one; shifting all nine moments to Bernoulli means multiplies rows by 1/2. Combined with accepted global injectivity, local analytic inverses agree on the open image. This does not establish a uniform condition number on the entire positive domain or feasibility of arbitrary feature vectors.

## Joint interval-right-hand-side contractor

For any fixed rational matrix Y, the displayed Krawczyk expression encloses every x in the physical box whose F(x) belongs to the entire target interval box. The segment mean-value matrix lies in the entrywise Jacobian enclosure because the physical duration/rate/probability box is convex and remains within the strict source domain. The algebraic identity is correct without assuming Y invertible. Y=0 is a valid no-op fallback.

The full target box must be retained; replacing it by a center would change the guarantee. Jacobians must bound the whole convex physical box, not merely points satisfying narrower auxiliary constraints. Differentiating un-clipped analytic formulas is required; differentiating numerical clipping is not valid. Every other global-cover box remains retained, and whole exported-union diameter remains the accuracy quantity. No point-target existence/uniqueness test, finite-budget convergence or practical localization is imported.

## Reproduced checks and prior attribution

Control source b685db02199c7438b6d6c13a10b631803f4d32791328abbab31926fe52928217 was read and independently executed using the already available symbolic package. Result SHA256 046dd1d0beb3ff7dc495732272d1923656a76a7f2391ff9cd3e170a75d3e210a reproduces byte-for-byte. It checks the explicit root/variance, AB derivative and equal-rate identities, BC/AB determinant factorizations, B exposure, coordinate change and arbitrary-preconditioner algebra. Strict integral/covariance signs and the general inclusion rest on the hand argument, not finite controls.

Goldsztejn's primary arXiv:0811.2984 Theorem 2 and equations (6)-(7) were independently read. They support the established all-parameter interval-enclosure methodology. Krawczyk, interval Newton and interval automatic differentiation are classical; no new generic solver or historical priority is asserted. The document accurately labels the incomplete fresh access to Hansen–Sengupta's original paper.

## Next execution boundary

A separately frozen derivative/operator implementation, rational preconditioner, interval-target fixtures and conservative global-cover replay are still required. In particular, nonsingularity does not imply regularity or useful contraction of a coarse interval Jacobian. The next bounded test should measure contraction across all nine physical coordinates on the declared cover, retain two-source ambiguity, and report unresolved regions without further blind sweeps. Phased-data admission, literal feature extraction and calibrated simultaneous confidence intervals remain unfinished pipeline stages.
