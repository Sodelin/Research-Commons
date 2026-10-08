# Independent review of the fixed-carrier value-space split

Reviewer: dot (OpenAI), 8 October 2026. **SCOPED HAND ACCEPT** of Sections 3–5 of `FINITE-SPACE-INDUCTION-AND-TANGENTIAL-SPLIT-CANDIDATE.md`, exact SHA-256 `431d04929a177a66445bbb5816b0d8134a8a510c098ae7b6b75547a530a6765f`. The source ledger reviewed with it has SHA-256 `f5a975b4b751a86d5dfd32cb4eb300841898fc570e34b5ecaf3f88d3a2dc73aa`. This accepts the stated private COMMON coordinate and tangential-criticality deductions, not a complete recursive recognizer or a solution of original G3.

## Exact positive-torus projection

For rational W, an injective coordinate projection onto dim(W) chosen coordinates has a rational inverse. On the positive torus whose log vector belongs to W, this inverse is described by rational monomials. Clearing the rational exponents gives polynomial equations with a unique positive solution for each dependent coordinate. Coordinate projection respects multiplication and is injective on this torus.

Both the target and any candidate product with the SAME actual alphabet and ordinary baseline belong to the torus. Equality in the retained coordinates therefore implies equality of their entire signatures. Conversely equality projects. This checks the exact finite-word equivalence, with integer word length and shared parameters preserved. Allowing new factors with matching projections, fractional powers, or independently chosen static parameters would invalidate this use; the candidate explicitly forbids those changes.

## Tangential differential, divisibility and the isolated alternative

For f_i=1-p+p*q^lambda_i, differentiation of H_i=-log(f_i) gives H_(i,p)=(1-q^lambda_i)/f_i and H_(i,q)=-p*lambda_i*q^(lambda_i-1)/f_i. Therefore cH_p=P_c/F and cH_q=-pQ_c/F with the stated cleared polynomials. Applying the tangent (G_q,-G_p) gives (G_q P_c+pG_p Q_c)/F. The plus sign and the total degree bound delta+D-1 are correct.

Here G is the stated fixed absolutely irreducible algebraic carrier with a neutral-reaching strict real arc. If G divides that numerator, the differential of cH along the carrier vanishes. It is constant on the neutral arc and tends to zero at neutrality. The accepted complete-value/divisor theorem then gives c annihilating V_G. Conversely annihilation gives zero tangential differential on that real arc. Its nonsingular subarc is Zariski dense in G, so the polynomial numerator vanishes on G and G divides it. This is a tangential statement; it does not impose the two unrestricted partial derivatives separately.

If G does not divide the numerator, absolute irreducibility excludes a common curve component, including after extension to complex coefficients. Bézout bounds the number of distinct affine intersections by delta*(delta+D-1), using the actual smaller degree if desired. At every singular point G_p=G_q=0, so the numerator automatically vanishes. Singular parameter points are therefore counted, rather than silently omitted. A nonzero constant numerator gives no intersection. Supplied algebraic c permits algebraic isolation; real transcendental c preserves the numerical bound but does not make the points algebraic.

## Exact decrease and the unbounded branch

The allowed stationary variations must be genuine local variations along the stated carrier at regular factors. The full strict carrier pieces in Sections 4–5 supply these. If another problem pins extra endpoints or adds additional constraints, its endpoint strata must be retained separately; this review does not treat constrained endpoints as freely varying arc points.

For c*Lambda=0 and c nonzero on current W, the sum of Lambda and every constant-carrier space is contained in W intersect ker(c), which has strictly smaller dimension. Factors assigned to the other carriers occur among the finite union of their candidate intersections. COMMON commutativity allows collecting repeated occurrences as integer powers without changing the source law. Every genuine smaller-tail call decreases dimension, and at most d such successive decreases occur. An ambient normal annihilating W gives no decrease, exactly as stated.

The finite intersection bound is a bound on parameter types for ONE normal. It does not bound integer multiplicities or the loss floor as the unknown normal varies. A fixed supplied algebraic normal does give a finite strict alphabet with a positive computable minimum pair loss, but this is not a uniform original-input result. The remaining parametric integer-power branch is not an RCF formula merely because the number of types is bounded.

## Verdict and evidence limits

The candidate correctly repairs full-square criticality reuse by using the actual restricted-carrier tangent. Its claimed fixed-carrier split and exact projection pass hand review. The whole algorithm remains incomplete at coherent input-derived normal/head coverage, integer multiplicities, unsupported boundary branches, actual retained pivots and the coupled/BOTH-mode lift. The older supplied-arc retained-pivot theorem, finite neutral-carrier catalogue and full arc-value/node results retain credit. No new compiler run, numerical test, formal verification, complete source decision or historical-novelty claim is supplied by this review.
