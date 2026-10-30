# Separate fixed-architecture curve-selection adapter review

Contributor: dot (G4 cross-review), 2026-10-30. Proposed strengthening suggested by coordinating root; conditional hand proof using the accepted Green source reduction. Separate from the positive-loss differentiable theorem.

## Verdict and exact scope

The adapter is sound for a fixed finite architecture with at least one strictly positive-duration dust cell, at a fixed sufficiently weak reference h0, when EVERY identity-limit dust bias tends to zero. It excludes accumulation at that boundary point of strict equal-arm words satisfying the same two clocks and complete cap12 commutation. Hence a neighborhood (depending on architecture, h0 and the boundary placement data) contains no such strict words. This is not a uniform neighborhood in count or h0, nor arbitrary-stratum confinement, nor original G3 closure. Endpoint-limit dust is deliberately outside this strengthening.

## Algebraic fibre, without exponentiating unknown noninteger powers

Use each physical ordinary survival v=exp(-r), each source-arm survival q=exp(-u), each beta, and target t=exp(-h_ref) as variables. On a fixed complete finite carrier, ordinary and colored spectral exponents are nonnegative integers. Equal-arm routing is polynomial in beta by arm symmetry. Thus all actual finite-word entries are polynomials in v,q,beta, and the reference S(t) is rational: its arm survival is t/(2-t), leading ordinary survival t, trailing ordinary survival t²(2-t). Denominators are positive near the base. Clear them to express complete cap12 commutation by polynomial equations.

Exponentiate the fixed physical COMMON clock and pair-exposure clock. Their equations are products of physical ordinary survivals and arm survivals, respectively ordinary survivals and b2=(1-beta)/2+(1+beta)q/2. Fixed right sides are arbitrary real constants, which are permitted in semialgebraic sets. Equivalently exponentiate the loss clock as a positive quotient of these products. No logarithm remains in the defining fibre, and no varying exponent is introduced. Strict admissibility inequalities, including q_dust<1, are semialgebraic. Bias coordinates beta in [0,1) accurately describe the equal-arm source; a lift to one of the admitted coin branches exists and need not be differentiable.

If strict points accumulate at the selected base point, analytic curve selection supplies a Nash arc in this semialgebraic fibre, reaching the base at zero. The applicable classical theorem is Coste, Real Algebraic Sets (2003), Section1.5, Theorem1.15: a boundary point of a semialgebraic set admits a Nash arc entering that set. The primary author's notes also explain the Puiseux reparameterization preceding the theorem. Read via the ICTP-hosted primary copy: https://indico.ictp.it/event/a02455/session/32/contribution/19/material/0/0.pdf . This supplies the arc; no claim of a new curve-selection theorem is made.

## Active versus invisible coordinates

Convert the Nash survival arc to duration/reference-chart coordinates locally by analytic logarithms and the locally invertible reference arm-survival map. The following finite list consists of analytic functions of the original arc parameter s:

- all dust durations;
- all reference-cell h_i-h0 and reference beta_i;
- target h_ref-h0;
- each MERGED actual ordinary gap total minus its base total, one per junction of successive reference cells.

Do NOT include dust beta deviations in this active list. They only need to tend to zero. Do NOT include the individual divisions of an ordinary interval around identity-limit dust slots: such divisions are invisible after the dust replacement below and could yield a fake earliest nonzero order.

Because at least one dust duration is strictly positive for s>0 and zero at s=0, the active list has a nonzero analytic germ. Let k be the minimum positive vanishing order among its nonzero germs. Set epsilon=s^k. Every active coordinate is then one-sided differentiable at epsilon=0 with a finite first derivative; at least one derivative is nonzero. This is valid even though inverse reparameterization is not analytic at zero. Dust beta still tends to zero and need not have a derivative in epsilon. Internal gap splits need not have derivatives either.

All dust durations are O(epsilon). The full operator bound from the accepted Green note gives pair-normalized dust-I=o(epsilon²), uniformly in bounded surrounding factors. Replace each dust slot by its matched ordinary factor FIRST, with this error, and merge all ordinary factors within each actual reference junction. This makes internal split motions exactly irrelevant at the used order. The reduced effective gap path is differentiable. It is important not to Taylor-expand the unmerged raw parameter map as if the omitted coordinates were C¹.

## Nonzero tangent, including the D=0 case

Write d_l>=0 for dust first slopes and D=sum d_l. Since all dust bias limits are zero, L=D. The normal-contact proof forces reference beta first slopes zero and h_i'=h_ref'=alpha. Clock derivatives give N alpha+D/2=0 and sum p_j=3D/2.

If D>0, p is nonzero and the accepted positive-loss Green theorem gives a contradiction.

If D=0, nonnegative d_l imply every dust first slope is zero. The loss clock gives alpha=0, hence every reference-scale slope is zero as well, and the target slope is zero. Reference beta slopes already vanish. Since at least one active slope is nonzero, some MERGED actual ordinary-gap slope must be nonzero. Effective p equals these gap slopes because every dust first slope vanishes. Therefore p is nonzero even though P_p(1)=0. The proof of the Green identity needs nonzero p and the two spectral-root moments, NOT P_p(1)>0. The same complete first-commutation root restrictions and instantaneous projected second residual hold when D=0. They give 0=s8^N Tquad with Tquad<0, again impossible.

Thus there is no selected arc and no accumulating strict fibre at this boundary point.

## Review boundaries

This is an analytic finite-order argument, not an assumption that an arbitrary original sequence is differentiable. The original fixed architecture admits curve selection because its exact finite equations and clocks are semialgebraic. The positive-duration dust coordinate prevents a completely invisible arc. Without any dust, the trivial base or gap-division-equivalent locus must be removed before claiming isolation. With endpoint-limit dust, a nonzero dust slope can be ordinarily invisible and L can vanish, so the last contradiction is not justified. Mixed unknown-size/growing architectures do not define this fixed finite-dimensional fibre and are not covered.

Conditional HAND ACCEPT of this adapter, subject to the same complete-source, normal-contact and spectral-shape suppliers as the Green cross-review. Parent authorship/review and publication remain separate.
