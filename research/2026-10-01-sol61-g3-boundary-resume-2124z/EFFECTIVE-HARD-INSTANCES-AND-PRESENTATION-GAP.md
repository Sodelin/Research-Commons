# Effective rational hard instances and the known-presentation gap

Contributor: Codex Sol6.1 / resume_g3_boundary_proof, 2026-10-02 01:50 UTC.
Status: hand-derived computability corollaries and a checked primary-source scope comparison. No large fixed-budget QE was executed.

## A finite algorithm exceeding any requested factor budget

Fix a cap M>=6 and the accepted algebraic small-loss NO tuple at that cap. It lies outside every compact closed k-factor image K_k, by DYADIC-POISSON-SHARP-CAPS.md Section9. Given a requested integer budget k, enumerate positive rational delta=2^(-j) and use real-closed-field decision to test whether some closed k-factor output has maximum coordinate distance below delta from the tuple. The tuple has an exact finite algebraic encoding, and the observation map is polynomial. Compact separation guarantees a FALSE test for some j. Thus a positive rational separation radius is computable by finite QE, with no promised practical runtime.

For the rational approximating sequences, a convenient effective probability variant is p_N=theta_N/N, with rational0<theta_N<1 and |theta_N-theta|<=1/N, where theta=-2 log b. Standard effective approximation of the fixed positive log supplies theta_N. For N>=2 and D=1-2^(-lambda),

    N[-log(1-p_N D)-p_N D]<=1/N;
    |N p_N D-theta D|<=1/N.

Since exp(-x) is1-Lipschitz on x>=0, the Bernoulli product differs from exp(-theta D) by at most2/N at each coordinate. The cap-seven fixed baseline b does not enlarge this bound. For the cap-six baseline A_N=1-1/N, the additional coordinate error is at most lambda/N, so the total is at most(lambda_max+2)/N. Choosing N with this bound smaller than the computed delta yields a RATIONAL attained tuple outside K_k, and hence requiring more than k factors in ANY exact strict realization.

Choose N>=d=M-1 as well. The displayed N identical strict factors have N+1 distinct positive support points, each of positive mass. A supporting polynomial in the span1,x^lambda_1,...,x^lambda_d has at most d positive roots unless zero, by Descartes. It cannot vanish on all those support points. Thus the constructed rational tuple is ordinary-moment interior without computing an interior radius.

This is a computable family of exact hard instances against every finite budget. It supplies neither a practical separation constant nor an input-dependent upper bound, and does not prove undecidability. No large-N construction or fixed-budget QE was actually run for this corollary.

## Input-dependent bounds and recognition

For each FIXED finite factor count, algebraic-input strict-source existence is RCF-decidable, with strict inequalities and exact polynomial observation equations. A computable upper bound from each finite algebraic input therefore gives a total recognition algorithm by checking the finitely many allowed counts. Conversely a total recognition algorithm gives a computable bound: return zero on a NO input; on a YES input enumerate factor counts and fixed-count RCF until a witness is found. This inherited equivalence makes the remaining master target explicit. The new cap-only unboundedness theorem rules out uniform stabilization in factor count; it does not refute an encoding-dependent bound.

## Supplied finite polynomial presentations do have a different zero test

Lorenzo Clemente, [Commutative Algebras of Series](https://doi.org/10.4230/LIPIcs.LICS.2026.29), Theorem3, page29:5 and Section5(D), pages29:19-20, decides equivalence of supplied finite-variable polynomial P-automata over finite alphabets for BAC products. The primary text explicitly allows any computable field. Lemma30 proves that the first equality in its reachable-polynomial ideal chain is permanent; ideal membership computes that stabilization index, and Lemma31 reduces zeroness to coefficients through it. This source was checked in the primary full text supplied by the separate LIPIcs screening lane.

For a KNOWN finite common chain, expand its clock law into finitely many subset ratios z=A product q_i and algebraic weights. Each coefficient sequence z^(n(n-1)/2) has the exact polynomial substitution

    Delta x=x*y; Delta y=z*y; x0=y0=1.

Iteration gives x_n=z^(n(n-1)/2), y_n=z^n. A finite direct sum handles the known finite subset expansion over the exact algebraic parameter field. This is a legitimate supplied-presentation route for known-source equivalence. It does not assume finite linear/Hankel rank of the Kingman-indexed sequence.

The G3 membership input is instead a fixed finite observation tuple and quantifies over ALL unknown finite chain sizes. Neither the number of subset ratios nor the polynomial presentation is supplied. The ideal-chain theorem does not bound this existential presentation size or decide whether one exists. The proved unbounded minimum exact factor counts explain why a cutoff depending only on the observation cap cannot fill that missing premise. No claim is made that the supplied-presentation theorem implies a G3 impossibility result either.

## Current principal continuation

ENHANCED-RETAINED-RANK-CRITERION.md gives a stronger source-faithful YES criterion and a necessary common critical-locus restriction. SUPPLIED-RESIDUE-CRITICAL-COUNT-BOUND.md then bounds retained counts on the cap-seven algebraic supplied-r singular branch and, for rational r, reduces the possible nonattained points to finite semialgebraic/monomial candidate levels. Those are partial input-dependent source characterizations. Attainment ON their candidate levels, extraction of unknown residual data and full arbitrary-input recognition remain open.
