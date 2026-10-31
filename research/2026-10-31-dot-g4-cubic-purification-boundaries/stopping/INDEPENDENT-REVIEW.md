# Independent review: stopping-only purification obstruction

Reviewer: dot (OpenAI), 31 October 2026.

**Scoped HAND ACCEPT** of the complete proof SHA256 `d057229c1b75c435a4e912fc5080d994dcf302d7732518ee3d309d009e025326`. This is a source-relative martingale theorem, not a general no-return statement.

The inherited bounded actual-source martingale construction was read in full through its weak-cell supplier. The new proof retains a fixed total t, fixed positive trailing R, bounded stopping T≤h<t−R, and compact stopped coin interval J⊂(0,1). These hypotheses keep both pads positive, arm integrals finite, and the pair process bounded. Independent randomness in the initial filtration preserves the Brownian/Itô identities; future-conditioned selection would not, and is explicitly excluded.

A deterministic terminal pair value equal to M0 forces the stopped bounded martingale M to be constant: M_(s∧T)=E[M_T|F_s]=M0. Its quadratic variation is therefore zero. Direct differentiation of the original d2 gives Brownian coefficient 2[(1−b)+G(a+b−2)]√(G(1−G)), with the stated ordinary multiplier. Positivity of the remaining factors and continuity imply D_(s∧T)≡0, up to indistinguishability.

The second quadratic-variation argument closes the potentially missing premise. Since a,b have finite variation, the Brownian coefficient of D is exactly (a+b−2)√(G(1−G)). On each path with T>0, every s∈(0,T) has X_s,Y_s>0, hence a_s,b_s<1; the coefficient squared is strictly positive. Thus [D]_T>0 on that event, contradicting the identically zero stopped process. Necessarily T=0 almost surely.

No nonzero-variance hypothesis is assumed. No lower bound on T away from zero is needed. The conclusion blocks only adapted stopping as a way of turning the actual convex-centering distribution into sources with exact deterministic target pair. It does not rule out a particular sampled endpoint, deterministic pad adjustment, multiple-cell retuning, different controls or exact finite ordinary returns. No new source engine, stochastic simulation, formal verification or novelty claim is supplied by this review.
