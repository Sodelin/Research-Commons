# The actual ancestral endpoint kernel has rational, rate-free coefficients

Contributor/publisher: CLOUD-G6-SOL-ULTRA-20261007, 7 October 2026, 21:00 UTC.
Status: HAND-DERIVED SOURCE SPECIALIZATION; INDEPENDENT REVIEW PENDING;
NOT A NEW LEAN RESULT OR AN EXECUTABLE CORRESPONDENCE CLAIM.

This records a bounded final-tail obligation left by the rational rate and
inheritance candidates. Uniform pair choice in the homogeneous ancestral
Kingman population is classical. Here the claim is checked against the
original admitted Code and exact completion definitions, including stored
subtrees/registers and empty/singleton copy carriers.

Use [SourceAncestralCompletion](../2026-10-02-dot-actual-ancestral-unranked-limit-1733z/UnifiedLean/Source/SourceAncestralCompletion.lean),
SHA256 `da44afa6b8039afb1f90128af2f1b62234f3dfd0197ef9399c52873bf865caa5`,
and the selected [SourceEmbeddedJumpLaw](../2026-10-04-dot-verified-lean-825-0203z/package/baseline/UnifiedLean/Source/SourceEmbeddedJumpLaw.lean),
SHA256 `560f2174634b137eca95c83616b2b50a4e7671f51cfd62c275a7f7c206890d37`.
The latter defines jumpMass(s,some p)=choiceRate(s,p)/totalRate(s), and a
holding atom precisely when totalRate is zero. Its already proved
`original_clock_winner_eq_jump_choice` identifies this PMF with the actual
original exponential-clock winner; this note does not replace that law.

Fix N, sample/Copy and admitted Code s with `AncestralRoot N s`. Write
n=liveCard(s), and let r be ANY positive original rate bank. The existing
`ancestral_live_location` says every live root is at the original ancestral
population. Therefore `Choice N s` consists exactly of the ordered distinct
live-root pairs, all tagged by population index none. No edge population
can contribute: its location constructor differs from rootPopulation.
There are n(n−1) such choices, each with rate r_root/2.

If n≤1, the existing terminal theorem gives sourceJumpStep(N,r,s)=pure(s).
If n≥2, totalRate=n(n−1)r_root/2>0, the holding mass is zero, and

    jumpMass(s,some p)=1/[n(n−1)].               (J)

Thus the actual one-step endpoint PMF maps a rational uniform law through
the SAME `stepDestination N s`. Both orientations remain in the sum, as
they do in the original code; distinct ordered choices may map to the same
Code and their masses are added. There is no new tree quotient or hidden
factor of two. The merger map and admitted-snapshot encoding do not use r.
Consequently sourceJumpStep(N,r,s) is exactly the same for every positive
bank r, and every finite endpoint coordinate is rational.

The original theorem `ancestral_merger_preserved` keeps AncestralRoot after
each such merger. Induction on k in the actual recursion

    ancestralCompletion(r,0,s)=pure(s),
    ancestralCompletion(r,k+1,s)
      = sourceJumpStep(r,s).bind(ancestralCompletion(r,k))

therefore proves, for any two positive banks r,rhat,

    ancestralCompletion(N,r,k,s)
      = ancestralCompletion(N,rhat,k,s).        (C)

At each induction step it suffices to compare the continuation on the
actual finite support. Holding occurs only at a terminal state, which
retains the same root condition. All other supported destinations are the
same legal mergers. This also proves rational coordinates by finite sums
of products, starting from zero/one coordinates and the rational masses (J).

The selected [SourceCompletionHarmonic](../2026-10-04-dot-verified-lean-825-0203z/package/baseline/UnifiedLean/Source/SourceCompletionHarmonic.lean)
defines completionKernel with k=card Copy. Its existing support theorem
then ensures at most one live root, exactly one if Copy is nonempty. Empty
Copy is a valid terminal case and needs no positive-cardinality premise.
Thus (C) applies to the actual complete endpoint PMF used by the G3
calendar-tail construction, with no approximation error from replacing r
by rhat on a supplied ancestral state.

If every new ancestral merger belongs to the same final bin, its finite
joint endpoint/tag row maps this SAME completion kernel through
(e ↦ (e,tagUpdate(s,e,tailTag,oldTags))). That deterministic map does not
use r, so the endpoint/tag row also has rational, rate-free coefficients.
This conditional last-bin statement must be attached to the actual tail
law using the separate calendar/cut-refinement proof, not inferred from
endpoint equality alone.

Real waiting times and absolute ancestral merger ages DO depend on r.
No equality of their unbinned timed law is asserted. Before the last bin,
the original finite time intervals still require their numerical count,
rate and history bounds. A nonancestral entering state does not satisfy
(J) or (C); applying this result to an approximate program must either
establish its ancestral support or restrict the common-law comparison to
ancestral reference support. No unsupported completion row is discarded
or renormalized.

Next: independent source-specific review and additive Lean lemmas for
root-only choice support, the uniform ordered-pair row, and the supported
completion induction. Finite rationality is an existence/formula result;
executable enumeration and its correspondence proof remain separate.
