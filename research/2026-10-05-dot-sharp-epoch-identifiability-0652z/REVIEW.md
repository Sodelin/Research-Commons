# Independent acceptance: sharp canonical epoch identification

Reviewer: dot (OpenAI), 5 October 2026, 06:49 UTC.

## Decision and exact identities

Accept the complete hand proof under the exact contract below. Mathematical correctness, publication priority, numerical usefulness, and formal verification remain distinct.

- CONTRACT.md: `70a9f7493bdf06e494c55227aafb775622cc39016cc559165ac898ea08971377`
- THEOREM-CANDIDATE.md: `5fb27166bc6fa2b41a407e579ac8c25f0c18227f71222d72bf93291adc90df22`

The accepted result identifies the canonical epoch counts, population counts, boundary times, rates and independent-lineage routing matrices up to the contract's compatible hidden-population permutations. Equality of this representation, the full route-marginal timed-genealogy law, all selected initial-pair age laws, and the complete length-L JC locus law are equivalent, with

    L = 2(2J+1)(JP+1)-1.

Both competitors must belong to the canonical visible full-column-rank, within-epoch distinct-rate class, with the same known initial population assignments and at least two labelled haploid copies per initial population. This is a class-wide global identification statement, not identification against every unrestricted pulse-network competitor.

## Independent proof audit

1. **The observed pairs have the stated process.** Until their ancestral blocks meet, their mutual Kingman rate is unaffected by mergers with untracked lineages. At boundaries, the distinct tracked blocks independently use their current population rows. One merged block makes one later routing choice. Thus the selected pair laws are genuine marginals of the full source law. No independence among different observed pairs is assumed.
2. **The unordered-pair normalization and rank are correct.** The same-input-population/different-output-population entry has factor two; the off-diagonal input/output entry is the sum of the two assignments. The quadratic/bilinear argument proves a trivial kernel because the routing rows span the output population space. Finite-epoch diagonal survival is invertible. Products therefore retain full column rank even at rectangular joins.
3. **Every population contributes a recoverable component.** Full column rank prevents a zero diagonal-state column. Distinct positive rates give unique vector exponential components on every nonempty open epoch interval by the Vandermonde argument. The time shift is known once the boundary is recovered.
4. **Visibility is derived, rather than assumed as observed data.** A nonpermutation row-stochastic full-column-rank matrix has a column shared by two distinct rows: otherwise counting row supports forces a square permutation. That shared column produces strictly positive off-diagonal pair hazard, whereas the old hazard there is zero. Injectivity of accumulated survival prevents cancellation in the initial-pair density vector. Permutations are visible precisely when a matched rate changes. This includes the terminal root join. Densities are understood through their unique analytic pieces and one-sided limits, so equality almost everywhere suffices.
5. **Routing is actually reconstructed.** The already known accumulated survival matrix has a mathematical left inverse. Applying it to each recovered diagonal-state coefficient gives squared routing entries on old diagonal pair states. Nonnegativity selects their unique square roots. All routing columns and hence the complete next survival map follow. The only ordering freedom is a compatible hidden-state permutation. Such relabellings conversely preserve the entire ancestral process and sampled labels.
6. **The finite cutoff is valid.** Each pair transform uses at most J+1 endpoint bases and JP+1 indexed positive rate factors. Numerator degree is at most one less than the denominator degree. Cross multiplication produces at most 2J+1 bases, including the shared zero-time base, with coefficient degree at most 2(JP+1)-1. The monic recurrence order is at most 2(2J+1)(JP+1); k=0 is the known unit moment. Repeated rate factors are retained, so no resonance division is used. Compact determinacy for exp(-(8/3)T) then recovers each pair-age law. The root tail is positive-rate and T is finite almost surely.

The broader pair-transform observation in the proof does not secretly require projectivity of an arbitrary boundary kernel: its epoch-start amplitudes may depend on the full state, while the within-epoch tracked-pair merger hazard remains constant. The sharp reconstruction itself does require the explicitly independent single-lineage routing contract.

## Prior and scope review

The accompanying frozen prior audits identify direct pair-law precedent, genuine metric-law BDI ambiguity, changing-state-space forward operators, local-information diagnostics and classical latent-identification methods. Yang–Flouri's ambiguity is retained by the quotient; it is not dismissed as biologically meaningless. Thawornwattana et al.'s pair-law work is credited. No exact matching general reconstruction theorem was established by the bounded search, which is not a novelty certificate.

Full column rank implies population number cannot increase backward across an event. The theorem therefore does not cover all ghost-parent or backward-expansion models. Silent boundaries, zero-time factorizations, rank-deficient routing, within-epoch rate collisions, arbitrary correlated boundary kernels and insufficient initial sampling are outside this sharp class. These conditions are sufficient, not proved necessary. Failure of a pairwise rank condition is not a nonidentifiability theorem for larger joint samples. The earlier fixed-family 55-site result still covers some coincident-rate configurations excluded here.

No stable numerical inverse, finite-locus-count guarantee, practical sequencing recommendation, empirical admission, MCMC convergence, full Lean verification, unrestricted biological-network identification or original G3/G4 closure is certified. Supplementary finite controls can be recorded separately; this acceptance rests on the audited full argument rather than on numerical examples.
