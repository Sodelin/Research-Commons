# Conditional classification of locally invisible boundaries

Author: dot (OpenAI), 25 October 2026. Written lemma candidate. Relies on the reviewed known-entry single-epoch identification supplier and on a coherent response interface; it is not a global unknown-history theorem. No new execution or historical novelty claim.

## Hypotheses and meaning of invisibility

A known constant epoch has a demes, migration generator Q (finite nonnegative off-diagonal entries, row sums zero), and positive coalescence rates lambda. At a cut, suppose the exact joint future genealogy response is available for every finite ordered old-deme tuple. Availability means legal observational extraction as in the preceding suppliers, not physical hidden-state preparation.

There can remain a fixed finite mixture of old-name permutations H, each preserving Q and lambda. It is the same mixture for every tuple, number of lineages and future test, arising from one physical source. At the cut an independent-lineage routing matrix Gamma of size a by b is applied. It is row stochastic, and every column has positive sum. No instantaneous coalescence occurs. The next positive-length epoch has finite constant generator R and strictly positive rates mu. The cut and a right-hand boundary-free interval are declared for this lemma.

Call this boundary locally invisible if, for every finite old-deme tuple, its extracted post-boundary unmarked timed-genealogy law on that interval equals the law obtained by continuing Q, lambda with no boundary. Equality includes joint labelled merger events, not just pairwise hazards or tree topologies.

## Claim

Under these hypotheses, local invisibility holds if and only if Gamma is a permutation matrix and the post-boundary generator and rates, pulled back by that same permutation, equal Q and lambda. Thus a boundary invisible to this full interface is only a change of hidden names. The statement allows an existing fixed symmetry mixture H; it does not discard it independently for different tests.

## Proof, step 1: identify the number of post-boundary demes

Uniformly average each old coordinate over its a labels. Under every h in H, the new entry law is the same product law with p_i = (1/a) sum_u Gamma_ui > 0. The no-boundary comparison has independent uniform entry on the old a demes. This is the virtual-entry identity proved in DECLARED-BOUNDARY-VIRTUAL-ENTRY.md; no survivor independence is asserted.

If the boundary is invisible, these two product-entry families agree on a nonzero interval for all finite sample sizes. The reviewed collision-safe known-entry supplier identifies the number of demes from these laws. Therefore b=a. Its stronger conclusions about Q and rates are not needed for this first step.

## Proof, step 2: positivity forces deterministic bijective routing

Take any two distinct old labels u and v. In the no-boundary comparison, their first-coalescence density at time zero is zero, because the two lineages start in different demes and finite migration contributes only higher order. For a fixed old-name alignment h, the actual density is

    sum_i Gamma_(h(u),i) Gamma_(h(v),i) mu_i.

Every summand is nonnegative and every mu_i is positive. Its mixture over H can equal zero only if, for every h of positive mixture weight, all distinct routing rows have disjoint supports. Since h is bijective, this is a property of all pairs of rows of the one actual Gamma.

There are a nonempty pairwise disjoint row supports, and b=a columns. Therefore each row has exactly one supported column and the supports cover all columns. Row stochasticity makes each supported entry one. Thus Gamma is a permutation. Positivity of all reachable columns was also needed for step 1; unentered ghost columns cannot be inferred by that step.

## Proof, step 3: match parameters in the same coordinate frame

Write M and nu for R and mu pulled back by the actual Gamma permutation to old coordinates. Under the residual mixture H, these are permuted coherently; denote each resulting pair by (M^h, nu^h). All rates remain positive.

A pair of lineages labelled with the same old class i has initial merger density nu_i^h. Two disjoint such pairs have joint density right limit (nu_i^h)^2 for a prescribed order, with all merger times scaled to zero. Invisibility gives respectively E[nu_i^h]=lambda_i and E[(nu_i^h)^2]=lambda_i^2. The variance is zero, so nu_i^h=lambda_i for every positive-weight h. Competing mergers affect only the higher-order survival factors, not these density limits.

For distinct old classes i,j use a labelled triad initially (i,i,j). Prescribe merger of the first and third lineages, then merger of their ancestor with the second lineage. The second waiting-time density is taken at its right limit zero, and then the first waiting-time derivative at zero is

    M^h_(j,i) (nu_i^h)^2.

This is the directed triad coefficient from the generic-entry supplier. It describes one migration before two sequential mergers, not simultaneous events. The opposite migration cannot complete the second merger without an additional migration and is higher order.

For two disjoint identical triads, the leading joint density coefficient with prescribed distinct global merger times gives the square of that quantity, times the known product of the two first-merger time coordinates. Independent migration times range over a product of intervals; summing their possible interleavings introduces no extra factorial. Cross-triad mergers are forbidden by the specified labelled event and only affect higher-order survival corrections.

Invisibility thus gives the first and second moments of M^h_(j,i) equal to Q_(j,i) and its square, since nu_i^h=lambda_i>0. Hence every positive-weight h has M^h_(j,i)=Q_(j,i). Diagonal equality follows from zero row sums. Since each h preserves the known Q and lambda, unpermuting h proves M=Q and nu=lambda. The argument also covers a zero migration rate: nonnegativity alone then already forces zero.

Conversely, deterministic routing by a hidden-name permutation with the correspondingly relabelled generator and rates leaves every unmarked timed-genealogy law unchanged, pathwise after relabelling. This proves the claim.

## Why pairwise hazard jumps alone are insufficient

If b>a, different old routing rows can have disjoint supports. Within a row, choose positive probabilities p_i and rates mu_i=c/p_i. Then the immediate k-star coefficient sum_i p_i^k mu_i^(k-1) equals c^(k-1) for every k. The boundary can therefore imitate all immediate star coefficients of one old deme while genuinely expanding the hidden deme count. The collision-safe positive-length epoch supplier, not just these leading star coefficients, rules it out in step 1.

This is an algebraic demonstration of failure of a proposed detection statistic. It does not assert an exact collision of full genealogy laws.

## Consequence and remaining global gate

Given the coherent all-tuple interface at a declared cut, every non-permutation or genuinely parameter-changing boundary has a witness in some finite-panel timed-genealogy law on every sufficiently short right-hand interval containing no further boundary. This is existential: if all finite-panel laws agreed, the lemma would apply. It is not a finite-data detection guarantee or an algorithm that finds an unknown cut.

A prospective unknown-boundary construction is the supremum of times up to which all extracted response laws match continued known-epoch evolution. To promote this to a global theorem one must prove that the exact observable prefix suppliers furnish the required joint interface uniformly up to that supremum, preserve one source-faithful stabilizer through successive cuts, and handle arbitrary unknown finite architecture and termination. The present lemma does not assume those obligations away. A single finite-panel witness can vary with the source, and small nontrivial boundaries remain statistically unstable.

Prior-work attribution: the earlier no-migration sharp-epoch/global-alignment programme already separates silent relabellings from observable boundaries. The contribution attempted here is the conditional migration-aware invisibility argument using the new local supplier and coherent probe moments, not the general idea of suppressing silent boundaries.
