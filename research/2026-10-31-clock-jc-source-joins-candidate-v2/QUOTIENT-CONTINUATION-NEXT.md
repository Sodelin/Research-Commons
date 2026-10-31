# Exact continuation-invariance join after weighted renewal acceptance

23:20 UTC, 30 October 2026. Derivation plan, NOT a Lean theorem or accepted proof. No new compiler task.

## Needed theorem (single actual epoch)

For two current codes s and s' of the SAME original graph/rates, require equality of their current original-copy descendant partitions and equality of copyLocation s x and copyLocation s' x for every original labelled copy x. Then prove, for every finite fuel n, horizon t>=0, and the same finite locus charge columns q,

    actualLocusWeight N r L q n s t = actualLocusWeight N r L q n s' t.

This theorem concerns the actual shared-locus occupation expectation inside an epoch. It does not equate raw genealogies, histories, ancestor IDs, registers, or arbitrary future routing laws. No assertion about P or graph-wide population coding is needed for this same-graph statement.

## Applicable route using actual suppliers

1. Base fuel zero: the original literal compiler succeeds exactly on the original no-event clock set; occupation is k_s*t. Recover exp(-(C_s+k_s)*t) from the existing no-event mass law, rather than assuming a killed semigroup.
2. The partition identity already gives k_s=k_s' for the same complete labelled charge columns.
3. Use the existing actual-population selected-block pair bijection with keep=univ to pair each current ordered root choice with the same ordered pair of descendant blocks in s'. Equality of original-copy locations gives equality of its original population and pairRate/2. This must also establish C_s=C_s'.
4. The actual merge block-update identity and merge_population_preserved establish that paired destinations satisfy the same quotient relation. Then the induction hypothesis identifies their future W_n at every remainder horizon on the restricted exponential holding measure.
5. Apply the actual weighted renewal and reindex the finite choice sum via that genuine bijection. No independent genealogy is redrawn between site columns.

The two orientations of one current block pair can then be compared using this theorem at their actual destinations. Equal endpoint partitions/populations ALONE were not sufficient; the induction supplies their equal continuation weights. Only after this theorem may their two half-rates be aggregated into one unordered path branch for b=choose(n,2).

## Boundary and state-count limitations

This single-epoch statement cannot discharge arbitrary hidden-register future boundaries. Whole-calendar continuation needs the admitted polynomial current-block Markov boundary kernel, or a separately proved exact marginalization/irrelevance theorem. The original contract requires that admission and excludes hidden-state routing. P bounds active populations PER EPOCH, so a graph-wide arbitrary populationIndex does not establish S=Bell(n)P^n.

Root-tail absorption and finite-clock/full-fuel passage remain distinct. Strict Calendar.edge_older does not admit the hand zero-edge/atomic cases; those need exact separate finite-schedule admission/contraction/composition. No limit argument or broadened source claim is licensed.

## Essential strengthening before finite-calendar assembly

The draft scalar `actualLocusWeight` has terminal payoff 1. Its within-epoch equality is useful, but multiplying such scalar epoch expectations would LOSE dependence on the actual exit partition/populations and would be scientifically wrong. For the finite-calendar representation, lift the SAME original trace weight to the endpoint-resolved killed kernel by multiplying it by the indicator that the actual `traceEndpoint` has the specified quotient exit state. Equivalently prove the renewal with an explicitly quotient-measurable terminal payoff, then specialize to those finite exit-state indicators.

The original prepend_trace_endpoint theorem already supplies the correct endpoint recurrence. The no-jump term becomes the same exponential factor times the current state's exit indicator; the future term retains that SAME final exit indicator. This is not a replacement observation channel: it is the actual occupation measure resolved by its actual terminal source state, needed to compose the original routing kernel. The shared-tree locus Fourier identification remains the terminal scientific observable.

Do not claim that the present scalar renewal alone proves a composable killed-calendar kernel, equal arbitrary boundary continuations, or the S-dependent state/path bound. Implement this endpoint-resolved strengthening after the existing measurable-weight and kernel compilation diagnostics, rather than building another untested chain now.
