# The same original clocks put the whole completion trace in the tail bin

Contributor: Codex, delegated G3/source-bridge lane, 7 October 2026. This is a separate hand corollary of the accepted literal-prefix collapse and the original dot clock-coordinate theorem. **HAND CANDIDATE; no new Lean implementation or compiler request.** The reviewed prefix proposition and its original standalone source remain byte-identical.

Fix an actual source state `s`, positive physical pair rates `r`, and the actual original-clock measure `currentPairClockMeasure N r s`. Let `T` be the last fixed calendar cut, `o ≥ T` the start age of the completion run, and `bin : ℝ → Tag` a readout with `bin a = b_tail` whenever `T < a`. No condition on inactive padding or on `bin T` is needed. Write

    z(n,H,c) = (literalMarkedTrace N n H s c).2
    e(n,H,c) = traceEndpoint N n s z(n,H,c).

Then on one full-measure event of original clock vectors, simultaneously for **every** finite merger budget `n`, every real horizon `H`, and every entering tag matrix `M`,

    foldTags N bin n s o M z(n,H,c)
      = tagUpdate N s e(n,H,c) b_tail M.                 (T)

The endpoint in (T) is the SAME record's full genealogy Code. Old joined-pair tags and diagonals are preserved; new joined pairs receive the tail tag; pairs still separate retain their old entries. The result includes incomplete prefixes and failed completion flags. It does not identify endpoint trees with their pair partitions.

**Proof.** The original `GProgram.G2.ClockBoundaryNull.actual_clock_strictly_positive` gives one almost-everywhere event

    ∀ p : Choice N s, 0 < c p.

Its body combines actual regular/nonnegative support with simultaneous avoidance of the fixed coordinate zero. Fix a clock vector in this event. The original `literal_active_time_is_coordinate` applies to every `n,H` and active index `i` of `z(n,H,c)` and supplies an ORIGINAL initial-state choice `p` with recorded relative age `z_i.age = c p`. This statement follows from the unchanged actual residual subtraction and prepend recursion; recursive waiting increments are not substituted for original coordinates. Consequently every active absolute age satisfies

    o + z_i.age = o + c p > o ≥ T.

Every active readout is therefore `b_tail`. The parent's `bin_constant_active_fold` changes this same record's fold to the constant-tail-tag fold; the [accepted entire-prefix proposition](PROPOSITION-AND-PROOF.md) then changes that fold to its actual persistent-endpoint update. Neither step changes flags, destinations, old tags or topology. Inactive padding writes nothing. This proves (T) on the single positive-coordinate event. Arbitrary horizons are quantified only after fixing `c`; no intersection of horizon-specific probability-one events is used. ∎

In particular (T) can be evaluated at **any horizon selected from the SAME clock vector**, including

    H(c) = (clockCover N s c : ℝ)
         = Σ p : Choice N s, |c p|,

and at `n = Fintype.card Copy`. By the original definition this is precisely `completeAncestralTrace N s c`. The argument uses only a strict lower bound on active ages. A horizon equal to an original coordinate causes no difficulty; avoidance of a fixed horizon boundary supplies no extra premise here. Empty choices give a vacuous positive-coordinate event and no active entries, so this statement needs no ambient default or nonempty Copy assumption.

For a measurable finite cut-bin readout, this pointwise clock result has a measurable full-cap record formulation: the fold, endpoint projections and finite tag update are measurable, and `complete_ancestral_trace_measurable` defines the actual pushforward `completeAncestralTraceLaw`. Thus, almost everywhere under that **actual** law,

    foldTags N bin (card Copy) s o M z.2
      = tagUpdate N s (traceEndpoint N (card Copy) s z.2) b_tail M.

This is a hand pushforward corollary, not an additional compiled declaration. The full-cap choice is needed here only to match the existing complete-trace definition; the original-clock formula (T) holds at every budget. It asserts no completed fixed-time `sourceTimeKernel` law at a random duration by substituting into a fixed-duration theorem.

The remaining complete-calendar attachment must retain the actual random entering Code and its correlated past decoration. The original `GProgram.G2.CompleteDecoration.actual_tail_matrix_decorates` already obtains genuine tail real-age decoration from `actual_literal_fold_decorates` at the SAME `clockCover`. Its `actual_complete_matrix_decorates` attaches the SAME complete matrix to the SAME complete endpoint under `completeCalendarTraceLaw`, by the actual conditional calendar/tail fibre construction. These are precise providers for the parent's next consumer: combine them with the verified same-record bin quotient and (T), prove the joint measurable calendar readout, and then attach the finite-tag decoder to the actual tree. A supplied arbitrary `M` alone has no physical old-decoration guarantee. Original G3 whole-fibre exact recognition and the full G6 endpoint remain open.

The exact original source bodies, later inspection commit, hashes and Git blobs for this corollary are recorded separately in [TAIL-SOURCE-INPUTS.json](TAIL-SOURCE-INPUTS.json); the seven-input prefix manifest is preserved unchanged.
