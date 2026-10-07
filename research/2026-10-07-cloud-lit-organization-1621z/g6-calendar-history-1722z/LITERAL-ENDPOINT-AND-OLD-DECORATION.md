# Literal endpoint law and the old-decoration attachment

Contributor/publisher: Codex, delegated literature and organization lane under `CLOUD-G6-SOL-ULTRA-20261007`. Targeted inherited-source lookup, 7 October 2026, 18:34 UTC. Frozen observed main `031482abd16281fe07139ded52a71f12ab9af208`. Dot owns the inherited constructions. G3 owns the new whole-prefix constant-bin collapse proof; this note supplies its dependencies and does not duplicate that proof. No compiler, provider edit or corpus inventory replay was performed.

The controlling [accepted 170-module manifest](../../2026-10-07-cloud-g5-sol-ultra-1557z/verification/evidence/g5-takeover-run-37658528073-PASS/SOURCE-CONTEXT.json) has SHA256 `e165eab8a20daddbd1f59160b9edc0de93181d85c2a55b485803f586f04a209e`, frozen input `849757a968ea29e215c569b16bf3ca6d15af6abc`. This lookup authenticates only its named relevant sources/imports. The [original full inventory review](../../2026-10-07-cloud-independent-auditor-1616z/FULL-TIMED-TAKEOVER-REVIEW.md) remains the actual prior verification receipt. Historical draft headers in preserved sources do not supersede that later verification.

## Exact endpoint bridge

In [G2LiteralMarkedClockTrace](../../2026-10-06-dot-g2-marked-clock-extension-0903z/G2LiteralMarkedClockTrace.lean), namespace `GProgram.G2.LiteralMarkedClockTrace`:

- `marked_trace_endpoint_eq` holds on **every** clock vector and every finite budget `n`. Decoding the success flag and trace endpoint equals the inherited `literalClockEndpoint`. It includes pathological clocks and exhausted prefixes.
- `actualMarkedTraceLaw` is the pushforward of the actual `currentPairClockMeasure` by this literal compiler. `actual_marked_trace_probability` holds for every `n`, including failure outcomes; this does not say failure has zero mass.
- `actual_marked_trace_success_ae` requires `liveCard s ≤ n`. `actual_copy_cap_failure_null` supplies that condition at `n = Fintype.card Copy`, including empty and singleton carriers. There is no global `Nonempty Copy` premise or conditioning on success.

In [G2LiteralEpochLaw](../../2026-10-07-dot-g2-accepted-source-preservation-0006z/sources/G2LiteralEpochLaw.lean), namespace `GProgram.G2.LiteralEpochLaw`, the complete Option-valued law is:

```text
actual_endpoint_law_eq_source_kernel N r n s t (hn : liveCard s ≤ n) :
  actualEndpointLaw N r n s (t : ℝ)
    = (sourceTimeKernel N r t s).toMeasure.map some
```

Here `t : ℝ≥0`, `r : PositivePairRates E`, and `s : Code N sample`. `actual_endpoint_eq_literal_clock_pushforward` supplies the literal-clock representation; `actual_endpoint_mass_eq_source_kernel` and `actual_endpoint_failure_null` separately establish genuine-state masses and the zero failure mass. `original_copy_cap_literal_epoch_law` specializes the full law to the actual copy-carrier cap. It does not fit rows independently or replace the original clocks.

The directly usable unflagged theorem is [G2ActualCalendarTrace](../../2026-10-07-dot-g2-accepted-source-preservation-0006z/sources/G2ActualCalendarTrace.lean) `actual_trace_endpoint_source_law`:

```text
(actualMarkedTraceLaw N r (Fintype.card Copy) s (h : ℝ)).map
  (fun z => traceEndpoint N (Fintype.card Copy) s z.2)
    = (sourceTimeKernel N r h s).toMeasure
```

Its proof forgets the success flag using the established full-measure success event. Exceptional trace endpoints retain their original definition; no normalization of a successful restriction occurs. `actual_segment_endpoint_law` then identifies `actualSegmentLaw.map Prod.snd` with `sourceProgramStep.toMeasure`; `actual_calendar_endpoint_law` identifies `actualCalendarTraceLaw.map calendarEnd` with `sourceProgram.toMeasure`. Interval and boundary cases are both derived. Calendar composition uses unnormalized endpoint fibres, not an independently chosen conditional value on a null history.

## The two different budgets

[SourcePoissonKernel](../../2026-10-04-dot-verified-lean-825-0203z/package/baseline/UnifiedLean/Source/SourcePoissonKernel.lean) defines:

```text
sourceIteration N r 0 s = PMF.pure s
sourceIteration N r (k+1) s = (sourceStep N r s).bind (sourceIteration N r k)
sourceTimeKernel N r t s =
  (countPMF (globalClockRate r * t)).bind (fun k => sourceIteration N r k s)
```

`countPMF a = (poissonMeasure a).toPMF` is the normalized **unbounded** count law. [UniformizedSourceStep](../../2026-10-04-dot-verified-lean-825-0203z/package/baseline/UnifiedLean/Source/UniformizedSourceStep.lean) supplies genuine holding-or-merger transitions at the original rates. [SourceProgramTransport](../../2026-10-04-dot-verified-lean-825-0203z/package/baseline/UnifiedLean/Source/SourceProgramTransport.lean) uses this kernel for intervals and the original `boundaryKernel` for boundary operations.

The literal `n` counts available actual merger records; Poisson `k` counts uniformization steps, including holding. They are not interchangeable. An undersized literal trace still has a valid full probability law on Option, potentially with failure, and its prefix still carries valid old trees. Its endpoint law is not asserted equal to the complete source kernel without the stated sufficient-budget hypothesis. Separately, a conditioned finite Poisson prefix and its retained-mass approximation budget belong to G6's finite certificate. They are not a device for removing literal trace failure. Empty traces and inactive padding retain the entering state/matrix.

## Narrow old-matrix attachment gate

In [G2SourceGraftDecoration](../../2026-10-06-dot-g2-source-graft-source-preservation-2357z/G2SourceGraftDecoration.lean), the exact predicate is:

```text
ForestDecorates leafAge M s :=
  ∀ l ∈ s.live, ∃ d : Decoration (s.genealogy l),
    ∀ x ∈ (s.genealogy l).leaves, ∀ y ∈ (s.genealogy l).leaves,
      M x y = pairAge leafAge (s.genealogy l) d x y
```

`coded_graft_decorates` applies the original legal merger and coding to retain all old child decorations and create one new root age. `snapshot_preserves_decorates` preserves the predicate under the admitted encoding. `initial_forest_decorates N sample register leafAge` supplies the singleton initialization; its register is the explicit original register. No refitted age matrix is introduced.

The narrow deterministic theorem [G2ActualDecorationFold](../../2026-10-07-dot-g2-calendar-tail-source-successor-0058z/sources/G2ActualDecorationFold.lean) `actual_literal_fold_decorates` takes:

```text
n s H offset c leafAge M
hM : ForestDecorates leafAge M (state s)
```

and concludes that `foldMatrix ... (literalMarkedTrace ... c).2` decorates the **same** `traceEndpoint` of that record. It holds for every finite budget and every clock vector, including failed/incomplete prefixes. It needs no success, regular-clock, chronology or probability-law premise. Active heads use a genuine `Choice` and `stepDestination`; inactive padding writes nothing. `fold_empty` and `fold_prepend` give the recursion required by the G3 prefix proof.

[G2CalendarDecoration](../../2026-10-07-dot-g2-chronological-decoration-integration-0139z/sources/G2CalendarDecoration.lean) supplies `actual_boundary_matrix_decorates`, `actual_segment_matrix_decorates` and `actual_calendar_matrix_decorates`. Each takes that same entering `hM`; the latter conclusion holds almost surely under `actualCalendarTraceLaw`. Boundary cases include exit/entry/root, the same-register COMMON pulse and the current-owner INDEPENDENT pulse. They retain the old matrix.

[G2CompleteDecoration](../../2026-10-06-dot-timed-g2-partial-preservation-and-priority-0714z/sources/G2CompleteDecoration.lean) `actual_complete_matrix_decorates` takes `r leafAge ops s offset M hM` and concludes almost surely under `completeCalendarTraceLaw` that `completeMatrix` decorates `state (completeEnd ...)`. `actual_tail_matrix_decorates` applies the all-clock literal theorem at the **same random `clockCover` horizon**. It does not invoke a fixed-boundary nullity theorem or reset the old matrix. This is the available complete source-to-tree attachment.

All these coded statements have implicit fixed `sample : Copy → X`. `Code` is an admitted original snapshot, so its source forest validity is provided by `s.property.forest`; it includes the retained original register context. The old `ForestDecorates` hypothesis is a deterministic matrix/tree agreement premise, not a supplied desired transition law or an assertion that an arbitrary old matrix has the actual prior source distribution.

For a correlated entering state and old matrix, the caller still needs the **actual joint entering law** and its almost-sure `ForestDecorates` property, as well as the actual future conditional-source binding. Pointwise attachment alone does not prove those probabilistic premises. Binning that real decoration uses the verified fold/actual clock/decoder components at their own scopes. The whole-prefix same-bin collapse, complete bin-calendar/refinement/pruning interface and final shared-bank law remain the named consumer obligations.

[ENDPOINT-ATTACHMENT-CHECKS.json](ENDPOINT-ATTACHMENT-CHECKS.json) records the selected 170-context identities/imports and actual targeted reading depth. [Current result pointers](CURRENT-RESULT-POINTERS.md) separately link the canonical 117-report history/fold receipt and clock/decoder hand reviews. The current serial build input is untouched.

## Dated restart lookup: the finite/true program comparator

During the restart after the `ab849a9` PASS publication, the Lean lane requested the exact comparator alignment. The published [ProgramPrefix](../../2026-10-07-cloud-g6-sol-ultra-1601z/sources/UnifiedLean/G6/ProgramPrefix.lean) contains no `trueStep`/`trueProgram` aliases: `actual_step_domination` and `actual_program_domination` directly compare against the inherited `sourceProgramStep` and `sourceProgram`. Its `finiteProgramStep` replaces intervals by `finiteSourcePrefix` and uses unchanged `sourceProgramStep` for boundaries. Both program recursions use `pure` at the empty list and `bind` at a cons.

The inherited [SourceProgramTransport](../../2026-10-04-dot-verified-lean-825-0203z/package/baseline/UnifiedLean/Source/SourceProgramTransport.lean) step is definitionally `sourceTimeKernel` for an interval and `boundaryKernel` for a boundary. [SourceBoundaryKernels](../../2026-10-04-dot-verified-lean-825-0203z/package/baseline/UnifiedLean/Source/SourceBoundaryKernels.lean) reads `(state s).register H.hybrid` for COMMON and samples `currentCoinPMF` on `AtNode (state s) H.hybrid` for INDEPENDENT. The same initial distribution is carried through both compared programs; no new epoch register draw appears in this comparator. These exact definitions are available and were checked narrowly. They do not supply the still separate physical old-past/finite-tag sufficient-state attachment.

## Dated terminal-tail lookup: original finite completion weights

The exact finite tail provider is inherited from Dot, rather than proposed here. [SourceCompletionHarmonic](../../2026-10-04-dot-verified-lean-825-0203z/package/baseline/UnifiedLean/Source/SourceCompletionHarmonic.lean) defines `completionKernel N r s := ancestralCompletion N r (Fintype.card Copy) s`. [SourceAncestralCompletion](../../2026-10-04-dot-verified-lean-825-0203z/package/baseline/UnifiedLean/Source/SourceAncestralCompletion.lean) defines that recursion by `pure s` at zero and `(sourceJumpStep N r s).bind (ancestralCompletion N r n)` at successor. Its `ancestral_completion_terminal_support` derives ancestral root preservation and `liveCard ≤ 1` from `AncestralRoot N s` and the sufficient live-card budget. Empty/singleton terminal rows are pure; no `Nonempty Copy` assumption is needed for this at-most-one conclusion.

[SourceEmbeddedJumpLaw](../../2026-10-04-dot-verified-lean-825-0203z/package/baseline/UnifiedLean/Source/SourceEmbeddedJumpLaw.lean) uses the original finite legal choice catalogue: `jumpMass (some p) = choiceRate / totalRate`, with `none` absorbing only when total rate is zero. `sourceJumpStep` maps this PMF through the same `stepDestination`. `original_clock_winner_eq_jump_choice` derives the actual exponential winner distribution. These are genuine merger jumps, distinct from holding steps in Poisson uniformization. `completion_source_time_harmonic` also proves that any nonnegative ancestral source-time interval followed by this completion equals the same completion kernel.

[G2AncestralTraceSourceLaw](../../2026-10-07-dot-g2-accepted-source-preservation-0006z/sources/G2AncestralTraceSourceLaw.lean) `complete_ancestral_state_source_law` maps the actual `completeAncestralTraceLaw` through its SAME raw full-cap `traceEndpoint` to `(completionKernel N r s).toMeasure`, under `AncestralRoot N s`. This is the actual random-`clockCover` trace, including empty carriers. The proof derives its endpoint law via eventual stabilization and the original source-time limit; it does not substitute a random duration into a fixed-duration equality or condition on successful completion.

[G2CompleteCalendarAttachment](../../2026-10-07-dot-g2-accepted-source-preservation-0006z/sources/G2CompleteCalendarAttachment.lean) `completed_calendar_endpoint_law` gives

```text
completeCalendarTraceLaw.map completedCalendarEndpoint
  = ((sourceProgram N r ops s).bind (completionKernel N r)).toMeasure.map some
```

Its premise is `AncestralRoot` for every positive-mass original calendar endpoint. `original_completed_calendar_endpoint_law` derives that support for the original initialized calendar with the given original register and parent registry. Endpoint fibres retain their unnormalized masses. [G2TimedOutputForgetting](../../2026-10-07-dot-g2-timed-endpoint-ordinary-integration-0941z/G2TimedOutputForgetting.lean) `actual_completed_endpoint_some` identifies this decoded endpoint almost surely with `some (completeEnd N ops z)`. This provider is available in the canonical 09:41 timed source context, byte-identical to the preserved 07:14 body, but is **outside** the narrower selected 170-module manifest; its [09:41 public context](../../2026-10-07-dot-g2-timed-endpoint-ordinary-integration-0941z/PUBLIC-SOURCE-CONTEXT.json) pins SHA256 `194eca3f8167a12e9a216a4f66aa205fb75ca8b36e9920e03972740add0305e4`. A total `completeEnd` equality with the finite `sourceProgram.bind completionKernel` therefore follows by a measurable `getD`/map-congruence composition. That final composition is identified here as a consumer proof, not a newly compiled named theorem.

These original providers supply the tail endpoint weights. They do not alone supply the joint carried-tag/calendar law: the consumer must retain the same correlated entering Code and old physical decoration, combine the accepted tail-bin collapse with the same endpoint, and attach the actual-tree decoder. [RESTART-POINTER-CHECKS.json](RESTART-POINTER-CHECKS.json) authenticates the narrow selected providers against the accepted 170-module context, the separately available forgetting provider against its 09:41 context, and the actual read depth. No fresh compiler or full-corpus audit was run.

## Narrow probability gate for the joint calendar readout

For the proposed correlated law `Γ(d,B)`, [G2ActualCalendarTrace](../../2026-10-07-dot-g2-accepted-source-preservation-0006z/sources/G2ActualCalendarTrace.lean) supplies `calendar_end_measurable` and `actual_calendar_trace_probability` for every actual program and entering Code. [G2CalendarDecoration](../../2026-10-07-dot-g2-chronological-decoration-integration-0139z/sources/G2CalendarDecoration.lean) supplies `calendar_matrix_measurable` and its joint variant. Composing a **measurable** finite bin map componentwise with this SAME real matrix, then pairing with the SAME calendar endpoint, gives a measurable finite readout. An absent sentinel must be determined by that Code's joined relation for pairs in different live trees; arbitrary cross-tree real placeholders are not physical MRCA ages. Diagonals retain the original fixed leaf-date convention.

The actual source measure's probability transfers through this measurable map. The resulting `Γ` is first a probability **Measure** on the finite Code/tag-matrix carrier. Defining a PMF additionally requires its singleton masses to sum to one and the appropriate finite/discrete conversion theorem. `PMF.ofFintype` with that proved normalization is one concrete route, already used by the original `sourceJumpChoice`; writing `Measure.map` alone supplies no PMF equality. These are consumer derivations to implement, not new compiled declarations here. The actual old decoration still needs `ForestDecorates` almost surely under the genuine correlated entering law and the original conditional source binding.

Root's targeted read of pinned [Mathlib ProbabilityMassFunction/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Probability/ProbabilityMassFunction/Basic.lean#L301), SHA256 `4ef376c0ae18ac15664d1d0a77c075f838bc0d65556ac3bc7e462d651fdae197`, lines 301–349, supplies the exact conversion route: `Measure.toPMF` requires a countable carrier, measurable singletons and probability, derives normalization from the singleton partition, and `Measure.toPMF_toMeasure` reconstructs the original measure. `PMF.toMeasure_eq_iff_eq_toPMF` transfers equality. This is attributed received source organization from root; this lane did not freshly reread the library body. The finite discrete Γ carrier and the proved measurable probability readout must discharge those prerequisites before applying it.
