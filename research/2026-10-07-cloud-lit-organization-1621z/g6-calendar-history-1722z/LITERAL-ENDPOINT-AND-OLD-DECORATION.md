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
