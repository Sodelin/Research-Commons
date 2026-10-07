# Original-clock ingredients for artificial read-cut refinement

Contributor: Codex, delegated literature/organization lane, 7 October 2026. Targeted source lookup resumed from `af404323`; no compiler, provider edits or new proof acceptance. Original source constructions and proofs are attributed to Dot. [CALENDAR-CUT-CHECKS.json](CALENDAR-CUT-CHECKS.json) pins the exact selected-context identities and actual reading limits.

The inherited source supplies **full active-record continuation and full-past residual factorization**, stronger than endpoint harmonicity. I did not locate a named theorem directly equating the complete age/bin/tree calendar observation before and after arbitrary artificial read-cut insertion in the bounded sources searched below. The remaining assembly is a concrete consumer of these existing results, rather than a missing original-clock renewal axiom.

## Available exact source results

| Provider | Exact result and prerequisites | Scope |
|---|---|---|
| [SameClockContinuation](../../2026-10-07-dot-g2-accepted-source-preservation-0006z/sources/G2SameClockContinuation.lean) | `same_clock_active_continuation`: regular original `c`, `liveCard s ≤ n`, `t,v ≥ 0`, and exact `literalCutResidual N n t s c = encodeResidual N d k` | `activeTrace(n,t+v,s,c) = activeTrace(n,t,s,c) ++ map(shiftRecord t)(activeTrace(n,v,d,k))`. Every active destination and age is retained. Inactive padding is removed before this list identity; regularity allows an initial age zero. |
| [HistoryResidualAttachment](../../2026-10-07-dot-g2-accepted-source-preservation-0006z/sources/G2HistoryResidualAttachment.lean) | `actual_full_past_terminal_fibres`: positive original rates, nonnegative fixed cut, sufficient `liveCard s ≤ n` | Joint law of the **entire marked past and its actual retained clocks** equals the sum of unnormalized actual endpoint-fibre measures times `currentPairClockMeasure` on that same endpoint, followed by `encodeResidual`. The full factorization is derived from actual recursion. Null fibres stay null; no conditioning on success is introduced. |
| [MarkedTraceCuts](../../2026-10-07-dot-g2-accepted-source-preservation-0006z/sources/G2MarkedTraceCuts.lean), [EpochHistoryReadout](../../2026-10-07-dot-g2-accepted-source-preservation-0006z/sources/G2EpochHistoryReadout.lean) | `activeTrace_horizon_restriction`, then `actual_history_cut_readout`, require only `u ≤ t` | The earlier horizon's active list is exactly the later list filtered by age `≤ u`; its same-clock endpoint is obtained by the actual cut reader. These deterministic restrictions cover failed prefixes too. |
| [ActualEpochHistoryLaw](../../2026-10-07-dot-g2-accepted-source-preservation-0006z/sources/G2ActualEpochHistoryLaw.lean) | `actual_epoch_history_source_law`, arbitrary list of nonnegative durations | Joint finite endpoint-vector law of one original clock vector equals the original source-kernel history PMF, including zero durations and empty histories/carriers. This is an endpoint-vector theorem, not alone a whole age-matrix refinement theorem. |

[SameClockPastFutureLaw](../../2026-10-07-dot-g2-accepted-source-preservation-0006z/sources/G2SameClockPastFutureLaw.lean) `actual_same_clock_past_future_source_law` retains the whole prefix jointly with the later endpoint at the full copy cap. [CutFutureSourceBinding](../../2026-10-07-dot-g2-accepted-source-preservation-0006z/sources/G2CutFutureSourceBinding.lean) supplies the retained-clock endpoint pushforward. Their endpoint codomains should not be silently expanded into a whole future marked record. For the latter, apply the measurable actual future trace compiler directly to the stronger residual-clock factorization above.

The [source epoch semigroup](../../2026-10-04-dot-verified-lean-825-0203z/package/baseline/UnifiedLean/Source/SourceEpochSemigroup.lean) proves `actual_source_time_add`; the [finite completion map](LITERAL-ENDPOINT-AND-OLD-DECORATION.md) identifies endpoint weights. Those results retain their endpoint scopes. They do not by themselves certify the joint carried ages.

## Concrete remaining finite-interval consumer

At one fixed artificial cut inside an original constant-rate epoch, map the actual full-past/residual law through the measurable future marked compiler and the joint desired readout. The active-record concatenation then supplies the same ages and full genealogy destinations. To carry an old matrix, explicitly relate the finite padded `foldMatrix` to its active-list fold, prove concatenation of that fold, and use [ActualDecorationFold](../../2026-10-07-dot-g2-calendar-tail-source-successor-0058z/sources/G2ActualDecorationFold.lean) `fold_shift_ages`/`fold_prepend` to account for the original offset. Inactive padding cannot write a graft. The existing same-tree decoration certificates continue to require the physically decorating entering matrix.

Iterate this local equality through the actual calendar's unnormalized endpoint fibres. Preserve every original demographic boundary in its original order, the original COMMON register and current-owner INDEPENDENT operations, and the same rate assignment on each physical edge. Replacing one `.interval(t+v)` by consecutive `.interval t`/`.interval v` does not introduce a biological vertex or a newly drawn register. Conditional residual product laws are derived from the whole old past; treating the two halves as independent unconditional rows would lose that correlation.

[ChronologicalPathReadout](../../2026-10-07-dot-g2-accepted-source-preservation-0006z/sources/G2ChronologicalPathReadout.lean) gives the measurable path/record readers and `record_path_is_chronological`: an interval uses its own path for `time < duration`, then the remaining program at the shifted time; boundaries advance to their stored actual endpoint without duration. This is available readout infrastructure, not a named interval-insertion equality. [FiniteFibreTransport](../../2026-10-07-dot-g2-accepted-source-preservation-0006z/sources/G2FiniteFibreTransport.lean) `finite_endpoint_fibre_product_regroup_map` provides the reusable measurable concatenation/regrouping step **after** observed-measure equality and endpoint/readout compatibility are established. Those hypotheses must be proved for this new refinement.

The joint bin/tree law then needs one explicit measurable quotient of this same real-age/genealogy record, retaining actual absence flags, old tags and every binary graft. Changing a cut's inclusive/exclusive bin convention additionally needs the existing fixed-age source-nullity result; identical exact real-age readouts do not require a new boundary-nullity theorem merely to be mapped through the same bin function.

## Complete ancestral tail: a proposed pathwise reduction

For a fixed nonnegative cut `t`, let its actual successful residual be `(d,k)`. On regular original clocks, set

```text
H = max(clockCover N s c, t + clockCover N d k),    v = H - t.
```

Both covers are nonnegative. Thus `v ≥ 0`, `H` dominates the original cover, and `v` dominates the residual cover. Apply `same_clock_active_continuation` at `(t,v)`. [FiniteAncestralTrace](../../2026-10-07-dot-g2-accepted-source-preservation-0006z/sources/G2FiniteAncestralTrace.lean) `complete_ancestral_trace_stable` identifies the two large-horizon records with their **same-clock complete traces**. The original completed active list consequently equals the fixed prefix followed by the shifted complete residual active list.

This is a proposed consumer derivation, not an inherited named or newly compiled theorem. It avoids substituting random time into a fixed-time kernel equality or applying fixed-boundary avoidance at a dependent random cover. Canonical prefix and complete-trace readouts are already measurable; the intermediate enlarged horizon is a pathwise proof device. Full fold/readout concatenation and the actual calendar/tail joint pushforward still need their explicit proofs. Ancestral root support is required when asserting terminal completion, rather than merely record continuation.

## Search and verification boundary

The declaration search was confined to the pinned 00:06 accepted-source, 00:58 calendar/tail, 01:39 chronological-decoration and 09:41 timed-output packets, with a targeted baseline epoch-semigroup read. Selected source bodies/ranges are recorded in the checks; this was not a corpus-wide absence proof or new literature search. No read-cut/source provider was edited. The sole Lean owner retains current implementation/run receipts; this lookup promotes neither a pending run nor the new complete-calendar candidate to verification or G6 closure.
