# One supplied original calendar into the accepted private word consumer

Contributor: Codex / rust_implementation, 10 October 2026, 13:30 UTC.
Status: **sourced findings and concrete implementation proposal**. This note
performs no compiler, native execution, runtime promotion or source admission.
The companion [provider inventory](CALENDAR-TO-WORD-PROVIDERS-20261010T1330Z.json)
pins source bodies, attributed receipts and unchanged accepted Rust inputs.
It extends the earlier [program/calendar inventory](PROGRAM-CALENDAR-COMPOSITION-READINESS-20261010T1234Z.md)
with the generated-calendar consumer, rather than reopening completed G1/G2.

The next compatible component is a pure calendar-to-word producer followed by
the unchanged [finite word](../../design/WORD-REFINEMENT.md) and
[ancestral completion](../../design/WORD-COMPLETION-EXTENSION-20261010T1300Z.md)
consumers. It takes actual rational node ages and one original inverse-rate/
inheritance bank, derives the complete original agenda, and retains the exact
physical substitution relating every interval coordinate to that same bank.
It need not add another transition kernel or numerical probability solver.

## Governing original providers

| Provider | Exact definitions or results used |
| --- | --- |
| [G5CalendarRoutes](../../../2026-10-04-dot-complete-original-g1-1549z/src/G5CalendarRoutes.lean) | `Calendar` requires only strict target-age < source-age for every original edge occurrence; `Calendar.Active` uses the older-side half-open convention. |
| [SourceCalendarCompiler](../../../2026-10-04-dot-complete-original-g1-1549z/src/UnifiedLean/Source/SourceCalendarCompiler.lean) | `sortedOriginalDates`, `boundaryOperations`, `calendarTail`, `compiledCalendarProgram`, and actual compiled-program projection. |
| [SourceCalendarTiming](../../../2026-10-04-dot-complete-original-g1-1549z/src/UnifiedLean/Source/SourceCalendarTiming.lean) | Distinct dates are strictly increasing, consecutive durations are literal positive differences, the first date is the actual minimum, and the last original date is the supplied root age. |
| [SourceCalendarCompatibility](../../../2026-10-04-dot-complete-original-g1-1549z/src/UnifiedLean/Source/SourceCalendarCompatibility.lean) | `LocationInEpoch`, `EpochCompatible`, actual time-kernel support and initial compatibility, including dormant future sampled tip nodes. |
| [SourceCalendarPhysicalSupport](../../../2026-10-04-dot-complete-original-g1-1549z/src/UnifiedLean/Source/SourceCalendarPhysicalSupport.lean) and [SourceInitializedCalendar](../../../2026-10-04-dot-complete-original-g1-1549z/src/UnifiedLean/Source/SourceInitializedCalendar.lean) | Actual exits, entries and successive intervals preserve temporal placement and derive complete original-root support. |
| [SourceNaturalInitialization](../../../2026-10-04-dot-complete-original-g1-1549z/src/UnifiedLean/Source/SourceNaturalInitialization.lean) | Singleton copies at their original sampled tips, one original register draw, `naturalCalendarLaw`, and `natural_calendar_ancestral_support`. |
| [G7BoundaryPhasePermutation](../../../2026-10-09-dot-g7-natural-calendar-relabelling-1958z/G7BoundaryPhasePermutation.lean) | `exit_phase_perm`, `node_phase_perm`, and `program_append` permit separate finite phase permutations of actual Code endpoint PMFs. |
| [OriginalCalendarPattern](../../../2026-10-09-dot-g6-original-calendar-schema-2223z/OriginalCalendarPattern.lean) and [OriginalCalendarSchema](../../../2026-10-09-dot-g6-original-calendar-schema-2223z/OriginalCalendarSchema.lean) | Same weak age order including ties; actual calendar-schema instantiation; interval occurrence variables and literal shared physical coordinates. |
| [G6NaturalCellInverseRates](../../../2026-10-09-dot-g6-natural-cell-feasibility-1835z/G6NaturalCellInverseRates.lean) | `calendarOfAges`, `ratesOfInverse`, `constructed_pair_rate`, `inheritanceOfValues`, and exact hazard/inverse-bank rewriting. |
| [G7NaturalCalendarPolynomial](../../../2026-10-09-dot-g7-completed-calendar-polynomial-2330z/G7NaturalCalendarPolynomial.lean) and [G7CompletedCalendarPolynomial](../../../2026-10-09-dot-g7-completed-calendar-polynomial-2330z/G7CompletedCalendarPolynomial.lean) | Actual naturally initialized finite and infinitely completed selected laws on a supplied typed original source, one shared bank and one weak-order cell. |

The compiler body is SHA256
`9974446d99fa344593d294e315e349ab71fdbe7574e932bb8b1a16ee1b2369fd`;
initialized support is `47ea73231fbfa732495e4fc5f42f1374e2ef505bfe3d4073b6cc2bed3fcc5535`.
Phase permutation is `fea51a87be89f084752b22df8c52ae345515f1a0986cd0475d1a4be09453b4cf`.
Its [author attempts](../../../2026-10-09-dot-g7-natural-calendar-relabelling-1958z/BUILD-ATTEMPTS.json)
retain the failed first source and successful final `phase-perm-2` source;
the [separate parent review](../../../2026-10-09-dot-g7-natural-calendar-relabelling-1958z/PARENT-CALENDAR-RELABEL-REVIEW.md)
accepts the generated endpoint PMF scope. The current accepted semantic
191-module context also contains these unchanged bodies. These are attributed
machine-checked providers, not new execution by this Rust worker.

## Input carrier and exact chronology

**Proposal.** A private `CalendarRequest` fixes the existing original `Context`,
sample/global-label map, mode vector of length hybrid-count, terminal value,
word/provider limits, and one rational bank. Bank order is unchanged from the
natural-cell layout: every vertex age, every original edge inverse rate,
one ancestral inverse rate, then original hybrid gamma. Validate the entire
input before any operational budget: exact dimensions and registries, original
structural predicates, every strict edge inequality, every inverse rate > 0,
and 0 < original gamma < 1. Parent0 is false and parent1 is true.

The inherited general `Calendar` permits unequal tip ages and negative absolute
ages. This is supported by the actual dormant-node initialization proof, not
an inferred extension. Keep the first absolute date and all supplied ages.
Do not silently shift ages, force tip ages to zero, or insert an interval from
zero to the first date. The G6 natural-cell bank additionally requires every
declared leaf age = 0; report that computed specialization separately when
using a chart witness. This consumer does not establish chart coverage or
original graph-class admission merely by accepting a literal bank.

For sorted distinct ages `a[0] < ... < a[d-1]`, construct the following agenda:

1. At each date, list every original edge ID whose **source** has that age,
   followed by every original vertex ID with that age. Choose ascending IDs
   separately inside the exit and entry phases.
2. At the earliest date run its batch immediately. Before each later date,
   insert one `INTERVAL(slot)` of exact positive duration
   `a[slot+1] - a[slot]`, then that later date's complete batch.
3. Each original edge exits exactly once and each original vertex enters
   exactly once, including unsampled declared tips. Preserve distinct parallel
   occurrences even when both endpoints and dates coincide.
4. Do not insert holding time within one equal-age class or after the final
   root batch. Root completion is a separate infinite-time consumer.

Equal dates are allowed for incomparable vertices; strict edge ages prohibit
an ancestor/descendant tie. A valid typed source has at least one original date
because its root exists. The compiler's empty-list definition is totalization,
not an admitted empty graph or missing-time calendar.

The original uses `Finset.toList`, not ascending numeric IDs. Existing
`exit_phase_perm` and `node_phase_perm` discharge the semantic ordering debt
once the exact filtered lists are shown to be finite permutations and the
phase equalities are composed with `program_append`. This does not claim that
literal inherited/native words are byte-identical. Exits remain before entries;
the proofs do not commute their order-sensitive event logs or extract a timed
observation kernel. Select the least numeric vertex as the native date-class
representative and record its class. The inherited pattern uses
`Classical.choose` for representatives; any valid representative has the same
age, but a native-to-original representative/rank adapter is still required.

## Producer artifact and reuse of the current word consumer

**Proposed pure output:** retain the original request, sorted absolute dates,
each date's complete vertex/exit registries, native representative IDs, generated
letters with date/phase/occurrence provenance, and slots with exact younger/
older dates, duration and their word position. Number slots by increasing
interval occurrence position. This gives an explicit bijection to the source
`IntervalOccurrence` subtype, rather than treating word positions as slots.

Construct the child `source_word::Request` with `Initial::Natural`, the original
fixed modes, generated letters, `slots = d-1`, selected terminal and unchanged
word/provider limits. Do not accept caller-supplied letters, per-visit modes,
parent replacements or a caller assertion of root support. The child keeps its
once-drawn register, full ordered per-Copy selected views and literal range
witnesses; duplicate fibres are summed as in the accepted private consumer.

The shared variable registry is slot-major original edges followed by the
ancestral population, then original hybrid gamma, exactly the current word
bank. Initial registers and independent pulses use the same original gamma;
COMMON uses its stored entering bit and does not redraw or update it.
There is no LAW-v1 gamma alias and no marginalization of registers before
the declared final readout.

For each positive inverse rate `u[p]`, the physical rate is `1/u[p]` by
`ratesOfInverse`. Produce exact rational exposures

```
exposure[slot,p] = (a[slot+1] - a[slot]) / u[p]
X[slot,p] = exp(-exposure[slot,p])
ORIGINAL_GAMMA[h] = supplied_gamma[h]
```

The same `u[p]` serves every slot, and the same slot duration serves every
original population. Keep those equations as physical-substitution metadata.
Do not convert exponential values to rationals or invent independently chosen
slot survivals. The resulting rational formal table remains exact, while
physical evaluations generally are not rational. Numerical evaluation and
certified error enclosures are separate consumers. This agenda has no finite
post-root interval, so its ancestral finite-slot coordinates are inert on
naturally reached states; keep them in the original full bank.

`FULL_VIEW` supports empty Copy and retains its once-drawn register mixture.
`ANCESTRAL_COMPLETE` additionally requires nonempty Copy. Original calendar
support derives that every final supported copy lies at the actual ancestral
root. The unchanged native completion consumer still verifies every formal
supported endpoint witness before any completion budget. Do not replace that
check with the existence of the calendar-support theorem.

## Operational limits and deterministic refusal

Keep the existing graph-bank <= 32 and Copy <= 4 domain, original populations
`edge_count + 1 <= 32`, word <= 32, slots <= 16 and expanded variables <= 256.
For `d` distinct dates, the exact generated requirements are
`word = edge_count + vertex_count + d - 1`, `slots = d-1`, and
`variables = (d-1)*(edge_count+1) + hybrid_count`. Use checked integer arithmetic.

**Proposal:** after input validation, check generated word length, slot count
and variable count, in that order, before allocating a child request. Each
compiler limit yields a distinct operational `Unknown {kind,required,cap}`;
do not turn a valid supplied calendar into invalid input or scientific
exclusion. Ordinary `V=15,E=14,hybrids=0` has graph-bank30 but can have15
distinct dates, requiring43 letters,14 slots and210 variables. The word cap
alone rejects execution of that valid calendar. Even leaf-age-zero calendars
can exceed the existing letter allowance. No cap increase is proposed here.

Once compiled, call the unchanged child with its exact cumulative work and
provider limits. Retain child Unknown stage/kind/population metadata and
distinguish it from producer limits, malformed input and external process
failure. No partial coefficient table is returned on either Unknown. A pure
compiled skeleton can be retained as provenance; it is not a solved law table.
No new query accounting, resource shortcut or completion redraw is needed.

## Acceptance scope, remaining assembly and next action

The accepted current completion source has independent20/20 finite controls,
330 ordered completed views, old eight finite contexts plus two hybrid
contexts, and117 canonical public regressions. The universal typed effective
completion source `69dc295b...` now has a complete140-module kernel/audit PASS;
its actual typed fixtures/evaluator remain a separate receipt obligation.
The existing word/chosen-table and universal native encoder/dictionary
refinements remain separate. The original initialization, temporal support,
phase permutation and completed calendar theorems are already providers;
they are not reopened G1/G2 gaps.

Design should freeze the producer schema/limit order and input-only calendar
fixtures before an additive `source_calendar` module or isolated producer is
built. Meaningful controls are: a two-tip ordinary calendar; one singleton;
empty Copy FULL_VIEW; empty Copy completion refusal; equal-age incomparable
internal vertices; distinct parallel incoming occurrences in each fixed mode;
original gamma1/3; unequal and negative sampled tip ages; nonuniform inverse
rates across repeated original populations; same weak-order retiming; a changed
weak-order cell; zero/negative rates or endpoint gamma refusal; one reversed or
equal edge age; and the valid43-letter compiler Unknown. Compare the complete
generated agenda, every slot/exposure equation, then the full ordered finite or
completed table and literal witnesses using the frozen independent word
reference. Do not infer generic Lean equality from those finite comparisons.

The next reviewed build should be separate, preserve the accepted completion
inputs/binaries, and add no public operation, public pin or source-admission
promotion. The intended result is a supplied-calendar conditional law
component, not full source census, observation-menu admission, QE or G7
resource-optimal policy synthesis. Root owns application checkpoints;
integration owns every Lean execution. This note's own verification is only
source/receipt/hash/link inspection, recorded in its companion inventory.
