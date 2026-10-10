# One supplied rational original calendar

Codex design lead, 10 October 2026. **Reviewed private implementation contract,
stage 1**: derive a complete calendar agenda and physical substitution, then call
the existing [word consumer](WORD-REFINEMENT.md) and [completion consumer](WORD-COMPLETION-EXTENSION-20261010T1300Z.md).
This adds no public RC1 operation, independent survival image, scientific source
admission or observation-fitting claim. The [source readiness review](../rust/notes/CALENDAR-TO-WORD-READINESS-20261010T1330Z.md)
and its pinned provider inventory supply the governing original definitions.

## Exact private input

`source_calendar::Request` and each input-only fixture have exactly these fields:

```
context, ages, inverse_rates, original_gamma, common, terminal,
compiler_limits, word_limits, provider_limits
```

`context` is the unchanged original `Context`: `vertices,root,edges,leaves,hybrids,local_samples,global_labels`.
All vertex, edge-occurrence, hybrid-registry and local Copy IDs retain their
original meaning. Validate the existing RootedBinary predicate, graph-bank <=32,
Copy <=4, injective uint64 global labels, and exact hybrid parent registry. No
cofacial, cut-child, planarity or leaf-age-zero premise is added to this consumer.
This finite structural check does not establish the original outer source census.

`ages` has V entries; `inverse_rates` has E+1 entries (ascending original edge
IDs, then the one ancestral population at the original root); `original_gamma`
has H entries. Each is a canonical reduced `p/q` string with positive denominator,
including `0/1`. Rational arithmetic has arbitrary exact precision; no hidden
256-bit bound is introduced. Derived durations and exposures stay exact.
Every inverse rate is positive, every gamma is strictly between zero and one,
and `ages[target(e)] < ages[source(e)]` for every original edge occurrence.
Negative absolute ages and unequal sampled tip ages are permitted. `common`
has exactly H Boolean entries, true for COMMON, false for current-owner INDEPENDENT.
Original gamma is P(true)=P(parent1); it is not the frozen LAW-v1 parent0 coordinate.
`terminal` is `FULL_VIEW` or `ANCESTRAL_COMPLETE`. Completion rejects empty Copy
with the existing `SOURCE_WORD_COMPLETION_EMPTY_COPY` before any operational cap.

Validate every input field, bank, graph and budget shape before compiling.
Malformed fields/contexts use `SOURCE_CALENDAR_INPUT`; dimension mismatch uses
`SOURCE_CALENDAR_DIMENSIONS`; non-strict edges use `SOURCE_CALENDAR_STRICT_EDGE`;
nonpositive inverse rates use `SOURCE_CALENDAR_INVERSE_RATE`; noninterior gamma
uses `SOURCE_CALENDAR_GAMMA`; malformed limits use `SOURCE_CALENDAR_LIMITS`.
Private probes retain established InvalidInput stderr/exit1/no stdout behavior.
There is no new generic JSON parser claim merely because fixtures echo JSON.

`compiler_limits` has exactly `word_length,slots,variables`, each an integer in
0..32, 0..16, 0..256 respectively. Above-hardmax values are InvalidInput, not
silently clamped. `word_limits` is the unchanged seven-field word Limits.
`provider_limits` has exactly `epoch,boundary,completion`; their fields/defaults are:

| Carrier | Fields and default caps |
|---|---|
| word | initial_assignments16, initial_terms256, queries4096, branches65536, term_products262144, destinations4096, terms65536 |
| epoch | calls4096, destinations4096, lifted_terms65536, branches4096, term_products65536 |
| boundary | assignments16, destinations16, term_contributions128 |
| completion | calls4096, destinations4096, lifted_terms65536 |

All word/provider caps are nonnegative uint64 values. Arithmetic counting work,
requirements and array indices is checked; integer overflow is an explicit
internal resource/representation error, never wraparound or a partial table.

## Agenda and one physical bank

Sort and deduplicate all original vertex ages into `a[0]<...<a[d-1]`.
At each date emit ascending original edge IDs with source age equal to that date,
then ascending original vertex IDs with that age. Before each later date emit
`["INTERVAL",slot]`, slot=its date index minus one. Emit no leading interval,
no holding time inside a tied cohort, and no finite interval after the root.
Every edge exits once, every vertex enters once, including unsampled tips;
parallel edge occurrences stay distinct. Keep absolute dates without shifting.

The child is the unchanged word Request with this context, `initial:{kind:NATURAL}`,
original fixed modes, slots=d-1, generated letters, terminal and word Limits;
pass through the original provider limits. Natural initialization draws all
2^H registers once, including empty Copy, with raw3^H term contributions. COMMON
uses that stored bit; INDEPENDENT uses fresh current-owner assignments without
changing the register. The child retains full ordered selected views and actual
Snapshot witnesses. Its completion root-support scan remains before completion
query limits; the typed calendar theorem does not bypass this executable check.

The child variable bank is slot-major original E then ancestral A(root), followed
by the original hybrid gamma variables. For each survival variable produce
`X[slot,p]=exp(-duration[slot]/inverse_rates[p])`; for gamma produce the original
supplied value. The same inverse rate serves every slot. Exponential values are
not converted into rational probabilities. This formal polynomial table plus
exact substitution is a supplied-calendar component, not a calibrated physical
observation law. Finite ancestral slot coordinates are retained even though the
natural agenda reaches A(root) only after its last finite interval.

## Pure producer and output schema

Compute exact requirements before allocating the child:

```
word_length = E+V+d-1
slots = d-1
variables = (d-1)*(E+1)+H
```

After all validation, check word_length, slots, variables in that order against
their respective compiler caps. A valid calendar needing too much work yields
CompilerUnknown. For example V15/E14 with15 distinct dates needs43 letters,
14 slots and210 variables, while its original graph bank is30. Do not classify
that source as invalid or excluded.

Pure compile returns Generated or CompilerUnknown; solve wraps the unchanged
word Decision. The private JSON base fields are exactly:

```
schema:"source_calendar_probe_v1", fixture, request,
source_admission_verified:false,
requirements:{word_length,slots,variables}, status
```

Successful compilation retains `agenda` with exactly these fields:

```
dates:[p/q,...],
cohorts:[{date_index,representative,vertices:[v,...],exits:[e,...]},...],
word:[[tag,index],...],
origins:[{date_index,phase,index},...],
slots:[{slot,word_position,younger_date:p/q,older_date:p/q,duration:p/q},...],
physical_coordinates:[{variable:[...],kind:"EXP_NEG"|"RATIONAL",argument:p/q},...],
leaf_age_zero:bool
```

The cohort representative is its least numeric vertex; vertices and exits are
ascending. `origins` is position-aligned with word: phase is `EXIT`, `ENTER` or
`INTERVAL`; index is the original ID or interval slot, and interval date_index
is its older cohort index. Slot word_position points to its unique interval
letter; younger_date/older_date are absolute rational dates. physical_coordinates
is position-aligned with the full child variable registry: EXP_NEG argument is
the exact positive duration/inverse exposure; RATIONAL argument is original gamma.
leaf_age_zero reports the G6 natural-cell specialization for every declared leaf.

TABLE adds `agenda` and `word_result`, the unchanged complete
`source_word_probe_v1` envelope using the same fixture name and derived child
request. Word UNKNOWN adds `agenda,word_result,unknown_scope:"WORD",consumer_population`;
status is UNKNOWN and consumer_population is null or the actual `["E",e]`/
`["A",root]` from the original child Limit. This outer field retains population
metadata omitted by the older private word renderer without changing that schema.
No rows or work appear inside an UNKNOWN child. Compiler UNKNOWN adds only
`unknown_scope:"COMPILER",limit:{stage:"COMPILER",kind,required,cap}`; kind is
word_length, slots or variables. No partial agenda, child or table is emitted.
Operational UNKNOWN is distinct from invalid input and external process failure.

Private fixture JSON uses fixed field order as displayed, no optional/unknown
fields, exact integer and rational values, one compact JSON object and trailing LF.
Independent fixture checks compare every field and coefficient, allowing only
different admitted positive-support Snapshot representatives for an identical
full selected view. This private comparison is not a new Lean/Rust public-byte
parity or universal parser/serializer refinement claim.

## Existing proofs, acceptance and outstanding bridges

`SourceCalendarCompiler` (9974446d...), `SourceCalendarTiming`, initialized support
(47ea7323...), natural initialization and completed-calendar providers already
prove the typed source agenda/physical endpoint semantics. `G7BoundaryPhasePermutation`
(fea51a87...) permits separate exit and entry list permutations, composed with
program_append. Bind ascending IDs to those finite permutations; do not reprove
commutation, swap phases, or infer timed-history equality from endpoint PMFs.
The native least representative and interval-slot numbering still need their
explicit original date-class/occurrence bijection refinement.

The input-only fixture freeze and independent reference must precede Rust source
mutation. Acceptance compares all cohorts/letters/slot identities/exposure
equations, complete ordered tables/registers/range witnesses/work, invalid-input
priority, distinct compiler and child UNKNOWN metadata, and the preserved117
public regressions if executable bytes change. Reuse the frozen word spectral
reference; it is independent of native history/lift recurrences. Existing
original epoch9, boundary12 and direct completion6/257 comparisons are accepted.
Universal native carriers, original chosen single-step polynomial identity,
original initialized whole-word coefficient composition and generated-calendar
refinement still require separate kernel/derivative evidence.

Keep the commensurate-rational primitive survival-bank substitution as a sourced
follow-up proposal. This stage does not implement it, numerical exp evaluation,
marked-time observations, source census, QE, inference, or policy synthesis.
