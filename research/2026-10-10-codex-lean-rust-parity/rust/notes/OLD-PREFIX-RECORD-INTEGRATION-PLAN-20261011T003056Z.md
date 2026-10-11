# Minimal private initialized-prefix record plan

Contributor: Codex Rust implementation role; 20261011T003056Z. Source/body review only:
no code, build, compiler, native solver, reference producer or new test was run.
The adjacent JSON authenticates existing text inputs and the accepted 1504 source
context. Original source headers may retain historical unchecked labels; context
acceptance is separately pinned. The preserved 68e/fcad prefix/factorization
contracts are proposals, not newly accepted roots in this note.

The smallest useful consumer is a **natural initialized literal endpoint record**
for one supplied fitted bank, stopped immediately before its named COMMON hybrid.
It returns the entering Code and every ProgramStep endpoint. It does not return a
timed merger trace, completed rooted law, arbitrary external Old initializer or
full native/source refinement claim. A pure later reader can inspect the entire
record; retaining that record closes the information loss in final-only output.

## Existing transitions and the precise missing hook

Reuse the immutable `source_fit_bank::Bank`: same Context, original edge/hybrid
occurrences, sample/label maps, ages, fixed modes and slot-major survival/original
Gamma bank. Original Gamma is P(true/parent1)=1-old g; stored bits and parent
occurrence IDs are unchanged. No independent per-step or per-copy coin is drawn.
The first private API accepts only a natural bank and a prefix of its agenda;
conditional warm starts, masks, ancestral completion and future-context laws are
separate interfaces.

`source_word::word_row` with empty word, `Initial::Natural`, `FullView`, and the
same declared slot bank can supply its existing one-time initializer. At this
singleton initial carrier, distinct full registers remain distinct keys. For
conditional steps reuse `source_boundary::boundary_row`,
`source_population::population_row`, and epoch `restrict_panel`/`join_panel`.
Internal CTMC merger paths with the same endpoint may sum within one epoch:
`historyLaw` records one Code after each ProgramStep, not every merger time.

There is a real obstruction to merely recording existing `word_row` witnesses:
`source_epoch::full_row` aggregates literal population destinations into
`selected_panel` before gluing, then aggregates joined rows by `selected_key`.
`source_word::accumulate` does the same across stages. Each key keeps one literal
range witness. That operation can lose a representative/ancestor choice and
cannot represent all literal initialized records.

The minimal later source derivative is a **shared conditional literal-row hook**:
retain all canonical literal destinations keyed by `snapshot_key` through the
existing population/panel product, expose them before selected aggregation, and
reuse the same word resolution/variable embedding/register checks. The existing
selected endpoint API stays unchanged. This needs reviewed edits to shared epoch/
word internals; none are authorized or made here. It is an observation point in
the existing algorithm, not another calendar, clock, route or coefficient engine.

Reuse's bounded accepted-source search found no theorem recovering Code from
selectedView. `G7EncodedMergerSupport` proves actual encode image and liveSome/
deadNone preservation; it does not choose a representative. An induction proving
that naturally reachable representatives are the leftmost leaves of their
ordered trees could support an optimized selected-only implementation, followed
by an explicit injectivity proof. Neither SourceValid nor Encoded supplies that
lemma today, so it is not an assumption of this plan. Existing epoch/word
coefficient identities are selected-carrier identities and do not automatically
bind this proposed full literal hook to the full Code PMF.

## Proposed private API and lossless storage

Pseudotypes, not an implemented or frozen public grammar:

```rust
prefix_record(bank: &Bank, spec: &PrefixSpec) -> Result<RecordDecision, RecordError>
PrefixSpec { exact_order: Vec<Symbol>, stop_before: OriginalHybridId,
             limits: RecordLimits, provider_limits: ProviderLimits }
StateId(u32); PathId(u32);
HistoryNode { parent: Option<PathId>, state: StateId }
RecordRow { leaf: PathId, polynomial: Polynomial }
RecordTable { bank_binding, variables, exact_order, stop_before,
              snapshots: Vec<Snapshot>, nodes: Vec<HistoryNode>, rows, work }
```

Each initial root node contains the entering literal Snapshot, including its
full original V register. A path for k letters has k+1 snapshots. Intern snapshots
by exact `snapshot_key`; intern nodes by **(parent PathId, destination StateId)**.
Two paths ending in the same Code remain distinct whenever any earlier endpoint
or their entering Code differs. Coefficients may combine only for the same whole
endpoint sequence. Cache conditional provider results by stage/symbol/current
StateId and the immutable bank/limits; reuse computations without merging paths.

Use the existing exact Polynomial bank for every path and multiply/normalize
existing conditional rows. Never infer a probability at the supplied point by
rounding logs or fractional roots. The designated private seed is the initial
register bit at the original hybrid vertex. Verify that every recorded endpoint
preserves the whole register; COMMON uses that same bit for all current owners.

A subsequent pure readout may pair that seed with the record obtained by erasing
only its private register coordinate in the entering Code **and every endpoint**.
Any aggregation must use the seed plus the whole erased path, not just its last
state. No independence flag is accepted. The accepted source theorem derives the
seed/product statement from actual natural initialization and NoPrivateWordRead;
this API does not promote its operational record check to that typed theorem.

## Exact order is an input relation, not an endpoint permutation

Validate all supplied letters against this same bank's cohorts: every original
exit/entry occurrence, original vertex/edge/hybrid map, slot number/duration,
date order and exit-before-entry phases must agree. The full ordering metadata
is retained even when the consumer stops at an interior node of a tied cohort.
No invented leading/trailing interval or interval between same-date nodes is
inserted. Stop-before resolves the original hybrid to its vertex and requires
COMMON; the prefix excludes that Enter and retains every earlier exit/tied node.

A caller-supplied literal Lean ordering suffices to **define a supplied-word
record** after its typed step/slot decoding is bound. It does not authenticate
where the list came from, nor establish equality to the unchanged compiler.
Calendar-prefix use additionally needs original carrier/registry/mode/calendar
bijections, literal per-cohort `Finset.toList` list equalities and the date/node
splits required by `actual_compiled_before_node_split`. The existing native
ascending-ID agenda can be used only under an explicit supplied-word label or
a proved equality to that exact original list. A caller Boolean saying “Lean
order” is never a proof or admission gate.

`exit_phase_perm` / `node_phase_perm` prove endpoint PMF equality for permutations
inside each phase. They do not identify the intermediate columns of an arbitrary
Old reader. In particular, reordering a tied entry batch can preserve its final
law while changing the record. No independence or source-prefix correspondence
is inferred from phase commutation.

## Concrete source binding and budget obligations

The existing accepted contracts define exactly the target information:
`G2SourceFiniteHistory.historyLaw` conses each step destination;
`PrivateRegisterHistory.initializedSourceHistory` retains any correlated Old
label, its entering Code, and the complete finite endpoint vector;
`PrivateSeedHistoryFactorization.naturalInitialJoint` couples the actual private
seed with that SAME natural Code. `actual_private_seed_erased_history_product`
derives the product under NoPrivateWordRead. A first recorder needs no arbitrary
external Old input because it returns the whole initialized record itself.

Still needed before a source claim: canonical native Snapshot/ordered-tree/ID
encoding to actual Code; literal conditional row equality before selected
pushforward, with actual physical slot evaluation; natural initializer equality;
compositional full-path readRows equality; exact program/prefix list binding;
and typed NoPrivateWordRead for the named prefix. These are reused-provider
adapters/proofs, not desired row laws or caller assertions. The 68e/fcad source
proposal and its later proof repairs are not substituted for an acceptance.

Provisional implementation bounds (to freeze only after review): existing four
copies, 32 letters, 16 slots and 256 variables; unchanged provider caps; wrapper
queries 4096, raw extensions 65536, term products 262144, frontier paths 4096,
interned states 8192, DAG nodes 65536 and total frontier terms 65536. Use checked
integer arithmetic, precharge raw extension/products before generation, and
check prospective state/node/term insertion before committing it. Proposed
coefficient arithmetic bits default 4096/hard 65536 and streamed frame 4 MiB
require operand/result checks. A provider or wrapper exhaustion returns UNKNOWN
with no partial table and preserves population/stage/kind metadata. Work counts
are observed, not a proof of exhaustion. Exclusive fresh output and a separately
approved process/storage envelope remain required before any future execution.

## Meaningful later regressions; none run here

1. Empty natural prefix retains every entering Code/register assignment and
   zero endpoints, rather than producing an empty initialized record.
2. Two intervals around an unrelated cohort allow the same final ordered Code
   via a merger before or after the intermediate endpoint. Those complete paths
   stay separate; forgetting paths recovers the existing final semigroup table.
3. Old g=1/3 means original Gamma=2/3; copies and carried descendants share the
   same once-stored COMMON bit. Every original register coordinate is retained.
4. A tied phase has equal endpoint laws under permutation but different prefix
   columns. Literal-list binding distinguishes it; no all-Old permutation claim.
5. A carrier diagnostic with the same selected ordered tree and representatives
   0 versus 1 exercises the raw hook. This is outside the natural-only API and
   prevents an unjustified general selected-to-Code injectivity assumption.
6. A no-read prefix erases the private coordinate at every stored Code while
   keeping the seed joint record. Future COMMON reads are not silently erased.
7. Exact/one-below path, node, arithmetic and frame bounds yield complete tables
   or explicit UNKNOWN, never partial records or infeasible-source claims.

These are targeted future information-preservation controls, not tests already
passed. No public endpoint, timed history, arbitrary full-carrier law, source
admission or global completion claim is created by this plan.
