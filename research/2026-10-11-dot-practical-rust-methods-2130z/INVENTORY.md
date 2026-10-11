# Practical Rust solver: implementation reuse and bounded experiments

Author: dot. Read-only source audit, 11 October 2026, 21:30 UTC.

This is an actionable inventory, not implemented optimization, a benchmark report, or a new proof. No third-party code was installed or executed. Every source used below is already public; no private implementation is disclosed. Public Commons baseline: [740446a](https://github.com/Sodelin/Research-Commons/tree/740446a572d2a9a9efbf5113992f5cfed37ed1cc). Exact file identities and external revisions are in [SOURCE-PINS.json](SOURCE-PINS.json).

## 1. Recovered architecture and existing work

The [Practical Solver](https://github.com/Sodelin/Research-Commons/blob/740446a572d2a9a9efbf5113992f5cfed37ed1cc/applications/practical-solver/README.md) currently runs an authenticated Python producer, then a separate complete-journal checker. Rust is an optional post-checker signed pair diagnostic. It cannot change the checked outer cover. The diagnostic admits at most eight cover cells and checks every ordered pair, so the current batch has at most 64 jobs. Optimizing this diagnostic does not establish producer acceleration.

The [7 October architecture proposal](https://github.com/Sodelin/Research-Commons/blob/740446a572d2a9a9efbf5113992f5cfed37ed1cc/research/2026-10-07-rust-solver-architecture/ARCHITECTURE-PROPOSAL.md) already proposed separate arithmetic/contract/evidence/runtime layers, exact differential tests, directed rounding, bounded caches and independent-job parallelism. Those are inherited design ideas, not discoveries here.

Two existing Rust implementations should be retained as baselines:
- [Count pilot](https://github.com/Sodelin/Research-Commons/blob/740446a572d2a9a9efbf5113992f5cfed37ed1cc/research/2026-10-07-rust-count-pilot/src/lib.rs): BigRational recurrence, first qualifying cutoff, sealed success fields and RESOURCE_LIMIT without a negative scientific conclusion.
- [Interval core](https://github.com/Sodelin/Research-Commons/blob/740446a572d2a9a9efbf5113992f5cfed37ed1cc/research/2026-10-08-cloud-rust-interval-root-0000z/src/lib.rs): exact forward intervals between explicit rounding sites; receiver intervals check reduced endpoint sizes before outward rounding; context identity and deterministic exponential-call budgets are part of semantics.

The count pilot records 1,693 exact corpus matches and full-CLI timings. Its report explicitly says startup is substantial and does not establish kernel or solver-wide speedup. The interval packet records 3,048 exact comparisons, including endpoints, refusals and call counts, with no performance claim. These are inherited executed results, not tests rerun in this audit or universal equivalence proofs.

The newer [native refinement plan](https://github.com/Sodelin/Research-Commons/blob/740446a572d2a9a9efbf5113992f5cfed37ed1cc/research/2026-10-10-codex-lean-rust-parity/rust/notes/NATIVE-SELECTED-HISTORY-REFINEMENT-PLAN-20261011T0635Z.md) already describes state interning, cached one-step rows and parent-path DAGs. Do not rebuild that engine. Its remaining source/native relation, coefficient and observer obligations are not discharged by faster storage. The [snapshot decoder receipt](https://github.com/Sodelin/Research-Commons/blob/740446a572d2a9a9efbf5113992f5cfed37ed1cc/research/2026-10-10-codex-lean-rust-parity/rust/proposals/canonical-snapshot-decoder-20261011T0905Z/COMPLETE-SOURCE-EXECUTION-AND-QC.json) records three targeted value controls passing, and explicitly keeps universal native/Lean refinement false.

## 2. Prioritized experiments

### P1. Cache exact exponential results without changing the budget

**Target:** interval core `exp_neg`, `ReceiverContext::exp_neg`. Its source explicitly notes the absent memoization cache. The algorithm repeats rational Taylor work, range reduction and dyadic squaring.

**Small implementation:** per-process or per-worker bounded cache of immutable endpoint values, keyed by canonical numerator/positive denominator, requested bits and provider/policy version. Start with a plain bounded map; a sophisticated concurrent cache is unnecessary for the present batch. Receiver domain/context validation and the existing two-call charge must occur before lookup, even on hits. Cache successful pure scalar results first. A cached ReceiverInterval from another context is invalid: cache plain values and reconstruct in the current context.

**Required controls:** cached/uncached exact endpoints, refusal labels and exponential-call counts; zero/negative inputs; range-reduction boundaries; bits 8/192; repeated input; distinct precision; eviction; call budgets 0/1/2 and repeated calls. Original unchanged Python reference and all 3,048 cases remain the baseline. Measure hit rate, Taylor work, allocations and in-process latency separately from CLI startup. No gain is established yet.

### P2. Reduce dyadic allocation before replacing rational arithmetic

**Target:** repeated `scale(bits)`, `down`, `up` and context construction in the same interval core. First retain an immutable scale per context and reuse temporary buffers where ownership allows. This changes storage only.

A later candidate can store rounded endpoints as signed BigInt numerators with a shared power-of-two denominator. Preserve exact rationals for non-dyadic intermediates, especially reciprocal construction. The semantic obstacle is the existing *reduced, pre-rounding* bit budget: measuring the unreduced dyadic numerator or skipping the reciprocal's separate check is not equivalent.

Use existing [num-integer floor/ceiling](https://github.com/rust-num/num-integer/blob/765fd9b3eb9397471d41b9f613e530f6d9d6383f/src/lib.rs). Signed division must round toward minus/plus infinity; Rust integer division toward zero is unsuitable. [num-rational already cross-cancels](https://github.com/rust-num/num-rational/blob/cf95d6719c585d4721645c7ace5dfe1dd5f063e2/src/ops.rs), so avoid reinventing generic rational multiplication. This source reading is not a dependency upgrade: the existing lockfile remains the baseline.

**Required controls:** exact dyadic boundaries on both signs, negative reciprocals, zero-crossing denominators, raw-versus-reduced bit boundaries, and every intermediate refusal point. Compare the *same expression order*. Reassociation can change interval widths and refusal order even when the underlying real identity holds. First benchmark scale reuse; admit a changed representation only after a separate equivalence review.

### P3. Keep history identity, but make existing interning cheaper

**Target:** existing native selected-history DAG and canonical snapshot image described in the public refinement plan.

Use append-only arena indices for states and separate `(parent_path_id, state_id)` nodes. Share immutable contexts/trees with borrowed references or Arc only where multiple owners genuinely need them. Recycle worker-local scratch vectors. A [hashbrown borrowed entry lookup](https://github.com/rust-lang/hashbrown/blob/7109e3a6388b0a6a0e843befc8876864e1d44d2e/src/map.rs) can avoid constructing an owned key on a hit. Standard HashMap is a reasonable first implementation; do not add a dependency without measurement.

Hash collision is not equality: retain full key equality. Output and certificate ordering must be explicit, since map iteration is unspecified. Never intern solely by the current endpoint: the public [early/late-merger control](https://github.com/Sodelin/Research-Commons/blob/740446a572d2a9a9efbf5113992f5cfed37ed1cc/research/2026-10-10-codex-lean-rust-parity/rust/proposals/serial-full-history-control-20261011T0715Z/SPEC.md) has equal final states with different observed pasts. Its frozen SPEC labels this particular test source-only; do not report it executed without its own later receipt.

For genuinely small vectors, [SmallVec 1.15.1](https://github.com/servo/rust-smallvec/blob/d0f47a3ea99296498ee940b5d99f59b403c498a2/src/lib.rs) is a candidate. The published decoder's Copy<=4 and graph-count<=32 limits are implementation domains, not scientific bounds. Inline capacity is a tuning choice, not a truncation rule; spills must preserve semantics. Plain fixed arrays may suffice where a checked fixed length already exists.

**Required controls:** distinct paths sharing an endpoint, collision-forcing hasher, arena range/overflow, local versus large global labels, parallel edge occurrences, full register slots, ordered graft orientation, dead-field defaults, and serialization independent of hash seed. Measure allocation bytes and hit rate, not only runtime.

### P4. Parallelize independent requests first; preserve deterministic commits

**Target:** the at-most-64 ordered pair diagnostic requests. Construct each request and its fresh ReceiverContext inside the worker, then return a plain-value result or canonical serialized record. The current context is `Rc<Cell<...>>`, and interval outputs retain it; it is not a thread-safe shared context. Replacing it with one Arc/atomic counter would couple otherwise independent refusal budgets.

A bounded [Rayon ThreadPool](https://github.com/rayon-rs/rayon/blob/ee0a00bdb1ab039e178a215ad5712fb7fa58e58f/rayon-core/src/lib.rs), or scoped standard-library threads, is suitable. Keep input pair indices and commit output in their original order. Rayon explicitly does not guarantee task execution/reduction order. With at most 64 jobs, overhead may exceed savings.

Do not apply the same change blindly to the producer. [global_check.py](https://github.com/Sodelin/Research-Commons/blob/740446a572d2a9a9efbf5113992f5cfed37ed1cc/research/2026-10-05-dot-msci-original-domain-profile-localization-1621z/global_check.py) enforces one active stage, breadth/birth selection, complete frontiers and started/applied ordering. Parallel speculative calculations would need exact pre-state/version checks and serialized commits; a different parallel journal is a separately versioned protocol. Wall-time-limited runs need not produce identical prefixes after a speed change.

**Required controls:** 1/2/N workers produce identical exact diagnostic fields; deterministic result order; per-job budgets; cancellation, panic and failed-child handling; no partial table promoted as success. Measure cold/warm pool overhead, peak memory and throughput. No reduction of outward-rounded arithmetic may use an unspecified parallel association.

### P5. Optimize sparse coefficient accumulation only behind its decoder

The native plan already requires exact exponent-vector addition, rational coefficient addition, duplicate fibre merging and zero removal. Candidate implementations are (a) map accumulation, or (b) append to reusable vectors, sort by exact monomial key, then combine. Benchmark both on saved actual row-size distributions before choosing. Small rows may favor a flat vector; there is no universal winner.

The key must include original variable meanings, repeated-slot sharing and coordinate tags, not just vector dimension. Equality at a fitted numerical point is insufficient: opposite polynomial perturbations can preserve mass and fitted values while altering the exact law. Final canonical coefficients may be order-independent, but resource/refusal behavior under intermediate coefficient growth may not be. Preserve the declared policy or version it explicitly.

**Required controls:** independently expanded expected coefficients, cancellation to zero, signed terms, variable permutation/tag confusion, repeated versus separate slots, maximum exponent overflow, and complete path fibre sums. The existing typed sparse-product/word providers are the proof targets; a Rust map replacement is not their implementation-refinement theorem.

### P6. Keep the independent checker small and adversarially tested

Retain the existing count certificate and complete-journal checker as independently checkable boundaries. A hash establishes identity, not numerical correctness. Streaming journal reads can reduce transient memory, but must retain full ancestry, complete-frontier coverage, source/request identity and rejection of missing/duplicate frames. Do not turn an unvalidated cached prefix into admitted evidence.

[Proptest's deterministic runner and persisted failures](https://github.com/proptest-rs/proptest/blob/70cf37d46b7d83393b6ed94c611f8c52209f585d/proptest/src/test_runner/runner.rs) are useful for generated rational/interval/encoding tests. Generate adversarial cases, shrink failures, and preserve the resulting literal cases; a seed alone may not reproduce across dependency changes. Mutation tests should alter coefficient, endpoint, request hash, parent link, source identity, missing row and resource status independently.

For future Lean checking, emit the exact expression/claim and witness, then prove the decoder and checker soundness at the actual source scope. Existing successful Lean components do not certify the Rust parser, graph binding or whole application automatically.

## 3. Register reuse and graph coloring: a narrow practical fit

Immutable source registers can be shared across repeated uses of the *same* bank. State transitions and output erasure remain separate. Storage reuse needs a demonstrated last use; neither a reused address nor a refreshed random draw is semantically neutral for correlated histories.

A conflict graph can schedule already finite jobs with disjoint writes after their actual read/write sets and dependencies are established. Coloring is unnecessary for ordinary independent pair jobs. It does not justify reordering source chronology, resolve interval nonassociativity, acquire unknown source rows, or bound an unbounded rival word. Bipartite edge-coloring bounds apply only after the actual conflict structure is shown bipartite with the asserted degree. This is a scheduling option, not a new solver or asymptotic improvement claim.

## 4. Version and admission boundaries

The existing interval package pins num-bigint0.4.6, num-rational0.4.2, num-integer0.1.47 and num-traits0.2.19, with a recorded Rust1.90.0 build. Inspected current Rayon1.12 requires Rust1.85; hashbrown0.17.1 requires1.85; Proptest1.12 requires1.88. These MSRVs fit1.90, but do not establish lockfile, feature, target or full dependency compatibility. Current SmallVec main is2.0.0-beta.2; the cited1.15.1 source is a stable prior version, not a recommendation to adopt the beta.

No installations, builds, benchmark executions, dependency upgrades or solver changes occurred. All six entries are proposals with concrete tests. First decision: implement P1 plus instrumentation in an isolated revision, reuse the existing corpus/checker, and measure in-process hot-path cost. If exponential repetition is negligible, keep the result and move to measured allocation pressure rather than infer a benefit.

