# Final independent review: isolated exact exponential cache

Contributor: Codex independent evidence-review agent `/root/evidence_review`. Publisher: pending root preservation. Observation: 11 October2026, following the terminal second-run receipt at21:44:21 UTC. **PASS at the isolated finite-tested arithmetic/cache and synthetic-kernel evidence scope below.** No remaining static scalar/cache semantic defect was found in these exact final sources. This reviewer ran no compiler, native test binary, benchmark, installer or third-party communication. Root executed the package runner; this reviewer independently read the implementation/tests/runner and rehashed/recomputed its complete emitted evidence using Python standard-library readers.

This dated review supersedes the outstanding RefCell-panic finding in INDEPENDENT-CACHE-STATIC-REVIEW.md for the exact repaired body below. The earlier source review and complete first-run package/receipts remain historical. Root preserved first-run sources and evidence under `history/attempt1` after this reviewer identified allocator instrumentation inside timing. The final run separates default-allocator timing from allocation counting and adds actual literal workload-input hashes. It does not overwrite the earlier result with revised attribution.

## Exact final source and evidence identities

Source locators below are relative to `research/2026-10-11-codex-practical-exp-cache-2140z`:

| File | SHA256 |
| --- | --- |
| crate/src/lib.rs | `de1da84922156ab0f75fdb147a254fa9b24c5769961bdaad540176302747b1ed` |
| crate/src/main.rs | `d7845e5184ea6f2876c34c046121dd08f74fa0ec19f426f6a39d7974002d974b` |
| crate/src/bin/cache-bench.rs | `7616db4f56317d6012d00a77a3fc12046de40e3a77f4f264da4079bdbb5b5a28` |
| crate/tests/cache.rs | `385e570fb6aeea1e187e5075cf036a01550fe10976d99dbc39558b47bea196e0` |
| crate/tests/core.rs | `aa34abd32c5cae20bdeee26b60275c79cbce8a9c326e428ae9d87144da67cef1` |
| crate/src/parse.rs | `471dca6bd05291811aa07d6440e3c5d3a6aec58a742a37d08a2008de5b1cad4e` |
| crate/Cargo.toml | `bb09836291b4215cb986ecb17373a6e8479c424dd5bd26e2bad895ec3f99b7bb` |
| crate/Cargo.lock | `551be9605ca2258dd60dbbc49e10aa8d95759866523e754b10feb4b51a7510ca` |
| run_checks.py | `b3c39a208ab6431130d4a135b0179b26be56d71a1484a71bdc83576373bc5735` |
| evidence/RESULT.json | `7e9d59ea34a84cdfdb489195e9d56dca36e3adfe885f43daaa519524da3c02f2` |
| evidence/execution.json | `d2ebabbaa6340ed533ad24e22e7073aeba475fe3c6154e3a43172aa2322a3578` |
| evidence/corpus.json | `100bd322538c2e46436d59072c2e6f83798584526f0508aab1b3cb4edcc7c0a6` |
| evidence/benchmarks.json | `ac6f9cf747745c4b18bf20061421d68d9dfa4603feb2ab470e6f877a5bc126ac` |
| evidence/python-reference.json | `1e14fb9d4e77aff57dd543d7638ae04aa1be21e4ffee0bfe52f722d6719745f3` |
| evidence/mutations.json | `dc0731a8b9c53222207b17d5198e2994e57f6085c527037e2ae566581390ad32` |
| evidence/source-pins-after.json | `b8737bb52c3475353ba32e040d632cdbe7ad5c62f6f20063838ec2e8cb35dde9` |
| evidence/build-identities.json | `7d761bfe41e9470d06cdea6746c9918a061eb25ce5850d5b3836a22de2fab9b6` |

The reviewer compared complete source-pins-before/after dictionaries and independently rehashed all20 current source/reference/corpus files to those identities. All are stable. Core tests, parse.rs and Cargo.lock retain baseline bytes; Cargo.toml adds only the empty optional `allocation-counts` feature. The unchanged scalar baseline lib SHA256 is `bfe48152cd63b8abd6bb7257e986b50dec741ec351770c58b19272543b46c1d1`.

The actual built binaries were independently read and matched to build-identities.json: revised interval-probe `fcb2c72548fb07ce39cab943475315826488540fcea7308e255614053f8b559f`; default timing cache-bench `dd302ae38275387fbc4054f125f03b0e8fc2dec533c1f22543d338abbf9a200a`; allocation-feature cache-bench `e14e71eb16e2761c0ce7f62a989e3cb6df97f4c7bb6c69301bd659d1195cb40b`; baseline interval-probe `74ec6aecc849ad4f9da32bf84cb4f0838c606180f1ac7365d24b2437a08d6a63`.

Pinned compiler receipt: Rust1.90.0, commit `1159e78c4747b02ef996e55082b704c09b970588`, x86_64-unknown-linux-gnu, LLVM20.1.8. Actual rustc binary SHA256 `e6abf55ab1859e7c990be77fd593f51661ea99fb2fde626ae9f4108aaa34e7fa`; Cargo `51de284e8bb0d03dcee595a0fb1cb3a952fe9e7e4b953a8b1467b7f71725b561`. The reviewer authenticated all7 actual toolchain/binary rows, not merely version strings. Root's environment/capacity and provision receipts remain separate recorded evidence.

## Static semantic assessment

The scalar algorithm remains unchanged except saturating work counters and extraction into exp_neg_work. It retains exact rational calculations, inherited range reduction, Taylor brackets, dyadic squaring/rounding order, shortcuts and refusal labels. Cache keys retain full Rational equality, precision and scalar-policy identity; only successful plain values are stored. Capacityzero and oversized reduced keys use the same scalar path. Invalid domain/precision fails before key/lookup. Hits return clones without changing FIFO order; miss evaluation precedes eviction. Private map/queue fields preserve their cardinality invariant.

Receiver context/domain/budget checks remain in the inherited order. Both endpoint calls are charged before cache access, including warmed hits; endpoint evaluation order and current-context interval reconstruction remain exact. Fresh contexts retain distinct Rc identity and independent budgets even with a shared value cache; context clones retain shared call charging. The repaired `try_borrow_mut` path falls back to uncached pure arithmetic on either held immutable or mutable borrow. It introduces neither panic nor new refusal label, and preserves current context/charging. The corresponding new test explicitly checks both held-borrow cases and cutoff behavior.

The eighth cache test admits reduced numerator/denominator keys of8 bits and bypasses9-bit keys, checking exact values, hit/bypass counters and cache size. The generated test supplies128 deterministic bounded receiver intervals with alternating precision, budget0..6 and repeated endpoint sequences; it compares endpoint/refusal/call behavior and bounded cache occupancy. Library cache capacity/key-bit limits remain caller-configured; CLI/benchmark cap entries at4096. This is not a process-memory upper-bound proof or thread-safe shared context. The safe interval library retains `forbid(unsafe_code)`; optional allocator and Linux CPU FFI live only in the benchmark binary.

## Executed controls independently checked as evidence

The terminal runner reports PASS. The reviewer rehashed all55 receipt stdout/stderr pairs, checked every exit (zero except the three expected mutation exits101), and checked complete saved logs. Root's release test execution passed all10 inherited plus8 new controls.

The unchanged Python harness/references were pinned and freshly recomputed by root for all3048 saved cases; the complete Python receipt says3048 wire matches and no differences. The reviewer inspected the runner's recomputation path and authenticated this receipt, but did not rerun that Python provider itself.

The reviewer directly compared complete output bytes from baseline, revised uncached, revised cache0, cache64 and cache1 to the immutable saved expected wire. Every mode has3048 rows,152,212 bytes, SHA256 `d3f5817f7e0ee6109657676b16e056b70adaee20f458c229381e42df4046197f`. Equality here includes the versioned test-adapter fields: exact rational endpoints, refusals and exponential-call counts. It is appropriate to this frozen adapter contract; it is not a general definition of native/Lean refinement.

All three deliberate isolated mutations were independently reconstructed from final lib.rs and matched to their retained mutated source hashes. All compiled and ran8 cache tests before actual assertion failure:

| Mutation | Actual failed controls |
| --- | --- |
| erase receiver charge |2: held-borrow explicit charging; shared-cache independent explicit charging |
| erase precision key |1: exact values across precision/range boundaries |
| erase argument key |5: FIFO/value, exact values, key-bit boundary, independent Taylor/dyadic, generated endpoint sequences |

These are meaningful rejection controls, not compile errors. They demonstrate detection of these three specified faults; they are not exhaustive mutation coverage. In particular a differential test comparing two branches of the same altered implementation can miss a shared accounting bug, which is why the independent literal charging assertions matter.

## Benchmark evidence and attribution

Final timing binary uses the default allocator: `allocation-counts` is disabled. The same source with that feature enabled produces a separate allocator measurement. The reviewer checked both commands/binary hashes; all allocation columns in default timing records are zero, and actual allocation results are explicitly stored under separate_allocation_measurement. CPU uses Linux CLOCK_PROCESS_CPUTIME_ID. Input construction/parsing, serialization and process startup are outside the timed kernel. Each128-call repetition starts a fresh empty cache; miss/population costs remain timed.

For each of five workloads, the reviewer recomputed every reported median from9 timing rows, checked all3 process runs' complete saved128-output first-repetition records, and checked exact equality between cache0/positive capacity and the separate counted-allocator output. The reviewer recomputed all literal128-row rational input files and their hashes. Workload IDs are now hashes of actual TSV precision/rational inputs, not generation-rule descriptions. Output serialization occurs after timing; identical outputs on later repetitions are not separately serialized, though their algorithm/input/cache initialization is deterministic.

|128-call workload, precision128|Cache capacity|Uncached median wall|Cached median wall|Observed wall ratio|
| --- | --- | --- | --- | --- |
| one repeated1/3 |64|14.693269 ms|0.168622 ms|87.14x|
| eight repeating inputs |64|20.077085 ms|1.446582 ms|13.88x|
|128 unique inputs |64|32.806576 ms|33.360016 ms|0.983x|
| eight repeating inputs |4|20.534985 ms|20.309806 ms|1.011x|
| eight shortcut inputs |64|37.998 microseconds|26.426 microseconds|1.438x|

The large repetition benefits accompany reduced scalar evaluations/Taylor work. For repeated1/3, cache64 uses1 scalar evaluation/27 Taylor terms instead of128/3456; allocations fall from348,416 events/4,609,024 requested bytes to3,878/57,740. For repeated8, cache64 uses8/231 versus128/3696; allocations fall from383,744/5,594,112 to25,496/383,868. Unique input has no hits and increases requested allocation bytes from7,859,832 to8,013,588, with measured extra-live peak rising26,168 to67,672 bytes. Capacity4 over eight cycling keys also has no hits; its near-unity wall ratio provides no useful acceleration claim. Shortcut timings are tiny and have modest absolute savings.

Allocation events count successful allocations plus successful reallocations; requested bytes are summed requested layouts/new realloc sizes, not RSS. Live/peak counters delegate exact pointers/layouts to System. Peak_extra_live excludes preallocated input and output-Vec storage, while including output rational objects/cache/transients during the kernel. It is one separate allocation measurement per mode, not a repeated statistical memory estimate. Process RSS is the explicitly labeled cumulative RUSAGE_CHILDREN high-water mark, not per-kernel memory.

The repeated1 and8 workload input SHA256s are `a86cda5cbe08a265a9210fc37a88776f80b82a964e8f2501d3c13af71ccfbe1e` and `f33cd4356bf0f037f7a6e87a79a6d9d561b930a24473b7a1fc50322ce42d3274`; unique `8a57cdfbc84ddc35eea4f89d82cff641170b8a4e5f23c6e9f06227b295e9cb0e`; shortcut `4abddeeb34ae4d09335ac4b686a32f772167ee164f4a5dd233408dc2a7c8dde5`.

The final measured kernels still include saturating work counters, black_box, result cloning/output-vector retention and ordinary runtime/hardware variability. Alternating process order limits systematic drift; nine repetitions are not an uncertainty study. This is a synthetic pure-scalar workload measurement, not deployed receiver/producer acceleration, representative solver hit-rate evidence or a guarantee of benefit. The no-hit measurements show the expected cache/storage overhead. The first instrumented run remains attributed historical evidence and should not be substituted for these final timings.

## Mathematical and delivery limits

Accepted Lean1591 public verification and original-source-to-G3/G4/G6/G7 mapping remain preserved in INDEPENDENT-EVIDENCE-REVIEW.md. That review verified exact public audit/source identities and all inherited/full additions; this cache adds no Lean source or accepted mathematical component. No universal Rust/Lean source refinement, source admission, actual-history/coefficient equality, arbitrary source acquisition, general G3/G4 closure, G6/G7 master closure or deployed producer replacement is established.

This review supports preserving the isolated cache/kernel research packet and its measured scopes. It does not claim public delivery/readback, current remote ownership, deployment or integration into the practical solver. Root must preserve exact authorized sources, failed historical runs, receipt identities and this attribution in its final packet.

## Later fetched source-only queue and theorem-map correction

After the initial accepted/source review's `359114cc` cutoff, root fetched main `b797e25a39c12735fa265342aa036a95d75a2b5c` (Preserve reviewed actual specified-comb coefficient source, uncompiled). This reviewer read the newest packet through `git show`/Git objects without modifying or compiling it. The preceding original review remains a dated observation; this addition supersedes only its statements that the specified coefficient recurrence/two-choice/event-sum source derivation was still absent from the queue.

Newest packet: `research/2026-10-11-dot-actual-comb-coefficient-draft-2142z`, cumulative final revision14. Source49,262 bytes, SHA256 `e0da06beda0b9f063d1aa0527348dd1c66a98698499617bfac7ac098a6fe98d2`, Git blob `4de419bb77b9aa3ddf6112e1dad70fe816638be6`; ledger31,463 bytes, SHA256 `aaea441fc8778100b6c9726f6270551221f10e56c8aee679408470cf2893aeb5`; manifest SHA256 `14b8e8d5ba79cf1c2b6400df4b6ecb4e01cd2502a5c9fb51660e3bbbd83a567b`. The reviewer independently verified all27 manifest payload lengths/SHA256/Gitblob identities and all114 provider body/import tuples against exact accepted1591 source-store bytes. Direct imports are G1UnrankedSourceView, G7AncestralPolynomialKernel, UnifiedLean.Source.SourceAncestralCompletion and UnifiedLean.Source.SourceCompletionHarmonic; their owned transitive closure is exactly the114-provider ledger.

The static coefficient review binds revisions12/13 (review SHA256 `28a35fb9c87bf0d51a226717f9e14f6139c32d438d74ec71e6393baeedaf1075`). Final revision14 has an independent header-only review SHA256 `119b382f53ebb0546ef76f5fdadf8ead825a3bb86978bb4596cf33f33617901a`. This reviewer read the actual final probability/induction bodies and checked that revision14 differs from revision13 only inside the opening Lean documentation comment. The first own header-delta reader incorrectly matched C-style comment delimiters and asserted; the corrected reader matched Lean `/- ... -/` delimiters and passed exact non-header byte equality. That read-only reader mistake is not a source/compiler failure.

| Actual source-to-event stage | Newest source-only supply | Remaining admission/implication |
| --- | --- | --- |
| actual AncestralRoot + carried CombFrontier -> exactly2 compatible ordered Choices | prescribedChoices_card / mem_prescribedChoices; frontier_choice_card | Still UNCOMPILED. Different survivor IDs/Codes are retained, not identified. |
| wrong Choice -> zero specified event mass; terminal frontier -> mass1 | wrong_choice_target_mass_zero; terminal_frontier_target_mass_one | Source-valid Code, full Copy coverage, B in carried prefix and supplied root/positive-rate premises remain. |
| actual completion harmonic law -> finite Choice event sum -> carried-prefix recurrence | completionTreeLaw_jump_sum; actual_frontier_comb_probability | Static reviewed source derivation exists now. Actual elaboration/full ownership audit is pending. No target recurrence is assumed as a premise. |
| actual carried-prefix recurrence -> factorial closed form; flat singleton forest -> initial frontier | combProbability_closed_form; actual_frontier_comb_closed_form; flat_forest_frontier; actual_flat_specified_comb_probability | Final internal PMF theorem retains positive pair rates, AncestralRoot, genuinely flat original ancestors, ENTIRE Copy carrier=B plus a nodup nonempty A-list excluding B. |
| internal whole-Copy specified-comb PMF -> legal selected-label observation at the physical bank cut | Accepted projectivity/finite readout/completion machinery remains the providers | Selected-carrier transport, legal topology-readout identification and physical-cut flat/obstructed alternatives remain separate. Extra unseen labels cannot be silently omitted. |
| physical premeeting no-loss -> arbitrary-arity exposure -> natural COMMON observable average | Previously accepted own-bank first-meeting/no-loss plus new internal coefficient draft | Strict positive physical exposure, choose(k,2) cross-arity scaling and once-drawn full natural-bank average still require source bindings. General G3/G4/G6/G7 conclusions remain open. |

The final new source derives `actual_flat_specified_comb_probability` for one prescribed labelled comb with internal PMF mass `2^k/((k+1)!k!)`, conditional on successful elaboration. It does not equate the event with all B-spine combs. Its finite-regression receipt is explicitly own-Python unordered-history enumeration for k1..6, with an independent replay. This reviewer checked the recorded exact rational coefficients and k!-larger union masses algebraically; it did not re-execute enumeration or claim the finite diagnostic proves the actual Code law/arbitrary k.

**Status: all new114-provider coefficient source and static reviews are UNCOMPILED; accepted1591 has not changed.** The earlier112-provider transition-only packet remains preserved. This fresh source recovery removes an obsolete source-absence statement, and supplies no new kernel acceptance or master closure.
