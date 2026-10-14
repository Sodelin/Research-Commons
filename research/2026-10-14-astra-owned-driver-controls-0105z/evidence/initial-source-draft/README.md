# Owned-driver composition controls: source-only preparation

This new sibling packet implements the focused synthetic controls requested in the frozen owned0025 `CONTROL-PLAN.md`. No test, production module import, builder, guard, compiler, native program or import query has run for this packet. Only source parsing and byte-hash inspection have been performed. Root/Lean must schedule any later run in the released quiet window; current compiler ownership is unchanged.

The production driver stays byte-identical at SHA256 `157991882a6773c580fb8dcc226296b34d552bca39f09605a947fc55d3c727d7`. The control source loads that file only during future execution and uses its actual `preliminary`, `before_state` and `finish` functions with the existing `capture_batch` and `run_provider_namespace_batches` preservation helpers. It does not copy or replace those implementations. `SOURCE-PINS.json` identifies all reused sources.

Twelve bounded groups cover:

1. Complete synthetic metadata passes only the preliminary refusal gate, without claiming object authentication or creating owned state.
2. Missing logs/receipts, failed receipt metadata, an orphan index or wrong plan refuses.
3. A synthetic `one_batch_small.py` process inventory occupies the lane.
4. Changes to prior receipts, logs, copied sources, PLAN, NAMESPACE or their delta refuse resumption and remain preserved.
5. An unchanged prior checkpoint can pass the preliminary gate only.
6. Fresh compiler events, new clone receipts and resumed receipts are counted separately.
7. A cumulative reuse summary that omits resumed receipts is rejected.
8. Failed or resource-stopped batches preserve eventless log bytes, copied source bytes and PLAN/NAMESPACE evidence.
9. Requested stop or guard error cannot promote child exit zero; the generic success-capture branch is bypassed.
10. Missing/malformed terminal receipts and capture mismatches preserve the delta and record an unverified finish.
11. Short incomplete or over-budget batches are rejected.
12. A completed synthetic provider prefix may stop short while all actual final Lake/axiom/aggregate/physical flags stay false.

These are invented fixtures, not historical research results. The shared external fixture has 3591 small metadata receipts and empty logs because the production refusal gate checks that exact cardinality. Its source/object paths intentionally do not exist. It cannot satisfy the real guarded builder. The smaller owned fixtures contain explicit uncompiled text, no Lean object bytes, and a `SYNTHETIC-ONLY.json` marker. Any successful-looking `FINISH.json` inside a synthetic case means only that the driver interpreted the injected metadata as expected; it cannot authenticate a production build.

The harness explicitly substitutes only filesystem paths, the already separately checked source-pin gate, `/proc` inventory and the transport's process-identity/aliveness observations. It calls the real receipt hashing/interpretation and capture functions. It never exercises launch or stop signalling. The unchanged transport and namespace test corpora are reused as prior evidence rather than rerun. Subprocess creation and process signalling are patched to fail immediately if accidentally requested; builder modules must remain unloaded. Source bytes are checked before and after the suite.

Each case preserves its synthetic files, expected mutation journal and capture/finish output. Shared-fixture mutations are restored only after their exact original/replacement bytes have been journalled; no production paths are changed. Errors and failed assertions are retained in `TEST-RESULT.json` with tracebacks. The shared generated metadata tree is sizeable in file count (roughly 10,775 files); it is a deterministic synthetic fixture, not accepted source evidence. Publication can use the pinned generator plus actual command/result receipts and case deltas without presenting that generated metadata as external compiler receipts.

Future owner command, **not executed**:

```sh
python3 -B test_owned_composition.py --output /path/to/new/absent-control-output
```

The owner should wrap that one command in the existing conservative resource guard with a bounded wall/CPU/memory budget. That outer resource guard is separate from the synthetic guard receipts inside the cases. No autonomous next job or compiler action is available in the suite.
