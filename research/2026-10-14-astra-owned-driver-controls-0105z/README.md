# Owned-driver composition controls: 12 synthetic groups passed

The owner executed the focused controls from the frozen owned0025 `CONTROL-PLAN.md` on 2026-10-14 at 01:15 UTC. All 12 groups passed in one actual resource-guard invocation: exit 0, no stop, 1.503 seconds, peak child RSS 30,326,784 bytes. The result is **PASS_SYNTHETIC_ONLY**. No builder was imported, no compiler ran, and the controls attempted no subprocess creation or process signalling. No production owned-provider batch was launched.

The production driver stayed byte-identical at SHA256 `157991882a6773c580fb8dcc226296b34d552bca39f09605a947fc55d3c727d7`. The controls loaded its actual `preliminary`, `before_state` and `finish` functions with the existing `capture_batch` and `run_provider_namespace_batches` preservation helpers. They did not copy or replace those implementations. The original six source-draft files remain byte-exact in `evidence/initial-source-draft/`; the unchanged `SOURCE-PINS.json` and `STATIC-REVIEW.json` describe that earlier, unexecuted cutoff. `VERIFICATION.json` records the subsequent execution and byte readback.

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

The harness explicitly substitutes only filesystem paths, the already separately checked source-pin gate, `/proc` inventory and the transport's process-identity/aliveness observations. It calls the real receipt hashing/interpretation and capture functions. It never exercises launch or stop signalling. The unchanged transport and namespace test corpora were reused as prior evidence rather than rerun. Subprocess creation and process signalling were patched to fail immediately if accidentally requested; builder modules remained unloaded. Source bytes were checked before and after the suite and during this evidence export.

Each case preserved its synthetic files, expected mutation journal and capture/finish output. Shared-fixture mutations were restored only after their exact original/replacement bytes had been journalled; no production paths were changed. The actual `TEST-RESULT.json` records no failures or errors. `evidence/composition-v1/EXPORT.json` binds 123 selected output files from the scratch run to their exported hashes. The large mutation journal is losslessly compressed, with both original and compressed byte hashes; 136 embedded delta payloads were authenticated. An intentionally malformed prior-checkpoint delta is preserved literally, with its export readback documented in `EXPORT-READBACK-NOTE.json`.

The roughly 10,775-file shared synthetic external fixture tree is omitted. Retained scope markers, synthetic terminal receipts, finish records and deltas provide the useful case evidence; the pinned fixture generator defines the omitted synthetic metadata. The export is a selected evidence packet, not a full scratch-directory backup.

The executed command is recorded exactly in `evidence/composition-v1/RECEIPT.json`. Its command shape was:

```sh
python3 -B test_owned_composition.py --output /workspace/scratch/astra-owned-driver-controls-0105-v1
```

The actual outer guard used 30 seconds wall, 20 seconds CPU, 256 MiB address space, 16 MiB file size, a 4 GiB physical-memory stop, and 8 GiB disk/1 GiB available-RAM floors. Its receipt SHA256 is `2ffed1f27757c38ebb9bd9e4971b95b2541a41077699f7ff894b2197cef070a8`. That receipt and its logs are actual execution evidence; receipts under `synthetic-cases/` are invented inputs or outputs of the controls. No autonomous next job or compiler action is available in the suite.

These finite controls establish the observed refusal, preservation and accounting behavior only. The real guarded builder still must authenticate the complete selected external closure, sources, logs, objects and namespace routes before an owned compilation. Final Lake execution, axiom audit, full aggregate completion and the physical representative remain separate obligations. The Python runtime, operating system, resource guard and harness remain trusted boundaries.
