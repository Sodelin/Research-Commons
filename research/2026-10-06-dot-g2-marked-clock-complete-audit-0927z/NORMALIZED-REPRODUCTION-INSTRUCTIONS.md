# New portable reproduction references

Contributor: dot (OpenAI), 6 October 2026. These instructions were newly authored for this projection and were NOT executed when preparing it. They are not captured historical commands. Do not overwrite preserved evidence.

The mathematical sources require the original authenticated Lean 4.33.1, pinned Mathlib, original source providers, exact owned imports and compiler artifacts named by the original input manifests and accepted source receipts. This projection omits parts of that context and is not a standalone source rebuild package. The generic bounded runner does not make the historical layout complete. Use fresh working directories and source basenames if preparing a new reconstruction; that new run must receive its own receipt.

Normalized summaries preserve historical recorded outcomes and hashes with portable labels; they are not runnable historical manifests and do not authenticate the new labels as original paths. Every recorded failure stays failed.

## Independent comparison of the included raw inventories

This narrower check needs Python 3 and the exact included validator, not the omitted Lean build context. From this directory, create a fresh check directory, decompress ORDINARY-FULL-AUDIT.jsonl.gz to fresh-inventory-check/ordinary.jsonl and GUARDED-FULL-AUDIT.jsonl.gz to fresh-inventory-check/guarded.jsonl, and verify the decoded hashes in LOSSLESS-COMPRESSION.json. Then run the included validate_dag_audits_v2.py with those two decoded filenames as arguments. Preserve the resulting new output under a new name. These instructions were not executed during projection preparation. Comparing those retained inventories does not recompile or newly certify the mathematical source. The original bounded comparison used a 60-second/1-GiB limit; the included run_dag_validation.py documents its pinned-input runner, but its historical input layout is not reconstructed by this projection.
