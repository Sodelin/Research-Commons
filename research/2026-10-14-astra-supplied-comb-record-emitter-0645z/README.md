# Supplied COMMON input-record emitter

Source-only draft: no emitter, test, Lean, Lake, native checker, or import-query execution has occurred for this packet. Root authorized additive source implementation after the design in `communications/2026-10-14-astra-supplied-comb-record-emission-design-0640.md`. Frozen runtime 2350, parsers, Rust code and earlier proof sources are unchanged.

`emit_supplied_menu.py` reuses pinned `certificates.loads/common_packet`, `emit_support.render` and `external_encoding.fixed_queries`. It emits their exact base/support sources, a constant `SuppliedCombCertificates Unit` wrapper for each original certificate digest, and a fieldwise assembler producing a literal `SuppliedCombCertificates (Fin n)` for all ordered pairs. The wrapper derives sparse-polynomial nonzero, nonnegativity and annihilation from the existing literal proofs. No actual source `P`, source law, desired conclusion, axiom, placeholder or native decision tactic is an input.

The raw original input bytes, canonical menu digest, spelling-sensitive canonical certificate digests, original pair order, original taxa-list-to-Fin map and exact rational tokens are retained separately. Every pair has literal level/coefficient/value/ID projection declarations, including diagonal pairs and zero coefficients. Distinct token identities are not merged merely because their rational values agree. The companion ledger supplies identity provenance: the mathematical structure has no ID field, and no parser/hash-refinement theorem is claimed.

The supported profile is the unchanged exact language: 4–8 taxa, n² pairs, typed ID namespaces (same text across namespaces is legal), empty parameter constraints, 1–32 complete joint configurations of exact nonnegative total mass one, and L in 1–8 with the existing 16-term/15-square-coefficient/128-bit rational caps. L1 has no valid nonzero annihilating certificate when y1=1 and is refused by the original checker. L2 and higher input-side certificates do not imply existence of a positive-survival physical source. No configuration is refactored or renormalized; zero-mass entries remain in original input and the ledger.

Input is bounded at 256 KiB and JSON depth 64. Output is bounded at 16 MiB before any directory creation; large repeated full query tables can therefore exceed this smaller emission profile and return UNKNOWN. The CLI sets 256 MiB address space, 30 CPU seconds and 16 MiB file size; an owner-controlled finite wall guard is still required. Pin/shadow mismatch, valid-input output-budget exhaustion and I/O failure return UNKNOWN; malformed supplied input is refused. Output paths must be fresh, source writes are exclusive, and the complete EMISSION manifest is written last. An interrupted partial directory is retained.

`LAKE-TARGET.lean.inc` is an emitted additive target fragment with literal roots and owned module list. It is not a standalone configured package or an actual receipt. The owner must supply authenticated selected consumer/provider, Mathlib, kernel/support routes and an isolated Lake configuration before compiling it. Source generation always reports `EMITTED_UNCOMPILED`, `status = UNKNOWN`, with source existence, physical representative, hmatch, expanded protection, outer admission and refinement flags false.

`test_emission.py` prepares nine bounded Python control groups: exact old-source/query equality and payload hashes; full pair/index binding with mixed L; original bytes versus canonical/token identities; all nontrivial L2–L8 profiles and nonzero test points away from zero; malformed pair/PMF tables; malformed arithmetic/transport; output-budget no-write behavior; module-shadow refusal; and exclusive emission/placeholder lint. These are future tests, not recorded successes. They do not invoke native or Lean subprocesses, and they do not establish universal generator correctness. A later owner Lean run must check literal Unit/Fin-record types, projections and axioms, including negative generated-proof mutations, separately from Python tests.

Proposed first quiet-window command, **not executed**, from the repository root:

```text
python3 research/2026-10-13-astra-unified-solver-0645z/guard.py
  --out research/2026-10-14-astra-supplied-comb-record-emitter-0645z/evidence/python-controls-v1
  --cwd /workspace/Research-Commons/research/2026-10-14-astra-supplied-comb-record-emitter-0645z
  --memory-mib 256 --wall 60 --cpu 30 --file-mib 16
  -- python3 test_emission.py
```

The fixed guard retains its 4 GiB physical stop, 8 GiB disk floor and 1 GiB available-RAM floor. This command is only a proposal awaiting the compiler owner's serial slot and source review. Actual elapsed time, results and source pins belong to a later receipt. No automatic retry or compiler job is part of these tests.

Even a future compiled record closes only the pure supplied-input-record gap. Exact physical row matching for the same tuple and correlated PMF, fully expanded protected h, actual outer admission, exact parameter feasibility and Lean/native correspondence remain unproved here. The current conditional budget on raw declared PE+PH is not promoted to complete search. Recovered accepted provider 0616 and unchanged consumer 400153aa remain the selected mathematical route; source recovery is not a fresh compile or full historical 1614 delivery.
