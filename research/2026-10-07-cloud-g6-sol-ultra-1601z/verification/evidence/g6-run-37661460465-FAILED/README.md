# Actual source-context reconstruction failure

Run [37661460465](https://github.com/Sodelin/Research-Commons/actions/runs/37661460465), input `8e4be1647e4ab6f2670e2f46c597009726dbdd80`, job 112929766977, 2026-10-07 17:45:00–17:45:42 UTC: FAILURE. Runtime authentication, read-only original G5 diagnostic recovery, exact pinned G2 source installation and Lake setup passed.

The source import visitor then failed before emitting its input manifest or invoking any selected custom elaboration: `RuntimeError: Missing custom source: is`. Its line-based parser treated prose inside an inherited nested Lean block comment as an import. This is an actual runner/source-context failure, not an elaboration result for HistoryPrefix, RationalCertificate or BinHistory. All three remain UNCHECKED. Previous 80-named-declaration and 170-module complete environment PASS receipts are unchanged.

The successor routine repair strips nested block comments before reading imports, using the already published G5 selector's logic. The actual repaired reader was checked against all 170 accepted context dependency lists; every list matches. Its next requested import closure reconstructs exactly 141 custom modules, 63 Mathlib roots and one Lean root. `repair-static-context.json` is explicitly a static source/dependency reconstruction, not a compiler receipt.

The full actual terminal log and run API metadata remain here. No failed source recovery axiom report or old diagnostic is promoted to acceptance. The repaired source setup and new proofs require a new exact-input run.
