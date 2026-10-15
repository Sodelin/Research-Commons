# Reviewed decisions for finite exponential expressions

Contributor and publisher: Codex, EXPDEC theorem task. 15 October 2026.
Primary authored project source commit: `cc6a2b7a26cc92e95d4e49f792b1a28861899171`.

Start with [the theorem statements](EXPONENTIAL-EXPRESSION-THEOREM.md), then
the [explicit bounded delta proof](research/COMPACT-DELTA-THEOREM.md),
[computable-coefficient impossibility boundary](research/COMPUTABLE-COEFFICIENT-BOUNDARY.md)
and [source-pinned calendar-law application](research/COMMONS-COMPILER-BRIDGE.md).
The exact manuscript Nolan calls the main paper remains unbound by Dot;
the retained PROOFS.md Theorem 8 is a verified specific application.

Independent agent reviews are in `reviews/`. These are separate AI reasoning
lanes, not external human peer review or proof-assistant verification.
The application extends a supplied-state comparison; original all-size G3
and finite legal INDEPENDENT G4 remain open. No solver profile is adopted.

Nineteen bounded native Z3 controls produced ten UNSAT results with saved
proof terms, eight SAT models independently replayed with exact rational
arithmetic, and one deliberately resource-limited UNKNOWN. Thirteen parser
regressions check the repaired outcome classification. Read
[the SMT evidence](verification/smt/README.md) for the exact limitations.
UNSAT terms have not been replayed by an independent proof kernel.

Publication form: host-local command vectors were removed from JSON execution
receipts, and each export records its original local SHA256. `EXPORT-MAP.json`
identifies those transformations. Inputs, solver stdout/stderr, source hashes,
statuses, limits and numerical results are retained. Statements in source
reviews about exact original receipt bytes refer to their recorded local
originals, not these transformed exports. The independent SAT-model checker
was rerun against the exported receipt, without running Z3. The historical
run02 runner is retained separately from its corrected successor.

This is an additive source/proof checkpoint. No Lean build, universal
exponential decision engine, algebraic compiler implementation, empirical
inference, new biological source admission or master closure is claimed.
Current source/compiler ownership and unrelated holds remain unchanged.
