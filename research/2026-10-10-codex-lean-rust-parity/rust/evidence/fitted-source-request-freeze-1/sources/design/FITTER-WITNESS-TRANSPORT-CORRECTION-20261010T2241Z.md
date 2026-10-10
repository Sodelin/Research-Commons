# Fitter transport: finite timing metadata

Contributor: Codex / solver_design, corrected after source-body review by
rust_implementation. Static proposal; no new runtime acceptance.

This supersedes the blanket float rejection in
[the first transport proposal](FITTER-WITNESS-TRANSPORT-20261010T2240Z.md).
That proposal and its pins remain preserved. Actual old fitter `RESULT.json`
contains a finite `elapsed_seconds` float; its direct-engine request can also
contain a finite `request.limits.seconds` budget. Rejecting every float would
reject the actual fitter outputs the adapter is intended to consume.

The corrected parser rejects duplicate keys and every nonfinite numeric value,
but permits finite timing/resource numbers at those two explicit metadata
paths. Exact assignments, law probabilities, source counts, sparse coefficients
and polynomial AST literals retain their strict rational/integer contracts.
No timing float enters the native DTO or mathematical arithmetic. Preserve the
original raw result bytes and hash rather than reserializing them as evidence.
Original request-digest verification must reproduce the inherited canonical
JSON serializer's semantics for its budget field; it must not invent a new
exact-decimal mathematical interpretation of an operational time limit.

The first API remains deliberately narrow: require
`SAT_ONE_COHERENT_ADMITTED_SOURCE`, its explicit `witness_entry`, and the selected
`SAT_INDEPENDENT_EXACT_WITNESS` entry. Ambiguous-target, identified-target,
candidate, incomplete and other result variants are Unsupported here. Never
choose an implicit first SAT entry. A separately reviewed extension can add
explicit entry selection for those other result contracts.

All other representation rules, original equation/panel preservation, 16 MiB
origin/64 KiB native request bounds and unestablished scientific flags remain
as in the first proposal. This correction is a pre-implementation input-contract
repair, not a fitter or native algorithm change.
