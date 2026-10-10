# Existing fitter witness to the native bank

Contributor: Codex / solver_design. Sourced static mapping and proposed API,
2026-10-10. No fitter, provider, compiler or native execution in this review.

The practical solver already exposes the old `find_source` engine through
[certified_bounds.py](../../../applications/practical-solver/certified_bounds.py#L318).
Its result retains the complete `backend_result`; the staged backend also saves
`backend/RESULT.json`. The selected `witness_entry` contains the original graph,
mechanism, exact values, all coupled equations and logarithmic physical realization.
No new optimizer is needed to feed the native supplied-fit bank.

The existing [capture.py](../rust/evidence/source-fit-bank-bridge-1/capture.py#L111)
already translates two saved fitter witnesses into the current DTO. Its
Fraction-only whitelisted polynomial AST is the reusable predecessor. It is a
fixture capture, uses `assert`, and silently selects the first panel; it is not
yet a general transport component. Production adaptation must use explicit
validation, a selected panel and bounded exact arithmetic.

## Smallest separate transport

Proposed new stdlib-only module: `rust/fitted_source_request.py`.
`export_witness(raw_backend_result, panel_row_index, global_labels=None, limits=None)`
returns the unchanged `source_fit_request_v1` plus separate
`source_fit_witness_transport_v1` origin metadata. CLI:
`--fit-result PATH --row-index N --output NEWDIR`. Start with the backend's raw
`RESULT.json`; a public-wrapper convenience can unwrap its exact `backend_result`
later. Do not invoke the fitter or a semantic checker during conversion.

The first adapter accepts the exact old result schema with status
`SAT_ONE_COHERENT_ADMITTED_SOURCE` and selected entry status
`SAT_INDEPENDENT_EXACT_WITNESS`. Check the canonical original request and equation
digests, explicit original scope flags, entry index and complete variable keys;
reject duplicate JSON keys, floats and unknown variants. These are transport
checks on supplied fields, not a new proof that the claimed old run occurred.

Retain the raw input, its SHA256, the selected entry index, complete original
request, equation strings/digest and all row/panel/action/readout metadata in the
origin artifact. Save the native request separately; its deny-unknown schema
must remain unchanged. Input bound: 16 MiB; native DTO bound: 64 KiB. Bounds,
invalid syntax and unsupported encodings produce an explicit failure with no
partial request. Preserve all original observations rather than emitting only
the selected panel's equations.

| Carrier | Exact conversion |
|---|---|
| Original graph | First endpoint occurrence defines the numeric vertex bijection. Copy the edge array in its exact order, retaining parallel occurrences. Root maps through that bijection. |
| Taxa | Old preparation maps public `taxa[i]` to internal `L_i`. Set native `leaves` to `[vertex(L0), …, vertex(Ln−1)]` and preserve the public taxon labels. Blindly copying an arbitrarily reordered graph leaf list would attach samples to the wrong taxon. |
| Parents and original IDs | Hybrid vertices are sorted by internal vertex name as in `Network.parameters`; incoming occurrences are in original edge-array order. External `registry.hybrid_ids[i]` labels internal `H_i`. Do not sort edge endpoints or swap parents. |
| Variable/value bank | Exactly `x0 … x(E−1)` then `g_<internal hybrid name>` in that sorted hybrid order. Require the exact value-key set. Rational strings normalize to reduced `p/q`. Keep old `g=P(incoming0)`; the existing binder performs `gamma_original=1−g`. Forced occurrence bits remain 0/1. |
| Exact trace | Reuse the capture's whitelisted integer/name/add/subtract/multiply/power/rational-division AST. No `eval`, caller expression imports or symbolic name parsing. Emit normalized lexicographic exponent vectors, omit zero coefficients, and retain equation order, duplicates and explicit zero equations. Enforce existing native dimensions, terms, exponents and rational-bit limits before expensive operations. |
| Copies | Select `panel_row_index` explicitly. Traverse public taxa order and each supplied sample list to form `copy_labels` and taxon indices. Require nonempty, distinct labels and at most four copies. Default global IDs are local indices; an explicit injective embedding is preserved as metadata and used for tree labels. Never replace global IDs above 2^53 with floats. |
| Physical bank | Preserve old strict integer-height calendar/log-rate definitions as provenance. The native binder already reproduces that height calendar and defines `u_e=d_e/(−log x_e)`, ancestral rate one. Never coerce these inverse rates into the rational-calendar DTO. |

The selected panel only chooses the native sampling carrier. Current readout is
the **natural completed rooted unranked law**. A selected row may have been
forced, randomized, unrooted or joint-quartet; its original reader and programme
remain in the origin. Do not claim the natural output equals that observed row.
Panels larger than four cannot be split into independent smaller fits. An
algebraic value is preserved as ascending rational polynomial coefficients and
the old **one-based** real-root index; the present native bank returns
Unsupported without evaluating or rounding it.

## Existing evidence and remaining gates

The recovered [solver.py](../../2026-10-04-dot-practical-solver-recovery-1803z/01-exact-source-solver/package/solver.py#L439)
fits one graph/assignment to every supplied row. Its
[verify_certificate.py](../../2026-10-04-dot-practical-solver-recovery-1803z/01-exact-source-solver/package/verify_certificate.py#L70)
regenerates the actual source equations and checks source admission, exact
positivity and physical realization. The public finite-registry adapter runs
that checker and retains its software scope. The recovered COMMON/INDEPENDENT
fit results are the actual origins of the already tested native DTO fixtures.
The new [independent reference](SOURCE-FIT-REFERENCE-ACCEPTANCE-20261010T2237Z.md)
checks the complete natural rooted polynomial and probabilities for those inputs.

A supplied old status or checker receipt is not an authorization to promote a
new native scientific flag. The thin converter establishes byte/representation
transport, not source-equation generation, generic native admission/refinement,
timed-history interpretation, empirical confidence, target inference, policy,
unknown-size exclusion or G6/G7 master closure. A later fresh captured old
semantic-checker binding can add its precise software provenance as a separate
consumer; generic Lean dictionary-to-original-Code refinement remains separate.
The exact source pins and static reviewed scope are in the companion JSON.
