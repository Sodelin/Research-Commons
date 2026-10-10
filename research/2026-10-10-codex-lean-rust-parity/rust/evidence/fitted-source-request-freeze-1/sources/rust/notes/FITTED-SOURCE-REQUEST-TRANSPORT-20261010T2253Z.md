# Existing fitted witness to the supplied-fit DTO

Contributor: Codex / rust_implementation. Implementation and static review,
10 October 2026, 22:53 UTC. No fitter, provider, exporter, native, backend or
compiler was executed by this contributor for this addition. Actual execution
of the new transport is pending the sole scheduler.

The new [fitted_source_request.py](../fitted_source_request.py) makes the old
[saved-witness capture](../evidence/source-fit-bank-bridge-1/capture.py) reusable.
It imports only the standard library. It accepts raw inherited backend
`RESULT.json` bytes with `SAT_ONE_COHERENT_ADMITTED_SOURCE`, the explicit
`witness_entry`, and that entry's `SAT_INDEPENDENT_EXACT_WITNESS`. Other result
variants are Unsupported; it never chooses the first satisfiable entry.

The reviewed [original contract](../../design/FITTER-WITNESS-TRANSPORT-20261010T2240Z.md)
and its [finite timing correction](../../design/FITTER-WITNESS-TRANSPORT-CORRECTION-20261010T2241Z.md)
govern this addition. Their SHA256 pins are `7d5bd138…` and `09d5df2f…`.
The predecessor is `7657508b…`, the inherited solver is `42e4353d…`.
The exact full hashes, source snapshots and unchanged dependencies are in
[the source freeze](../evidence/fitted-source-request-freeze-1/SOURCE-FREEZE.json).
Design independently read the complete exporter and recorded static PASS in
`design/FITTER-WITNESS-TRANSPORT-STATIC-QC-20261010T2252Z.json` (`fa94dfc6…`).
Static review and syntax parsing are not execution acceptance.

`export_witness(raw_backend_result, panel_row_index, global_labels=None,
limits=None)` returns an unchanged `source_fit_request_v1` dictionary and a
separate `source_fit_witness_transport_v1` origin. The explicit panel index
chooses the copied carrier only. Every original observation row, equation,
randomization action and reader stays in the origin; every supplied equation,
including duplicate and zero rows, stays in the native DTO in original order.
The API raises `TransportError` with Invalid Request, Unsupported or Unknown
status when representation, scope or operational limits prevent conversion.

The CLI is:

```text
python -B fitted_source_request.py --fit-result OLD_RESULT.json --row-index 0 --output NEWDIR
```

It creates a fresh directory containing the unchanged `BACKEND-RESULT.json`,
canonical `SOURCE-FIT-REQUEST.json`, `ORIGIN.json` and a transport `RESULT.json`.
Existing directories are refused without changing their files. Input syntax,
scope and resource failures emit no native request. Exit 0 means representation
export completed, including retained algebraic descriptors; such descriptors
explicitly carry `native_evaluation_scope=UNSUPPORTED_ALGEBRAIC_EVALUATION` and
false arithmetic/evaluation flags. Exit 1 is invalid input or execution failure;
exit 2 is transport Unsupported or Unknown. This CLI launches no solver.

The numerical vertex bijection follows first endpoint occurrence. Original
edge-array order and parallel occurrences survive exactly. Hybrid names use
the inherited sorted order and incoming occurrence order; external registry
ID `i` names internal `H_i`. Public taxon `taxa[i]` attaches to `L_i`, regardless
of the saved graph's leaf-list order. Copies follow public taxon order and the
supplied list order. An explicit injective global-ID embedding is preserved as
integer metadata, including values above 2^53. Old `g=P(incoming0)` stays in the
DTO; the existing binder supplies `gamma_original=1-g`. Forced bits are never
complemented or reordered.

Canonical inherited request/equation digests are checked independently of raw
JSON whitespace, which is retained byte-for-byte. Finite operational floats
are allowed only at `elapsed_seconds` and `request.limits.seconds`; no other
numeric float, duplicate JSON key or nonfinite number is accepted. Exact value,
law-weight and polynomial arithmetic uses integers/Fraction. Exact decimal
strings are rational strings, not binary floats. The original integer-height
calendar, edge duration/survival occurrence and logarithmic rate metadata must
agree. No logarithmic rate is rounded into the rational inverse-rate calendar
DTO.

The AST translator reuses the predecessor's integer constants, bank names,
negation, addition, subtraction, multiplication, nonnegative literal powers
and division by a nonzero rational constant. It uses no `eval`, caller import
or symbolic identifier parser. Terms normalize to nonzero reduced rational
coefficients in lexicographic exponent order. A rational assignment is checked
against the entire supplied trace with the same bank. Algebraic values preserve
ascending coefficients and the old one-based root index; their positivity and
trace evaluation are not inferred.

Operational bounds are explicit: raw origin 16 MiB; native DTO 64 KiB; origin
sidecar 16 MiB plus 256 KiB; JSON depth 128 and nodes 262,144; expression bytes
64 KiB, nodes 4,096 and literal power 64 (the predecessor's sublanguage); selected
copies 1–4; existing graph/shared-bank bounds 32. Native defaults remain 4,096
equations, 65,536 terms, 1,000,000 arithmetic steps, 4,096 rational bits and
4,096 power exponents; custom limits cannot exceed existing hard limits, with
rational bits at most 65,536. Operands and results are bit checked, term products
are checked before expansion, and bounded rational products/additions have at
most twice the operand bits plus one before reduction. Work counters are
observations of this converter, not a proof of provider work or exhaustion.

The requested downstream observer is natural completed rooted unranked
genealogy. A forced, randomized, unrooted or joint-quartet selected row is
explicitly tagged `COUNTERFACTUAL_NATURAL_ROOTED_OBSERVER`. Even a matching
natural rooted row does not acquire a source-observation fit flag. Supplied
statuses, digests and exact zero equations can be forged together; the converter
does not reconstruct their source meaning or authenticate an actual old run.
Source admission, provenance, observation fit, timed history, native/Lean
refinement, statistics and full-solver flags remain false. The mathematical
G1/G2/G5 completion is unaffected by this representation boundary.

[review_fitted_source_request.py](../review_fitted_source_request.py) is a
focused scheduler-only harness: two actual saved fitter results against their
previously accepted native DTOs, explicit forced/randomized panel provenance,
reordered leaves/public taxa/large global IDs, duplicate and zero trace rows,
algebraic retention, refusal/resource controls, CLI raw-byte/no-overwrite checks
and one existing source-fit-readout application pipeline with a separately
captured independent old-compiler reference. It launches no fitter, census,
old source checker or unchanged broad suite. The unchanged core/frontend/
adapter/launcher pins must remain stable. Actual execution must follow the
pending repaired selected-reference component8 and application4 checks.
