# Private rational common-atom extractor: proposed concrete contract

Contributor: Codex Rust implementation role, 10 October 2026. Status: proposed for root review; no code/build/runtime promotion at this capture. Target body and attribution: [readiness inventory](G6-RATIONAL-COMPRESSION-READINESS-20261010T1613Z.md).

## Input and domains

One duplicate-rejecting JSON object, exactly these fields:

```json
{"schema":"g6_rational_compression_request_v1","M":4,"atoms":[{"z":"1/3","alpha":"0/1"},{"z":"2/3","alpha":"3/2"}],"limits":{"atoms":64,"matrix_cells":8192}}
```

Atoms have exactly `z` and `alpha`. Array position is the immutable original atom ID; duplicates in z are allowed and never identify IDs. Rationals are canonical reduced `p/q`, positive denominator, exact arbitrary precision within the overall 65,536-byte request cap. Require `0<z<1`, `alpha≥0`. No supplied approximate float or probability-mass-one normalization. The private supported cap is `2≤M≤4`; natural integer tokens follow the accepted `calendar_cli::request::Nat` implementation, including `-0` interpreted as zero while booleans/floats/exponent notation/strings are refused. `limits.atoms` lies in `0..64`, `limits.matrix_cells` in `0..8192`. Unknown/missing/duplicate fields, wrong schema or unsupported limit configuration are invalid input.

Validate the entire request/domain before resource decisions. If the original input array length exceeds `limits.atoms`, return UNKNOWN of kind `atoms`, before moment/matrix generation. This count includes input zero weights. Thus a valid request over the supported maximum may still carry an honest resource UNKNOWN rather than a source infeasibility statement. The frame cap bounds parsing; no allocation is based on an unvalidated claimed atom count. Empty arrays are permitted.

Filter zero weights, preserving original ID order; if no positive weights remain, return an empty positive certificate with mass zero and all tail moments zero. No RREF is called. If at most `M−1` positive weights remain, retain them unchanged. Each later step is the exact audited 4760 Fraction algorithm: full `(M−1)×n_positive` matrix with rows `[1,G3,…,GM]`, first available pivot row, first free column, canonical null direction, `theta=min(alpha/d : d>0)`, nonnegative weight update and zero deletion. No value-based deduplication or rowwise choice.

## Work and UNKNOWN

Work has exactly `elimination_steps` and `matrix_cells`. Before **each** coordinate/RREF matrix generation, compute with checked integer arithmetic `required=matrix_cells+(M−1)*current_positive_count`. If `required>limits.matrix_cells`, return UNKNOWN with the previous completed work and no partial certificate; otherwise charge that full matrix cell count before generation. Charge one elimination step after its successful exact update. The matrix measure is a deterministic logical budget, not a bit-complexity theorem or an observed CPU-operation count. With at most three rows each RREF has bounded passes; input cardinality and deletion bound the number of steps. Default 64/8192 covers the worst possible 64-positive-atom path (M=4, at most 6,222 generated matrix cells). Rational integer growth remains subject to bounded process resources; a killed process is execution failure, never mathematical UNKNOWN/infeasibility.

## Results, binding and checking

Canonical result encoding is compact lexicographically sorted ASCII JSON plus one LF; complete frame cap 4 MiB. Successful/UNKNOWN envelopes include exactly `schema:"g6_rational_compression_result_v1"`, `request_raw` containing the exact original UTF-8 request bytes as a JSON string, `request` containing the parsed semantic object, `status`, `work`, and false fields `source_admission_verified`, `source_factor_realization_verified`, `arbitrary_real_extraction_verified`. Both raw and parsed bindings are checked against the separately supplied request.

Successful `status:"COMPRESSED"` additionally includes `output_atoms:[{"input_index":id,"beta":"p/q"},…]`, `mass:"p/q"`, and `tail_moments:[{"level":3,"moment":"p/q"},…,M]`. IDs retain original strictly increasing order, each in range; every beta is strictly positive; cardinality is at most `M−1`. The independent mathematical checker computes common mass and every geometric moment from the original atoms and selected original IDs, and checks the reported mass/tails as well as equality. It invokes no RREF. Choosing a different valid common-atom certificate can pass the mathematical checker; deterministic byte correspondence to the old algorithm is an additional differential obligation.

`status:"UNKNOWN"` additionally includes only `limit:{"kind":"atoms"|"matrix_cells","required":nat,"cap":nat}`. No `output_atoms`, mass or moments are allowed. Validate exact request binding, kind/cap agreement, `required>cap`, completed work bounds and frame. For atoms, required is the original length and work is zero. Matrix-limit framing does **not** claim independent exhaustion or a source impossibility certificate; its mathematical `certificate_valid` is false. Solver exit is 0 for COMPRESSED, 2 for UNKNOWN.

Invalid request/internal/execution failures have a minimal three-field envelope `{schema:"g6_rational_compression_result_v1",status:"ERROR",error:"INVALID_REQUEST"|"INTERNAL"|"EXECUTION_FAILURE"}` and exit 1; no partial atoms or original source conclusion. Internal arithmetic inconsistency is distinct from bad user data. Native checker output is `g6_rational_compression_check_v1` with status ACCEPT/REJECT, boolean `certificate_valid`, and false source/factor/arbitrary-real gates; ACCEPT exits 0, REJECT 1. Its UNKNOWN acceptance authenticates only framing, while COMPRESSED acceptance certifies the finite supplied rational moment identities.

## Delivery and acceptance

Add only a separate `rust/rational-compression/` crate, private `rational-compression-probe` executable, harness/notes/evidence. Reuse frozen parent exact Q/BigInt arithmetic and accepted natural JSON DTO/serde versions; no accepted core/frontend/helper source changes. Build target and ELF live outside the repository under `/tmp` or existing ignored native scratch, and every source/provider/binary identity is freshly recorded. No application dispatch or release command.

Focused acceptance: old deterministic M=2,3,4 compressor cases and corresponding saved original full-row transfers (331 equalities), zero/all-zero/duplicate-ID handling, exact/one-below resource boundaries, and independent positivity/index/cardinality/mass/tail checks including a same-mass balanced moment forgery. The accepted source theorem consumes a **single checked certificate** for all capped original CoLocated population rows; rational-to-real casting/checker binding remains a separately supplied proof. Neither rational extraction nor these finite tests construct a positive source network, admit arbitrary mixtures/graphs, identify generally transcendental calendar survivals with rational atoms, or complete the solver mission. Actual original Lean three-calendar saved-output comparison has priority on arrival.
