The future `PREFIX-PROVENANCE.json` is an owner-reviewed immutable handoff of the
**completed** original 3591-module execution. No instance is fabricated in this
draft, and `PREFIX_PROVENANCE_SHA = None` prevents execution until its actual
bytes are pinned in a reviewed source successor.

Required top-level fields:

- `schema`: `astra_complete3591_origin_ledger_v1`.
- `plan_sha256`: the unchanged active-plan SHA
  `ef775a7223500314359a9ed02a87d207b18eacda9cddfa5a8990c5e1a8e43f10`.
- `original042_057_059_outer_guards`: literal `UNKNOWN`.
- `modules`: exactly 3591 records with indices 0 through 3590 in order.

Each record must contain:

- `index`, `receipt_sha256`, `stdout_sha256`, `stderr_sha256`: actual original
  canonical bytes, including empty logs where that is the observed result.
- `compiler_sha256`: the selected official Lean 4.33.1 executable SHA.
- `command`: the complete literal original compiler argv, including its actual
  default, synchronous or Mathlib-specific option selection. No normalization.
- `runner_sha256`, `helper_sha256`, `recorded_execution`,
  `recorded_environment`: the corresponding literal fields, or `null` if the
  original record did not contain them. Missing identities must be explained
  by the actual published evidence, never supplied as desired metadata.
- `original_outer_guard_outcome`: the literal evidence classification. It must
  be `UNKNOWN` for recovered batches 042 (indices 2499–2530), 057 (2894–2925)
  and 059 (2927–2958). Other completed-module origins may belong to a successful
  batch or to a later failed/stopped batch; classify the actual outer receipt.
- `separate_recovery_authentication`: the actual immutable recovery references,
  or an empty list when not applicable. Recovered ranges require nonempty
  references without promoting their original outer outcome.
- `evidence`: nonempty records with repository-relative research `path`,
  `bytes`, `sha256` and a human-readable exact locator/role as additional
  metadata. These must include enough actual guard/capture/source/repair chain
  to authenticate that particular receipt and its execution profile. Every
  referenced file is rehashed. Repeated file identities are deduplicated only
  after checking identical pins.

The author and independent reviewer of this future manifest must verify each
locator semantically against the actual packet, not merely collect hashes.
The pinned manifest is an explicit trust boundary for historical context not
fully encoded by early receipts. The first 916 receipts are also compared as
JSON values with the frozen published `MATHLIB-SOURCE-EXECUTION.json` archive,
SHA `75c4ac16fb140e4a5b4e07f01f4dd6c3833b366be6cd1f812a3c608c458edda7`.
This handles early missing runner fields without inventing new executions.

Preparation creates the following new-state structure:

- `PLAN.json`: literal full 3661 source-query plan.
- `PREFIX-PROVENANCE.json`: exact reviewed provenance copy.
- `0000.json`–`3590.json`, `.stdout`, `.stderr`: byte-exact original copies.
- `reuse/0000.json`–`reuse/3590.json`: separate `AUTHENTICATED_REUSE` wrappers,
  binding original receipt, original context and provenance hashes.
- `source/<module>.lean`: selected source bytes, preserved before compilation.
- `INITIALIZATION.json`: exact preparation command/guard directory, source
  pins and wrapper hashes. Later authentication requires its closed successful
  guard, and preserves rather than deletes any incomplete preparation.
- `3591.json`–`3660.json` and corresponding logs: only actual new compiler
  records, as each bounded invocation completes. Their guard directories must
  have actual closed receipts before later reuse or complete authentication.

The fixed consumer function returns the same basic module-row shape as the
existing verifier plus deterministic origin metadata. It does not return a
caller-controlled proof registry, physical-admission certificate, or a claim
that a module count completes the mathematics.
