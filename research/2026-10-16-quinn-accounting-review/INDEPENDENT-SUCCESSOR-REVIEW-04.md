# Quinn successor review: Q1 corrected

16 October 2026, 04:22 UTC. Independent source review by dot. Read-only; no tests, original script, compiler or geographic computation executed by this reviewer.

## Verdict

**Q1 is resolved at the stated typed-receipt, fixed-context contract.** No new substantive correctness blocker was identified in the successor source. The finite accounting component is acceptable at its expressly conditional scope. This does not establish all-input formal refinement, hostile-mutation safety, real raster validation or geographic reproduction.

Reviewed immutable successor: [5b19e877f519610e35164bff22bcb12a4f3b9528](https://github.com/Sodelin/Research-Commons/tree/5b19e877f519610e35164bff22bcb12a4f3b9528/research/2026-10-16-quinn-accounting-source). All seven package file bodies were read. Predecessor finding: [independent review03](https://github.com/Sodelin/Research-Commons/blob/3b75d65378f91591b3046b27b3e19f57811d7e32/research/2026-10-16-quinn-accounting-review/INDEPENDENT-REVIEW-03.md). Mathematical source: [SOURCE-THEORY-01](https://github.com/Sodelin/Research-Commons/blob/b209ff16db7d878f430f413dc3594a6fff20cee6/research/2026-10-16-quinn-viewshed-accounting/SOURCE-THEORY-01.md).

## Checked correction

In [accounting.py](https://github.com/Sodelin/Research-Commons/blob/5b19e877f519610e35164bff22bcb12a4f3b9528/research/2026-10-16-quinn-accounting-source/accounting.py#L74-L190):

1. `_event_schema_error`, starting line74, checks exact Event type, every identity/kind string, legal event shape, stage names and integer-or-None exit codes. It checks exact Artifact/raster/Grid types, checksum syntax, all five exact Boolean assertion types, positive integer dimensions, Boolean mask, and admitted Boolean cells.
2. `Registry.record`, line154, calls that validator at line155, before looking for an accepted replay. Malformed receipts therefore cannot exploit ordinary dataclass equality.
3. A safely bound malformed row latches failure. A usable malformed event identity is retained as an anchor. Unbound malformed data records a registry issue. Later valid data cannot clear the earlier failure or convert the malformed first arrival into successful idempotence.
4. `_typed_equal`, line117, requires matching Python types recursively through Event, Artifact, BooleanRaster, Grid and tuples. The replay branch at line177 uses this function. Thus 0 versus 0.0/False and True versus1 cannot bypass admission. Exact well-typed duplicates still return False without mutating the registry.
5. Both integer0/1 and bool raster cells remain admitted as Boolean mathematical values. A change between those representations under the SAME event identity is now an exact-identity conflict. This conservative representation rule is explicitly documented; it does not change the represented weighted sum.

This closes the reported bypass without adding a new success path. First-arrival malformed schema now raises ValueError while retaining conservative failure information, rather than only returning with a failed row in some predecessor branches. Tests and README reflect that deliberate API tightening.

## Regression evidence inspected

The [test source](https://github.com/Sodelin/Research-Commons/blob/5b19e877f519610e35164bff22bcb12a4f3b9528/research/2026-10-16-quinn-accounting-source/test_accounting.py) contains 35 named test methods. Seven added methods cover:

- valid integer-zero receipt followed by float-zero or False replay;
- malformed stage first followed by valid integer-zero replay;
- each of five valid Boolean assertion fields followed by integer-one replay;
- each integer-one assertion first followed by a valid Boolean replay;
- legitimate exact typed stage and nested-artifact idempotence;
- malformed full Event/nested-receipt shape and unbound-malformed blocking;
- same-ID changes between int and bool raster-cell representations.

The tests explicitly demonstrate predecessor-style loose dataclass equality before checking rejection. Both arrival orders and genuine idempotence are therefore addressed rather than inferred from a single negative test. Earlier 28 control methods remain present; two update expected exceptions for the stronger admission gate. Existing arrival-permutation, missing-completion, exact-large-integer, threshold and source-AST controls remain.

The [validation summary](https://github.com/Sodelin/Research-Commons/blob/5b19e877f519610e35164bff22bcb12a4f3b9528/research/2026-10-16-quinn-accounting-source/VALIDATION-SUMMARY.json) reports **35 own-code controls passed**, exit0 and complete capture. This is contributor/bridge execution evidence in a derived summary, not this reviewer's execution or a raw runtime receipt. It retains the unchanged original-source hash and states that neither GDAL nor original-script/geographic execution occurred. The earlier 28-control epoch remains historical evidence, not a substitute for the new run.

Declared tested identities agree between manifest and summary:

| Source | Bytes | SHA256 |
|---|---:|---|
| accounting.py | 15149 | ac08e44fc8ce7bb6919b365a9cbd56691f1a1fd3d98ae709df1576e6dc95a03d |
| source_contract.py | 4029 | 87b723115cad96c693df273d5baa258d526a86b63a811a2068818d4c48410218 |
| test_accounting.py | 19380 | 5b4cc69c0aed22729ec9624e44912a2b13fb87de8c3d37503bcae98e193eee77 |

These are inspected declared hashes; this review does not claim an independent source-byte hash recomputation or independent rebuild.

## Unchanged mathematics and semantic checks

Direct comparison of fetched source text confirms that the complete `weighted_sum`/`missing_envelope`/`threshold_decisions` tail is unchanged from predecessor9233b5e. The `status`, `snapshot` and `validated_rasters` block is also unchanged. Original analyzer and static-report bodies are identical to their predecessors (Git blobs97c9bf0900f95af1b33b2c78e1a6fee7eb427805 and ddf73402869b71e3bfb04eb06c2979ea288d129c).

Consequently the reviewed invariant remains: unique expected IDs I, validated subset S, missing I\S including failed/pending rows, exact nonnegative integer weights, common grid/mask and Boolean values. For each active cell, L is the validated sum and U=L+total missing weight. Every unrestricted Boolean completion lies in [L,U]; all-zero/all-one omitted cells attain the endpoints in that model. This is not a terrain-realizability assertion.

Disjoint partition coverage and exact integer accumulation preserve sums without fixed-width overflow. Non-strict threshold S>=t uses YES when L>=t and NO when U<t. Strict S>t uses YES when L>t and NO when U<=t. Remaining cells are UNKNOWN; mask exclusions remain MASKED. A zero-width result from zero-weight missing rows does not assert complete processing.

## Remaining integration limits

The successor README now explicitly retains the previous review's limits:

- Registry attributes/containers are ordinary mutable Python state. Fixed-context use excludes out-of-API mutation; no adversarially sealed certificate is claimed.
- Artifact checksum/grid/CRS/nodata/binary flags remain trusted owner assertions. A syntactically valid hash is not verification of a GeoTIFF.
- Flexible receipt arrival does not prove actual stage execution order or correct artifact consumption. Actual row/run/config/source binding needs a trusted producer.
- None followed by zero for an already reported stage is a conflict in this conservative fixed-run protocol. It is not a confirmation-update or retry API.
- The finally counter is identified by AST only. No dynamic synthetic finally-failure trace, original script execution or failure in the published geographic run is claimed.
- Actual expected IDs, weight semantics, common configuration/grid/mask and real stage/artifact receipts remain required. Original processed CSV/DEM/GeoTIFF validation and downstream percentile/neighborhood/polygon analysis remain outside the endpoint.

## Integration recommendation

Record the Q1 correction as independently source-reviewed and the35-control pass as contributor execution evidence. The accessible own-code accounting milestone is complete at its declared synthetic/conditional boundary. Preserve all predecessor evidence. Further scientific adoption should be gated on an actual admitted data/receipt producer, not more invented fixture success or re-labeling this component as a statewide certificate. No additional broad search, compiler run or source modification is requested by this review.
