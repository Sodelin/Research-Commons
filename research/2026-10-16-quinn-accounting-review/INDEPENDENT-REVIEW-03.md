# Independent Quinn source/evidence review

16 October 2026, 03:36 UTC. Reviewer: dot, existing prior/review role. Read-only review; no Python source or tests executed and no compiler used.

## Disposition

The deterministic missing-row envelope, exact integer accumulation and threshold decisions are sound at their stated conditional inputs. The published implementation is a useful finite accounting component. One concrete malformed-replay admission defect should be fixed before describing all receipt admission as exact/type-strict. No false weighted envelope was identified for an unmodified Registry populated with admitted trusted receipts. This review does not establish actual geographic correctness or universal implementation refinement.

Source snapshot: [9233b5effbd20cabac34a691c5e1a309b3bd855b](https://github.com/Sodelin/Research-Commons/tree/9233b5effbd20cabac34a691c5e1a309b3bd855b/research/2026-10-16-quinn-accounting-source). All seven published file bodies were read, including all three Python bodies. Earlier mathematical contract: [SOURCE-THEORY-01](https://github.com/Sodelin/Research-Commons/blob/b209ff16db7d878f430f413dc3594a6fff20cee6/research/2026-10-16-quinn-viewshed-accounting/SOURCE-THEORY-01.md).

## Finding Q1: equality-based replay bypasses exact-type admission

In [accounting.py](https://github.com/Sodelin/Research-Commons/blob/9233b5effbd20cabac34a691c5e1a309b3bd855b/research/2026-10-16-quinn-accounting-source/accounting.py), `Registry.record` first handles an already seen event ID by `if old == event: return False`. The generated dataclass equality uses ordinary Python value equality. Only after this branch does a new stage receipt require `type(event.exit_code) is int`.

Concrete source-derived trace, not an executed test:

1. Record Event('same', 'a', 'run-1', 'config-1', 'stage', stage='viewshed', exit_code=0).
2. Replay that event ID with exit_code=0.0, or exit_code=False, and all other fields unchanged.
3. Python has 0 == 0.0 == False. Dataclass equality therefore treats the new receipt as equal and returns False without rejecting it or latching failure.

The same weakness affects exact-replay claims for artifact assertion fields: True and 1 compare equal although `valid_for` deliberately requires each assertion `is True`. The first malformed arrival is rejected; the malformed duplicate can bypass that check.

Impact: a specific admission/identity promise is weaker than advertised. In the displayed trace, the earlier valid receipt remains stored, so the arithmetic result is unchanged. This is not a demonstrated false geographic certificate or false L/U bound. It is a correctness issue for a public API claiming malformed receipt rejection and exact idempotence.

Recommended repair: validate/canonicalize the full event and nested receipt schema before the idempotent replay branch, or define replay identity with explicit type-sensitive canonical fields. Preserve exact duplicate acceptance, conflict latching and unknown-ID blocking. Add controls for valid-zero then float-zero/False replay and true assertion then integer-one replay, as well as the reverse arrival order. Do not merely add a test that repeats a well-typed event.

## Mathematical checks

- For fixed expected IDs I, `validated_rasters()` supplies S and `missing_envelope` uses every i in I\S, including failed and pending rows. No missing row is silently taken as visibility zero in the upper bound.
- Exact natural weights are enforced with `type(value) is int`, excluding bool, floats, negative values and fractional weights. This is narrower than the mathematical nonnegative-real theorem and is a legitimate implementation domain.
- For every active cell, `weighted_sum` computes L=sum(i in S) w_i v_i. Each missing Boolean term lies in [0,w_i]; U=L+sum(i in I\S)w_i. The all-zero/all-one completions attain these endpoints in the unrestricted Boolean-completion model. Terrain-realizable joint completions are not claimed.
- `partitions` must cover exactly the supplied raster IDs, with no duplication. Built-in Python integer addition has no fixed-width overflow. Reordering/disjoint partitioning preserves the mathematical exact sum. Masks yield None and are excluded from threshold claims.
- Non-strict S>=t: YES iff L>=t, NO iff U<t. Strict S>t: YES iff L>t, NO iff U<=t. These are the correct boundary conventions. Thresholds accept exact integer/Fraction values and reject Boolean/float inputs. Invalid endpoint order/shape and mixed masked/nonmasked bounds are rejected.
- A zero-weight missing row can yield an exact zero-width envelope while `all_expected_validated` remains false. This correctly distinguishes value determination from complete processing.

## Accounting and provenance checks

- Validated status requires four distinct named zero-exit stages and a valid artifact assertion. Attempted is separate from the disjoint validated/failed/pending partition. Nonzero and stale/wrong-configuration receipts latch failure; unknown IDs create a registry-wide issue blocking aggregation.
- Missing stage outcomes remain pending. A None stage followed by zero for that same stage is currently treated as a conflicting outcome and latches failure. This conservative choice should remain documented: this is not a live pending-to-confirmed update protocol; a retry requires a new registry/run.
- Receipt arrival order can vary. The wrapper does not establish actual dependency execution order or that all stages consumed one another's correct outputs. Artifact checks, checksum correctness, CRS, transform and nodata are explicitly trusted owner assertions. The hash string is syntax-checked, not recomputed from a GeoTIFF.
- `Registry` context fields and containers are ordinary mutable Python attributes. The fixed-registry theorem assumes callers do not mutate them outside the intended methods. The package does not provide an adversarially sealed certificate type. A production adapter should freeze/read-protect its context or state this API assumption explicitly.
- Stage receipts and artifact receipts share row/run/config names but do not carry a cryptographically authenticated production history. This remains an integration premise, as the README correctly states.

## Static analyzer and original source

[source_contract.py](https://github.com/Sodelin/Research-Commons/blob/9233b5effbd20cabac34a691c5e1a309b3bd855b/research/2026-10-16-quinn-accounting-source/source_contract.py) hashes and AST-parses source bytes; it neither imports nor executes the original script. Its pinned analyzer reports four ignored `os.system` results, two removals, the finally counter and fields extracted before entering try. The [static report](https://github.com/Sodelin/Research-Commons/blob/9233b5effbd20cabac34a691c5e1a309b3bd855b/research/2026-10-16-quinn-accounting-source/STATIC-SOURCE-REPORT.json) preserves the necessary qualification: failures before try do not increment that finally counter. The 0.85417 paper / 0.85714 script discrepancy is recorded without claiming practical inequivalence or a failed published run.

The analyzer is deliberately narrow and hash-bound. It is not a general semantic verifier for arbitrary Python or shell commands. Original source attribution and official archive identity agree with the earlier theory packet.

## Recorded evidence and test gaps

The [28-test body](https://github.com/Sodelin/Research-Commons/blob/9233b5effbd20cabac34a691c5e1a309b3bd855b/research/2026-10-16-quinn-accounting-source/test_accounting.py) includes all 120 five-event arrival orders, 64 missing-cell completions, large-integer sums, threshold ties, invalid inputs, stale/conflicting identities, hash binding and an AST-only side-effect sentinel. These are useful finite controls, not 28 theorems or all-input proof.

The [validation summary](https://github.com/Sodelin/Research-Commons/blob/9233b5effbd20cabac34a691c5e1a309b3bd855b/research/2026-10-16-quinn-accounting-source/VALIDATION-SUMMARY.json) reports 28 passing controls, exit zero and complete capture. It explicitly labels itself a derived sanitized summary rather than a raw execution receipt. This reviewer read that contributor evidence, not an independent fresh execution. Its source identities match the manifest's declared tested identities; no independent byte-hash recomputation is claimed here.

The tests reject malformed first-arrival stage codes but omit Q1's malformed same-ID replay. They verify the original finally counter syntactically, rather than executing a synthetic finally-failure trace. Do not claim that specific dynamic trace was tested merely because the static count test passed.

## Integration decision

Accept the finite mathematics and retain the execution evidence at its stated level. Fix Q1 and preserve/retest the original bytes and new regression controls before stronger receipt-admission adoption. Then the remaining external integration requires the actual expected-ID universe, exact observer-weight interpretation, common grid/mask/configuration, and trusted stage/artifact production. Original processed CSV/DEM/GeoTIFF inputs and actual geographic validation remain outside this package. No GDAL installation, original-script execution, statewide result, Lean verification or canonical solver adoption follows.
