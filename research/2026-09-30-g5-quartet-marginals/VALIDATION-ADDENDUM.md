# Validation addendum: structural hybrids must have inheritance entries

Session G5-QUARTET-MARGINALS-20260930. Evidence: executed extracted-validator regression, not a full replay or independent audit of the older script.

## Defect and exact scope

The older research/2026-09-30-calendar-metric-g-continuation/verify_g5.py, Git blob 6f76613b69b12bda1633e398c45529c461d56765, constructs its hybrid set from the keys of the supplied inheritance dictionary. It does not require those keys to equal the actual indegree-two vertices. Its validation can therefore accept a structurally hybrid source record with the hybrid probability omitted and skip that hybrid's child-bridge test.

`check_validation_addendum.py` retains the extracted constructor/validation logic, with formatting normalized. An otherwise valid one-hybrid fixture with an empty inheritance dictionary is accepted by that extracted validator. `validate_source_record.py` rejects it by comparing the dictionary keys to the structural indegree-two set. It also checks interior weights, labels, leaf correspondence, edge endpoints and unique edge IDs. It supplements, rather than replaces, the full graph admission checks.

## Executed result

The regression returned PASS: old extracted validation accepts the malformed record; the supplemental guard rejects it; all 14 actual source records from the completed quartet suite pass the guard. This is a schema-validation defect, not an admitted equal-law/different-target example. The mathematical theorem already requires an interior inheritance probability at EVERY structural hybrid.

The new quartet suite uses the original local Source implementation, which separately computes the structural hybrids and rejects missing weights. The extra key-set guard was run on all actual fixtures after that suite. It is not falsely reported as code that the earlier suite had already called.

## Preservation and repair

The older published script is left intact for provenance. Before constructing its Source object, apply validate_source_record(record), then retain its existing graph/time/bridge/LSA/planarity checks. The exact regression is reproduced after the full quartet suite by:

```bash
python -B check_validation_addendum.py
```

No existing valid source, target, probability calculation or theorem conclusion was silently changed. Acceptance of this correction is separate from independent proof acceptance of G5.
