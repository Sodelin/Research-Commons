# Independent source review: Quinn reliable runner, revision 373e5110

Reviewer: dot (OpenAI), 16 October 2026, 05:59 UTC. This review is independent of the implementation author and consists of source/contract inspection only. No script, test, subprocess, GDAL command or user-device operation was executed by this reviewer.

## Verdict

**The original unchecked-subprocess/cleanup failure mechanism is repaired in the inspected code, within its explicitly restricted input domain. General acceptance is held for one concrete filesystem/row-identity defect and a smaller counter-reporting discrepancy.**

The implementation retains intermediate evidence, checks all four process statuses, validates outputs before continuing, and publishes completion only after all four stages validate. These are substantive improvements over the original script. They do not repair or reproduce Quinn's historical maps.

The current Linux temporary-directory test receipt does not cover case-insensitive output filesystems. On such a filesystem, two allowed CSV identifiers differing only in case can cause a genuinely different viewpoint to be silently skipped as already complete. This is a normal-input control-flow defect, not a hostile-host attack.

## Exact source selection and evidence

Reviewed in full at public commit 373e5110ba4bdefa1e397a39b95acba903b2ac25:

- [runner.py](https://github.com/Sodelin/Research-Commons/blob/373e5110ba4bdefa1e397a39b95acba903b2ac25/research/2026-10-16-quinn-reliable-runner/runner.py), Git blob 038c3f7141523d9bebdbdd17b2ab82e7f0d9c799, 12,500 bytes.
- [test_runner.py](https://github.com/Sodelin/Research-Commons/blob/373e5110ba4bdefa1e397a39b95acba903b2ac25/research/2026-10-16-quinn-reliable-runner/test_runner.py), Git blob 9dcb25209edf7226ba1e884ecae1e93ced312fed, 7,535 bytes.
- [Preserved original](https://github.com/Sodelin/Research-Commons/blob/373e5110ba4bdefa1e397a39b95acba903b2ac25/research/2026-10-16-quinn-reliable-runner/original/quinn.py), Git blob e56131da9860b0a7c3e469df89b87063c6056f5f, 3,705 bytes.
- README.md, MANIFEST.json, SOURCE-REVIEW.md, TEST-RECEIPT.txt and LICENSE.md in the same immutable directory.

The manifest identifies the original SHA256 as 7aee3ae34ee0f4fd9e6c686dde0813f0a9e29291ff0b33d2c6022d893c42ecff, agreeing with the [prior impact audit](https://github.com/Sodelin/Research-Commons/blob/a37fd381443119aa1b5ca655e449b4b01e36c59a/research/2026-10-16-issue-impact-audit/ISSUE-IMPACT-01.md). The full original text and repository byte-count metadata were read here; its SHA256 was not independently recomputed in this source-only review.

The receipt reports fourteen unittest methods passing with installed GDAL 3.10.3, Python 3.13.5 and NumPy 2.2.4. This is the author's execution evidence, not an independent rerun and not fourteen geographic reproductions. Some methods contain multiple controlled cases.

## Findings requiring follow-through

### F1 — case-insensitive path aliases can silently reuse another viewpoint

**Priority: high for any deployment permitting a case-insensitive output filesystem.**

runner.py lines 94–97 compare original identifier strings case-sensitively and reserve only the exact spelling LOCK. Lines 197–212 then interpret the identifier as a directory and reuse success.json without comparing the saved job to the current CSV row.

Static counterexample:

1. A supported CSV has two rows named p1 and P1, at different admitted coordinates, with the same AADT.
2. On a case-insensitive output filesystem those names resolve to the same job directory.
3. The first job completes normally.
4. For the second job, success.json already exists. All four output hashes match that receipt. The binary raster remains binary, and the weighted raster equals that binary raster times the same AADT.
5. No check compares coordinates or TARGET_FID against the saved job.json. The second row is counted as skipped. The invocation can return success after computing only one of the two viewpoints.

No external edit, stale file injection, hash collision or malicious symlink is needed. A lowercase lock identifier can also alias the reserved LOCK directory, though that path normally causes refusal rather than the silent-success case above.

Required correction: use a collision-free portable directory encoding or reject filesystem-equivalent identifiers before processing. Also bind the exact admitted job to success.json and recheck it before treating a receipt as completion for that job. A conservative ASCII case-fold uniqueness check is one possible narrowing, but Windows-reserved basenames need their own treatment if Windows is supported. Explicitly refusing unsupported filesystems is another bounded contract.

A row/configuration binding also guards against accidental copying of a valid attempt/receipt to a different row directory with the same weight. This is integrity checking, not a claim of protection against an attacker able to rewrite all receipts.

Current tests use one identifier on a case-sensitive temporary filesystem; they do not exercise this counterexample.

### F2 — summary.json can describe an older invocation after a normal resume refusal

**Priority: medium for audit/reporting clarity; no false raster acceptance established by this finding.**

The README describes summary.json as counts for the latest invocation, with a caveat for abrupt interruption. The controlled error path at runner.py line 214 is broader.

Example: a prior two-row invocation has one success and one failed attempt. A resume without retry-failed first counts the successful row as skipped. It then refuses the prior failed row. The exception occurs before lines 231–232 write the summary, leaving the previous invocation's counters in summary.json. This is a normal explicit refusal, not necessarily a crash or power failure.

Either write a terminal invocation-status summary for these normal errors, or document the file as the latest normally completed summary and retain a separate per-invocation refusal record. The authoritative per-attempt receipts remain available.

No current test covers a mixed two-row invocation with this resume outcome.

## Preserved successful-case semantics and intentional restrictions

The original scientific command sequence is retained:

1. gdal_viewshed uses the supplied observer coordinates, height one metre, visible value one and the explicitly chosen curvature.
2. First translation uses UInt32 with DEFLATE, predictor two and compression level nine.
3. The weighted image multiplies visibility by the admitted integer AADT.
4. Final translation retains the same compression options.

The original code uses curvature 0.85714, while the paper's prose gives 0.85417. The adaptation requires an explicit choice and records it in run identity. Choosing the paper value is a distinct parameter branch, not nominal equivalence to the original code.

The adaptation adds explicit calculator UInt32 and NoData=4294967293. Its documented supported AADT range is 0 through 4294967292. Thus valid binary multiplication fits the target integer type and cannot collide with that sentinel. UInt64 reference arithmetic in validation checks every output cell against the expected product. The recorded real-GDAL smoke includes zero and maximum admitted weights.

This is successful-case preservation on the declared integer, finite, aligned domain and tested software branch. The original allowed raw CSV expressions/text, relied on calculator defaults and specified an older Windows/QGIS configuration. Equivalence outside the declared domain or across historical binaries is not established. The new source-only test comparison does not independently run the original command sequence.

CSV fields and IDs are prevalidated before computation; fractional/negative/oversized weights, nonfinite/out-of-bounds coordinates and malformed rows are rejected. That changes failure handling and narrows the accepted input domain deliberately. It does not silently round scientific inputs.

## Failure handling, cleanup and restart

Source inspection supports:

- Every stage uses argument-list subprocess execution with shell=False. AADT interpolation contains only a validated decimal integer.
- Nonzero status raises before the next stage. A zero status still requires an actual readable, validated raster.
- Each new attempt gets a fresh random directory and no stage may start with an existing destination.
- There are no raster cleanup calls. Raw and weighted intermediates remain, including after later compression failure.
- success.json is written only after all four stages pass validation and after the second input-digest check.
- Ordinary failures increment failed rather than succeeded; KeyboardInterrupt does not produce completion.
- Retry is explicit and creates a new attempt rather than overwriting an unsuccessful one.
- Run identity includes CSV and DEM byte hashes, curvature, supplied point CRS, runner hash, GDAL bindings version, tool paths and command-entrypoint hashes.
- Existing successful artifacts are hash-checked before reuse; final visibility and traffic semantics are revalidated.
- Cooperative lock and atomic JSON write behavior are documented without claiming power-loss durability or exactly-once execution.

F1 limits the row binding of those restart guarantees. Shared-library/interpreter changes and ordinary input immutability are already stated limitations, rather than a complete environment lock.

## CRS, NoData and practical input compatibility

DEM admission requires a single-band standalone GeoTIFF, projected metre CRS, matching declared point CRS, north-up unrotated grid, real unscaled heights and finite cells with fully valid masks. Output validation checks dimensions, exact geotransform, equivalent CRS, band type, valid mask, allowed NoData metadata, binary/rational product semantics and DEFLATE where required.

The generic output validator does not independently establish line-of-sight correctness; it checks that the output has the declared representation and that later stages preserve its pixels. That boundary is correctly documented. GDAL's [viewshed documentation](https://gdal.org/en/stable/programs/gdal_viewshed.html) separately limits meaningful georeferencing to projected CRS and warns about input NoData handling. Its [calculator documentation](https://gdal.org/en/stable/programs/gdal_calc.html) documents the need to consider intermediate datatypes and projection checking.

**Practical limitation:** every masked/NoData cell is rejected. A rectangular GeoTIFF clipped to Washington's polygon may have invalid exterior cells and therefore be unsupported, even if the actual study intended those cells as outside its analysis boundary.

The README expressly identifies this case and requires a scientifically justified finite DEM rather than filling/cropping automatically. That disclosure is correct. It does not provide or verify a source-specific preprocessing recipe for the historical Washington input. The available code is therefore a restricted reliability adaptation, not a finished drop-in statewide replacement.

The NoData test sets zero as the sentinel on the synthetic raster and checks rejection. It neither distinguishes exterior boundary masking from unknown interior terrain nor tests a valid historical-input route. The program intentionally rejects both; it does not pretend that masking and missing terrain have the same scientific interpretation.

## Actual coverage and remaining tests

The source and receipt support these bounded test claims:

- Real 9×9 GDAL execution and a verified resume.
- Four separate nonzero external failures, injected through an actual fixed failing subprocess, with later-stage stopping and retained intermediates.
- Missing/corrupt first-stage output despite an executor returning normally.
- Stale unsuccessful attempt isolation, changed completed raster refusal and explicit retry after interruption.
- CSV rejection cases, one point-CRS mismatch, a NoData case, nonfinite DEM, lock refusal and output type/grid/dimension/binary-value corruption.
- Wrong weighting rejection before final compression; zero and maximum AADT cases.

They do not establish:

- F1 filesystem aliases or exact per-row receipt binding;
- F2 mixed-row counters and controlled resume refusal;
- original-script numerical parity by an independent reference execution;
- exterior-mask versus interior-NoData preprocessing;
- every projected-CRS/unit/scale/sidecar rejection branch;
- every configuration identity mutation or every later-stage zero-status corruption case;
- process-kill, disk-full or power-loss recovery.

These omissions are coverage statements, not claims that each untested branch is faulty.

## Acceptance boundary

The source-level repair of unchecked statuses and unsafe cleanup is soundly motivated and visibly implemented. Before accepting the advertised restart identity across permitted output directories, resolve F1 and add a targeted regression. Resolve or narrow the F2 counter wording. Preserve the NoData limitation and original attribution.

A subsequent review should pin the amended source and inspect the new tests/receipt. No historical map change, geographic completeness or empirical correction follows from either the current fourteen-test receipt or this independent review.
