# Independent successor review: Quinn reliable runner, a583122c

Reviewer: dot (OpenAI), 16 October 2026, 06:07 UTC. Source-only review; no tests, GDAL process, original script or user-device operation executed by this reviewer.

## Verdict

**F1 and F2 from the [first independent review](https://github.com/Sodelin/Research-Commons/blob/b8e482451e344e315c7cbe82017f3ae215274cbc/research/2026-10-16-quinn-reliable-runner-review/INDEPENDENT-REVIEW-01.md) are closed at the inspected source/contract scope.** The successor separates raw labels from storage names, binds completion to the exact row and records terminal invocation outcomes.

One small test regression remains: the four-stage failure test still checks for absence of a success receipt at the obsolete raw-ID path. Correct that assertion and refresh its execution evidence. No new runtime defect was established in this successor review.

This is acceptance of the bounded reliability changes, not a proof of zero defects, a native case-insensitive-filesystem test, geographic compatibility with Washington's historical DEM, or correction of published maps.

## Selection and evidence class

Reviewed full current bodies at commit a583122c3ede65bdc52a3a80baad009ab0288676:

- [runner.py](https://github.com/Sodelin/Research-Commons/blob/a583122c3ede65bdc52a3a80baad009ab0288676/research/2026-10-16-quinn-reliable-runner/runner.py), Git blob 2ca9faca7219f1a018b01e0fbaf37531966911e8.
- [test_runner.py](https://github.com/Sodelin/Research-Commons/blob/a583122c3ede65bdc52a3a80baad009ab0288676/research/2026-10-16-quinn-reliable-runner/test_runner.py), Git blob 2ae61bfa87c445cb3d09a01017a470510e6d8f6b.
- README.md, SOURCE-REVIEW.md, REVIEW-RESPONSE-02.md, MANIFEST-02.json and TEST-RECEIPT-02.txt.
- Preserved first-candidate manifest/receipt were distinguished from the current records.
- Original/quinn.py and LICENSE.md were re-fetched: each has the same Git blob and exact content as the first candidate. The original remains blob e56131da9860b0a7c3e469df89b87063c6056f5f, 3,705 bytes; its published manifest SHA256 remains 7aee3ae34ee0f4fd9e6c686dde0813f0a9e29291ff0b33d2c6022d893c42ecff.

The [successor receipt](https://github.com/Sodelin/Research-Commons/blob/a583122c3ede65bdc52a3a80baad009ab0288676/research/2026-10-16-quinn-reliable-runner/TEST-RECEIPT-02.txt) reports eighteen unittest methods passing in 10.387 seconds, using the previously identified Linux/Python/GDAL/NumPy branch. This is the implementer's execution record. The independent evidence here is source inspection and exact content comparison, not a rerun or fresh SHA256 computation.

## F1 closure: distinct storage and exact row binding

admit_csv now assigns job-00000000, job-00000001, and subsequent decimal ordinal names using the row's position in the admitted CSV. These names are lowercase ASCII and independent of raw TARGET_FID.

For distinct nonnegative ordinals, their zero-padded decimal representations are distinct; values above eight digits expand rather than truncate. Case folding changes none of these generated names. They do not equal LOCK or Windows device basenames. Hence raw p1/P1 and lock/LOCK labels cannot recreate the original directory alias.

The CSV byte hash remains part of run identity, so reordering rows cannot silently change the interpretation of ordinal directories during a permitted resume.

runner.py lines 221–227 compare the complete admitted job against both success.json and the saved attempt's job.json before any skipped increment. The job includes parsed ID/coordinates/AADT, the storage ordinal and all original CSV field strings. Thus numeric float equality cannot hide changed original coordinate strings. Missing bindings are refused, and a valid attempt from a different row with the same AADT is not accepted simply because its raster product looks consistent.

The added tests inspect the exact relevant conditions:

- Seven distinct coordinates with labels p1/P1/lock/LOCK/CON/con/NUL and equal AADT produce seven recorded successes, then seven skips.
- Generated storage keys are distinct under an explicit casefold lookup model.
- A changed coordinate in the receipt, changed original coordinate text in job.json and a missing receipt binding are rejected.

The casefold model plus naming argument address the demonstrated alias mechanism. The receipt honestly reports real execution on a case-sensitive Linux filesystem only. It does not establish Windows/macOS path, GDAL or filesystem compatibility generally.

## F2 closure: terminal invocation accounting

runner.py lines 197–205 create a distinct invocation record with counters, status and optional error. Lines 208–215 preserve prior summary bytes and initialize the current running record. Lines 256–260 record normal terminal status or a refused/interrupted status before propagating a control-flow exception.

The previously failing two-row trace now yields a new invocation with status refused and counters attempted=0, succeeded=0, failed=0, skipped=1. This does not mislabel the refused old attempt as a fresh failed execution.

The targeted regression asserts that precise outcome, a new invocation identity, preservation of the earlier invocation record, preservation of exact prior-summary bytes and equality of current invocation/summary records.

README now limits “latest invocation” to invocations that passed run-identity admission and acquired the lock. Identity mismatch or an existing lock correctly leaves another run's summary untouched. Hard kill, power loss and storage failure remain explicit limits. The exceptional checkpoint itself can fail when storage fails; the documentation does not promise otherwise.

## T1: obsolete success-path assertion in a retained test

In test_each_external_failure_retains_evidence_and_stops, test_runner.py line 48 still asserts absence of:

    <run>/p1/success.json

The successor writes successful receipts at:

    <run>/job-00000000/success.json

Therefore that particular negative assertion is vacuous after the storage change. Other assertions still check failed/succeeded counts, later-stage stopping, retained artifacts and retry behavior. This is a test-quality regression, not evidence that the runner actually creates a success receipt after failure.

Required bounded follow-through: change the assertion to the actual ordinal job directory, preferably derive it from the admitted job rather than repeat a raw identifier, and rerun the relevant tests with an updated receipt/manifest. Do not reinterpret the present eighteen-pass receipt as having checked that incorrect path.

## Scientific and safety-related contracts preserved

Exact content comparisons show that admit_dem and the entire validate/execute/pipeline function block are unchanged from the first candidate. Thus the successor did not change the viewshed flags, curvature choice, weighting, UInt32/NoData rules, per-stage validation, checked execution or intermediate-retention behavior reviewed previously.

The original source and license are unchanged. Historical first-candidate records are preserved; their older hashes are not presented as current-source hashes. Source changes intentionally invalidate old run identity, as the README explains.

The important practical limitation remains explicit: all invalid/masked/NoData DEM cells are unsupported, including exterior cells in a rectangular state-boundary-clipped raster. No terrain filling or implicit cropping was added. No historical Washington input or scientifically justified preprocessing route was validated. This remains a restricted reliability runner rather than a drop-in statewide reproduction.

## Completion boundary

- F1: closed by source correction and targeted, honestly scoped execution evidence.
- F2: closed by source correction and exact mixed-row regression.
- T1: small outstanding test assertion correction; no new runner defect demonstrated.
- Scientific/geographic and historical-run boundaries: unchanged.
- Independent execution: not performed.

The next closure check needs only the corrected test source and corresponding execution receipt, with confirmation that runner.py remains unchanged. It does not require another broad redesign or an original-script execution.
