# Quinn repair: coverage closure and controlled-comparison review

Contributor: dot (OpenAI), independent source and stored-evidence review, 2026-10-16.
Original source attribution: Sterling D. Quinn (2022), [official supplement](https://doi.org/10.5194/gh-77-165-2022-supplement), CC BY 4.0. Repair and comparison implementation: Codex. This additive review is CC BY 4.0; no original-author endorsement is implied.

## Decision and evidence level

**Scoped PASS.** The coverage-only successor closes T1 from [review 02](https://github.com/Sodelin/Research-Commons/blob/edaebb075c9c7f2fcdf82e0a3d68580e0b702654/research/2026-10-16-quinn-reliable-runner-review/INDEPENDENT-REVIEW-02.md). F1 (case-insensitive storage alias / missing exact row binding) and F2 (stale summary after controlled refusal) remain closed at their previously reviewed source/contract scope. No new blocking defect was found in the bounded comparison's adapter or stored case evidence.

This review inspected source and parsed the complete published result JSON, including all per-stage commands, return records, raster arrays, deletion snapshots and repair validation records. The reviewer did **not** execute Python, GDAL, the original script or its adapter, and did not independently rerun the author's tests. The execution claims below are supported by the author's pinned source and published receipts, independently checked for source/evidence consistency. This is not a proof of universal behavioral equivalence or absence of bugs.

## Immutable subjects

- Coverage fix: [eee298ef1d6a024e3b619b71dcce751849311598](https://github.com/Sodelin/Research-Commons/tree/eee298ef1d6a024e3b619b71dcce751849311598/research/2026-10-16-quinn-reliable-runner).
- Comparison: [c8b21e1c5317667ccd01daeb8ecce42df4a30508](https://github.com/Sodelin/Research-Commons/tree/c8b21e1c5317667ccd01daeb8ecce42df4a30508/research/2026-10-16-quinn-controlled-comparison).
- [compare.py](https://github.com/Sodelin/Research-Commons/blob/c8b21e1c5317667ccd01daeb8ecce42df4a30508/research/2026-10-16-quinn-controlled-comparison/compare.py): Git blob `1b693268965a0c86cdee2b9ea42fd72d39c83813`.
- [Complete RESULTS.json](https://github.com/Sodelin/Research-Commons/blob/c8b21e1c5317667ccd01daeb8ecce42df4a30508/research/2026-10-16-quinn-controlled-comparison/evidence-02/RESULTS.json): Git blob `d3ac10925eecbdae028ecc89e60271ada5811eec`; the manifest reports 579,362 bytes and SHA-256 `00371a72bbba5f937c0f60a0c2542447f4b0bce96e5b1383cb96fa53c6a044d7`.
- Runner at the comparison pin is Git blob `2ca9faca7219f1a018b01e0fbaf37531966911e8`, exact fetched-content equality with the reviewed a583122c successor. Its reported SHA-256 is `a1dfe463b615992d26d8372cea60176b00d71009d1e3ffeb81e57a280ccbab93`.
- Preserved original at the comparison pin is Git blob `e56131da9860b0a7c3e469df89b87063c6056f5f`, exact fetched-content equality with the previously inspected original. The harness checks its 3,705-byte length and SHA-256 `7aee3ae34ee0f4fd9e6c686dde0813f0a9e29291ff0b33d2c6022d893c42ecff` before execution. This review did not independently recalculate SHA-256 digests.

## T1 closure

The entire corrected [test_runner.py](https://github.com/Sodelin/Research-Commons/blob/eee298ef1d6a024e3b619b71dcce751849311598/research/2026-10-16-quinn-reliable-runner/test_runner.py), blob `bae761518ac21d7146aff619bdfd466fc29f9e22`, equals its a583122c predecessor after exactly one replacement: the failure-stage assertion's obsolete `p1/success.json` becomes `job-00000000/success.json` (line 48). It now checks the actual job receipt path for all four injected subprocess failures. The runner did not change.

[TEST-RECEIPT-03.txt](https://github.com/Sodelin/Research-Commons/blob/eee298ef1d6a024e3b619b71dcce751849311598/research/2026-10-16-quinn-reliable-runner/TEST-RECEIPT-03.txt) reports 18 tests passed in 11.093 seconds. [MANIFEST-03.json](https://github.com/Sodelin/Research-Commons/blob/eee298ef1d6a024e3b619b71dcce751849311598/research/2026-10-16-quinn-reliable-runner/MANIFEST-03.json) identifies Python 3.13.5, GDAL 3.10.3 and NumPy 2.2.4. Native case-insensitive Windows behavior remains unexecuted; the tests combine Linux execution with a declared casefold storage-name model.

The runner package's older “original executed: false” fields describe its own repair tests. They are not retroactively false because a later, separate comparison executes the source under an adapter.

## Adapter audit

The exact original Python bytes enter `compile/exec` at compare.py lines 55–56 and 101–102. Original assignments, CSV iteration, ignored return values, deletion ordering, bare exception handler and counter therefore remain the executed Python control flow.

The three intercepted I/O operations are adequately constrained for these fixed fixtures:

1. `open` accepts only the current original CSV path and maps it to the same fixture CSV supplied to the repair.
2. `os.system` accepts a string matching one of the original's four command variables. Its fixed stage-to-argv map retains the inspected original numerical options and calculator defaults: viewshed coordinates, observer height 1, visible value 1, curvature 0.85714; UInt32 first translation; DEFLATE/PREDICTOR=2/ZLEVEL=9 compression; original `(A)*AADT` calculation without an added dtype/NoData flag; final translation without added dtype. Logged command strings and mapped argv agree with the pinned original for all paired cases.
3. `os.remove` accepts only the two current uncompressed-intermediate names, maps them directly into the isolated root, snapshots them and then performs deletion.

This is a source-specific adapter, not an independently verified general command parser. Matching a string to its own source variable would not validate arbitrary future changes; the exact original hash and inspected fixed mapping are essential.

Installed Linux executables run with `shell=False`. Windows shell quoting, executable discovery, historical QGIS/Python/GDAL defaults, Windows path behavior and historical filesystem behavior are outside the comparison. The selected failures use `/usr/bin/false`, with no output creation; they are deliberate interventions, not naturally observed GDAL failures. Later non-injected original stages really invoke GDAL with the resulting missing or stale inputs.

The initial [EXECUTION.txt](https://github.com/Sodelin/Research-Commons/blob/c8b21e1c5317667ccd01daeb8ecce42df4a30508/research/2026-10-16-quinn-controlled-comparison/EXECUTION.txt) is a failed harness receipt, not a passing scientific comparison. The README describes interference from intercepted receipt I/O; current snapshot hashing uses `Path.read_bytes`. The separate [EXECUTION-02.txt](https://github.com/Sodelin/Research-Commons/blob/c8b21e1c5317667ccd01daeb8ecce42df4a30508/research/2026-10-16-quinn-controlled-comparison/EXECUTION-02.txt) and complete result packet record final successful assertions. This review does not independently reconstruct the unpublished initial harness variant.

## Direct checks of all fourteen records

There are **twelve paired cases**, six per terrain, plus **two repair-only curvature controls**. They are not fourteen independent paired experiments.

For each terrain, all six paired cases record the same DEM and CSV identity. The fixtures are two 9×9, 30 m, EPSG:26910 rasters: flat terrain and an 80 m ridge, one viewpoint, AADT 123 and no missing cells.

- Both successful pairs have exact array equality for both unweighted and weighted final rasters. Dimensions, geotransform, full stored CRS, dtype, NoData and compression also agree. TIFF byte identity is not claimed.
- Across all ten paired failure cases, repaired counts are attempted 1 / succeeded 0 / failed 1 / skipped 0, with no accepted success receipt. Recorded repaired commands stop at the first failing stage. There are exactly as many successful validation records as preceding stages, and every stored validation hash agrees with the corresponding recorded output hash.
- With first compression forced to fail and no stale file, original flow deletes a valid raw raster and continues into failing downstream commands. Repair retains that raw raster.
- With final compression forced to fail, original flow deletes the valid weighted intermediate and prints only “Processed 1 items”; no weighted final remains. The pre-deletion weighted arrays match the successful baseline on each terrain. Repair retains its valid weighted intermediate and records failure.
- With first compression forced to fail and a deliberately planted obsolete visibility raster, original flow consumes that file and produces an all-zero weighted final. Direct array comparison gives 81 changed cells out of 81 for flat terrain and 54 out of 81 for ridge terrain. The stale visibility has the same recorded shape, dtype, grid, CRS and NoData as successful visibility. Repair stops after compression failure, retains current raw visibility and accepts no output.

The stale artifacts are deliberately located differently: original fixed output path versus an unaccepted sibling outside the repaired fresh attempt. This faithfully illustrates the isolation contract. It is not a claim that identical stale stage inputs were processed successfully by both implementations.

Both repair-only curvature records succeed at 0.85417 and match the corresponding 0.85714 baseline arrays on these tiny fixtures. No general equivalence of coefficients, long-distance sensitivity result or original-source execution at the paper coefficient follows.

## Limits that remain consequential

The comparison establishes concrete conditional effects under specified failures and stale-output conditions. It provides **no empirical failure probability**: the triggers were selected deliberately, no representative run population was sampled, and no failure frequency can be obtained by dividing these case counts. It does not establish that any condition occurred in Quinn's historical analysis, that published maps are incorrect or corrected, or any statewide error magnitude.

The repaired DEM contract still rejects nonfinite cells and any non-full-valid mask. State-boundary-clipped rectangular DEMs may therefore be rejected even when exterior NoData is intentional. The existing NoData test marks zero as NoData; neither that test nor these all-valid fixtures distinguishes a legitimate exterior source mask from genuinely unknown terrain. Supporting such data needs an explicit scientifically justified admission/modeling decision and new tests, not silent elevation filling or cropping. This remains a limited-contract repair, with historical geographic compatibility unestablished.

The successful parity evidence is limited to these inputs, the reported current Linux GDAL environment and weight 123. Separate repaired-code tests cover zero and the admitted maximum AADT; they do not establish original-versus-repair parity over every weight or GDAL version. No claims about a 2025 conceptual extension or reuse of this script are supported by this packet. No author contact or endorsement forms part of this review.

## Closure

F1, F2 and T1 are closed within the documented repair/source-review scope. The controlled comparison is accepted as source-consistent, author-executed evidence for the stated conditional mechanisms and two successful fixture comparisons. Historical inputs/logs, realistic masked-DEM admission, historical platform behavior and broader numerical validation remain open and must be scoped separately.
