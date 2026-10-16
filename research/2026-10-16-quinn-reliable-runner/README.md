# Reliable per-viewpoint runner: additive Quinn script repair

**Successor correction:** see [REVIEW-RESPONSE-02.md](REVIEW-RESPONSE-02.md) for the case-insensitive storage and invocation-summary fixes. Current hashes/tests are in `MANIFEST-02.json` and `TEST-RECEIPT-02.txt`; the original manifest/receipt describe the preserved first candidate.

Contributor: Codex, 2026-10-16. Based on Sterling D. Quinn's [official 2022 supplement](https://doi.org/10.5194/gh-77-165-2022-supplement), accompanying [What can we see from the road?](https://doi.org/10.5194/gh-77-165-2022). The exact 3,705-byte original is preserved in `original/quinn.py` and **must not be executed for these tests**. This package is an independently prepared reliability adaptation, not an author-approved release or a correction of historical maps.

`runner.py` retains the nominal single-viewpoint sequence: GDAL viewshed (observer height 1 m, visible=1, invisible=0), UInt32 DEFLATE compression, multiplication by integer AADT, then DEFLATE compression. It does not perform statewide aggregation, reconstruct viewpoints or modify terrain. The [historical-input audit](../2026-10-16-quinn-input-reconstruction/RECONSTRUCTION-03.md) remains separate.

## Requirements and quick start

Use a Python interpreter with NumPy and the GDAL Python bindings. `gdal_viewshed`, `gdal_translate` and `gdal_calc.py` must already be on PATH. The tested environment uses `/usr/bin/python3`, GDAL 3.10.3 and NumPy 2.2.4. No installation is performed by the package. Other versions require validation; command entrypoint hashes and GDAL bindings version are recorded, but dependency libraries/interpreters are not a complete environment lock.

Run the isolated synthetic tests (temporary 9×9 rasters only):

```sh
/usr/bin/python3 -m unittest -v test_runner
```

For your own admitted inputs, choose a NEW output directory and explicitly select curvature:

```sh
/usr/bin/python3 runner.py --csv points_to_analyze.csv \
  --dem clipped_nad83_1arcsec.tif --point-crs EPSG:26910 \
  --elevation-metres --curvature 0.85714 --run runs/example-001
```

`EPSG:26910` is an example, not an inferred guarantee about the original file. Supply the actual CSV coordinate reference system. **Curvature is required:** `0.85714` matches the original script; `0.85417` matches the paper's prose. Neither is silently selected or described as empirically correct. The elevation-metres flag attests that unlabelled DEM heights really are metres; code cannot infer their physical units.

The command exits 0 for all successes/verified skips, 1 for recorded job failures, and 2 for admission or run-level errors. A Python interruption is not success. Inspect receipts rather than treating the presence of a TIFF as completion.

## Admission and validation contract

- CSV requires unique `X,Y,TARGET_FID,AADT` column names; extra columns are ignored. Rows must be structurally complete. IDs are unique case-sensitive labels of 1–80 letters/digits/underscore/hyphen. They are never used as filesystem names. Labels such as `p1`, `P1`, `lock`, `LOCK`, `CON` and `NUL` remain distinct data labels. Coordinates must be finite and inside the DEM's half-open pixel extent, in exactly its CRS. Python/GDAL double coordinates are used; there is no implicit reprojection, snapping or decimal-precision claim.
- AADT must be a nonnegative decimal integer, at most **4,294,967,292**. Fractional values, negative values, expressions, scientific notation and NoData collisions are rejected instead of rounded. Valid weighting is checked cell-by-cell using UInt64 reference arithmetic against visibility × AADT.
- DEM must be a standalone single-band GeoTIFF with projected metre coordinates, north-up unrotated grid, unscaled real elevations and no invalid/NoData/masked/nonfinite cells. Reported units must be metres or blank with the explicit user attestation. External sidecar dependencies are rejected. **A state-clipped DEM with NoData outside the boundary will be rejected.** Supplying a supported finite DEM requires a scientifically justified preprocessing decision; this runner does not fill or crop it automatically.
- Each output must reopen, have the expected dimensions, CRS, exact geotransform and type, and have valid cells. Viewshed pixels must be 0/1; conversions must preserve pixels; weighted pixels must equal exact multiplication. Compressed stages must report DEFLATE. The validator does not independently reimplement the viewshed algorithm or establish scientific truth.

The real GDAL smoke test exposed that the installed calculator's default UInt32 NoData marker is `4294967293`, not the maximum UInt32 value. The repair explicitly pins UInt32 and that marker, preserving the observed successful-case semantics on the supported domain. The maximum admitted AADT stays below it. This is an intentional restriction, not a silent change in integer arithmetic. See [GDAL viewshed documentation](https://gdal.org/en/stable/programs/gdal_viewshed.html) for the input-NoData limitation and [calculator documentation](https://gdal.org/en/stable/programs/gdal_calc.html) for type/NoData behavior.

## Failure isolation, receipts and restart

Every admitted CSV row receives a deterministic `job-<zero-based-ordinal>` storage ID (at least eight decimal digits) and uses a fresh `job-<ordinal>/attempt-<random-id>/` directory. These lowercase ASCII names are injective within the byte-bound CSV, including under case folding, and independent of the raw label. Subprocess arguments are passed as a list with `shell=False`; the calculator expression is formed only from an admitted integer. No stage may start with an existing destination. Command, stdout, stderr and exit-code files are written; a zero exit still requires raster validation. A successful validation gets its own hash receipt. A failed stage prevents later stages and records an error.

**All intermediates are retained. There is no cleanup feature.** This intentionally trades disk space for evidence and avoids deleting the only correct raster after failed compression. Space budgeting is the user's responsibility before large runs. This package's tests never execute the untouched original, and no statewide run has been performed.

Only after all four stages validate does `success.json` bind the exact admitted job (including all original CSV field strings, parsed coordinates/AADT and storage ID), attempt and all four output hashes. Resume compares both this job binding and saved `job.json` to the currently admitted row before checking output hashes or accepting a skip. Consumers should read this receipt and use `visibility.tif` / `traffic.tif` from that attempt. Do not glob all attempts into a cumulative raster. Counts in `summary.json` are for the latest invocation that passed run-identity admission and acquired the cooperative lock: attempted, succeeded, failed, skipped. Each invocation also has its own `invocation-<id>.json` record, with status `running`, `completed`, `completed_with_failures`, `refused` or `interrupted`. A controlled resume refusal writes current counters and an error before raising. Before replacing the latest summary, its exact previous bytes are archived under the new invocation ID; older invocation records remain. Pre-admission failures (including identity mismatch or an existing lock) report to stderr and do not modify a run that they were not admitted to. Abrupt kill or storage failure can leave a running/stale record; individual receipts and attempt directories remain the acceptance evidence.

To resume a completed or partially completed run, repeat the same arguments with `--resume`. CSV bytes, DEM bytes, explicit CRS/curvature, runner source, GDAL bindings version, tool paths and entrypoint hashes must match. Completed outputs are hash-checked and final raster semantics revalidated before being skipped. Changed/corrupt completed results cause refusal, never overwrite. Ordinary input immutability during execution is required; the runner also hashes inputs before/after each attempted job.

An existing unsuccessful/incomplete attempt is **not retried automatically**. Inspect it, confirm no prior process is still writing, and use `--resume --retry-failed` to create a new attempt while retaining the old one. Changing inputs/configuration requires a different run directory. This is intentional even for harmless CSV reordering or runner upgrades.

A cooperative `LOCK/` directory excludes simultaneous invocations. Normal unwinding removes it. A hard kill may leave it behind: establish that the prior runner and its child commands have stopped before manually removing ONLY that empty `LOCK/` directory. Never remove it merely because a timeout elapsed. There is no daemon, auto-recovery or hostile-host security claim. JSON files use fsynced temporary writes and replace; filesystem/directory durability after power loss and exactly-once execution are not promised. A leftover `.tmp` is evidence of interruption; preserve the old run and use a new directory if receipt recovery is uncertain.

## Verification and limits

The tests exercise real GDAL success, every command's nonzero failure, zero-exit missing/corrupt output, wrong weighting, stale attempts, interrupted attempts, changed completed outputs, identity mismatch, CSV/CRS/NoData/type/grid admission and zero/upper-bound traffic values. Test process failures use a fixed isolated mock command, not CSV shell interpolation. `TEST-RECEIPT-02.txt` records the successor execution; `MANIFEST-02.json` binds source hashes and environment. The original receipt and manifest are retained for the first candidate. `SOURCE-REVIEW.md` records the local source review and outstanding independent review.

The first test run failed because of the NoData-marker validation assumption; that was inspected and corrected before the final run. Prior raw logs are preserved in the workspace; this report does not claim the initial draft passed. The bounded tests do not prove zero bugs, arbitrary-version compatibility, original execution equivalence outside the admitted domain, historical map correction, or empirical reproduction. Disk exhaustion, process termination and external edits can interrupt a run; absence of a success receipt means the attempt is unaccepted. Full scientific validation and source-to-paper provenance remain separate.

Actual OS coverage: Linux case-sensitive filesystem with real GDAL. The case-insensitive regression additionally models filename lookup by `casefold()`; no Windows or macOS filesystem execution is claimed. Existing first-candidate run directories cannot be resumed by this successor because runner-source identity changes; preserve them and choose a new run directory.
