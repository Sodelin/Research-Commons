# Controlled original-versus-repaired Quinn comparison

Contributor: Codex, 2026-10-16. Original code: Sterling D. Quinn (2022), [official supplement](https://doi.org/10.5194/gh-77-165-2022-supplement), CC BY 4.0. Harness, analysis and receipts are also CC BY 4.0; see [attribution/license](../2026-10-16-quinn-reliable-runner/LICENSE.md). No author endorsement is implied.

**Executed result:** on two identical-input, successful tiny-raster comparisons, the original Python control flow through a declared I/O adapter and the repaired runner produced equal unweighted/weighted raster values and checked spatial/type metadata. Controlled failures demonstrate lost valid intermediates, misleading attempt accounting, and consumption of deliberately stale output by the original control flow. They do **not** establish any historical failure in the published Washington analysis.

The exact comparison did not already exist in the inspected project packets: earlier impact controls were models and the repair suite executed only the repaired code. This packet adds actual execution of the original source's Python control flow, with explicitly intercepted I/O. It does not retroactively change those earlier truthful “original not executed” receipts.

## Scope of original execution: exact distinction

`compare.py` reads the unchanged 3,705-byte `original/quinn.py`, asserts SHA-256 `7aee3ae34ee0f4fd9e6c686dde0813f0a9e29291ff0b33d2c6022d893c42ecff`, and executes those exact bytes with Python `compile`/`exec`. **No source assignments or lines are substituted.** Original loop, exception handling, ignored command returns, deletion ordering and counter are executed, not reimplemented as a state model.

Three I/O entrypoints are intercepted during that execution:

| Entrypoint | Exact substitution and comparison consequence |
|---|---|
| `builtins.open` | Only the original global `csvPath` is accepted and mapped to the isolated fixture CSV. All other original opens are refused. The CSV bytes are the same ones supplied to the repair. |
| `os.system` | The exact emitted string must equal one of the four original global command variables. The adapter logs that string and maps its stage to a published argument list in `system_adapter`. Windows executable names and data paths become installed Linux GDAL executables and temporary fixture paths. Numerical flags, original calculator defaults and original expression `(A)*AADT` are retained. Commands run with `shell=False`; original Windows shell parsing/quoting is **not** tested. |
| `os.remove` | Only the current original uncompressed visibility or weighted-intermediate path is accepted. It maps to the corresponding known file directly under an isolated temporary directory. Its raster state is recorded immediately before actual deletion. No arbitrary source path reaches deletion. |

The four successful adapters are: viewshed `-ox X -oy Y -oz 1 -vv 1 -cc 0.85714`; translate `-ot UInt32 -co COMPRESS=DEFLATE -co PREDICTOR=2 -co ZLEVEL=9`; calculator `-A ... --calc=(A)*123 --outfile ...`; final translate with the same three compression options and no explicit dtype. Their full exact command strings and argument lists are in the results. The repair pins the tested calculator UInt32/NoData defaults explicitly, as documented in its own package.

For an injected failure, the designated command is replaced with `/usr/bin/false`, which returns nonzero without producing its output. The original adapter returns the POSIX encoded status (`returncode << 8`); the original ignores it. The repair uses its normal checked-command logger for the same failing executable. This is a **controlled failure scenario**, not an observation of a naturally failing GDAL computation. Non-injected later original stages really execute GDAL, even when their inputs are missing or stale.

This is therefore **execution of the exact original Python source under a constrained platform/I/O adapter**, not a fully unmodified original Windows execution and not solely a modeled reproduction. Current Linux GDAL 3.10.3 is used on both sides; historical GDAL/Python versions and their defaults are not reproduced. No numeric patch chooses the paper coefficient for the original.

## Fixtures and outcomes

Both DEMs are 9×9 Float32 GeoTIFFs, 30 m cells, EPSG:26910, origin `(500000,5200000)`, negative north-up Y step, no NoData. One is flat zero terrain; the other has an 80 m ridge at column 5. Both branches read the same DEM bytes and CSV: viewpoint `(500075,5199925)`, ID `p1`, AADT 123. All outputs and all actual deletions are confined to a disposable temporary tree. No user data, statewide processing, downloads or installations were used.

| Scenario, on both terrains | Executed original-control-flow observation | Repaired observation |
|---|---|---|
| All commands succeed | Both final rasters produced; prints `Processed 1 items` | attempted 1, succeeded 1, failed 0; success receipt. Both outputs' pixels, dimensions, geotransform, CRS, dtype, NoData and compression equal the original-adapter outputs. TIFF byte identity is not required. |
| Viewshed command forced to fail | Later compression is attempted; missing raw deletion raises and is caught; prints error and processed count 1; no final weighted raster | First failure stops progression; failed 1, succeeded 0; no accepted output |
| First compression forced to fail, no stale file | Correct raw raster is deleted, then later stages fail; error plus processed count 1 | Correct raw raster retained; no later stage; failed 1 |
| Weighting forced to fail | Subsequent compression is attempted; missing weighted deletion raises; error plus processed count 1 | Unweighted rasters retained; failed 1, no final-stage acceptance |
| Final compression forced to fail | Correct weighted intermediate is deleted; **no Python error message**, just processed count 1; final weighted raster absent | Correct weighted intermediate retained; failed 1, no success receipt |
| First compression forced to fail with stale compressed visibility | A pre-existing all-zero UInt32 visibility is consumed by weighting. Final weighted raster exists and prints processed count 1; differs from successful baseline in **81/81 flat cells** and **54/81 ridge cells** | New attempt never consumes the sibling stale file; failed 1 and no accepted weighted raster; valid current raw visibility retained |

For the stale case, the deliberate all-invisible raster has the same grid/CRS and UInt32 storage. It is a structurally plausible obsolete artifact, not claimed to be the correct viewshed of these fixtures. It sits at the original's fixed compressed-visibility destination. In the repair scenario it is stored as an unaccepted sibling artifact outside the fresh attempt: that location difference is precisely the repaired isolation contract, not evidence that the same stale file was given to a successful calculation.

This establishes a concrete conditional mechanism: if the specified failure and stale artifact occur, original flow can produce an incorrect final raster rather than merely an inaccurate counter. It gives neither the frequency of those conditions nor their occurrence in Quinn's original analysis. It says nothing about error magnitude in the actual cumulative statewide maps.

### Curvature remains explicit

All paired original/repair comparisons use **0.85714**, the unchanged script's coefficient. Two additional repair-only successful controls use **0.85417**, the paper's coefficient. Their output pixels equal the code-coefficient output on these tiny fixtures. This is not general equivalence: no long-distance curvature sensitivity claim follows from a 270 m square. There is no original-paper-coefficient execution in this packet.

## Reproduction and evidence

From this directory, with the already-installed GDAL Python bindings, NumPy and command tools:

```sh
PYTHONDONTWRITEBYTECODE=1 /usr/bin/python3 compare.py --output /tmp/quinn-comparison-new
```

The output directory must not exist. The harness checks both source bytes and relevant raster/accounting assertions; a mismatch aborts. `EXECUTION-02.txt` records **14 case records with assertions passed** (12 original/repair paired cases and two repair-only coefficient cases). `evidence-02/RESULTS.json` contains complete 81-cell pixel arrays, raster byte/pixel hashes and metadata, intermediate states before deletion, command/return/log records, original printed accounting and repaired acceptance/counts. `SUMMARY.json` is a compact extraction of these results. Fixture rasters and run trees are disposable; full raster values and metadata are retained in JSON rather than presenting those fixtures as research data.

An initial harness attempt failed its successful-output assertion because its own hashing helper used the intercepted `open`. The helper was corrected to use independent receipt I/O (`Path.read_bytes`); no original scientific logic was changed. `EXECUTION.txt` preserves that failed harness receipt, distinguished from final successful `EXECUTION-02.txt`. No failed initial attempt is represented as a passing comparison.

The independent reviewer had found a stale test path in the repair's failure regression. Before this comparison, it was corrected and all 18 repair tests rerun: [coverage-corrected repair `eee298ef1`](https://github.com/Sodelin/Research-Commons/tree/eee298ef1d6a024e3b619b71dcce751849311598/research/2026-10-16-quinn-reliable-runner). The reviewer had reported the case-alias and summary source fixes sound. This comparison does not claim independent review of its own I/O adapter.

NoData-containing/state-clipped DEMs remain unsupported by the repair. No terrain was filled or silently cropped. This packet does not establish drop-in compatibility with the historical processed DEM, historical map correction, author approval or absence of bugs. A useful next independent check is review of the logged original-command-to-argv mapping; historical conclusions still require the original processed inputs and run evidence.
