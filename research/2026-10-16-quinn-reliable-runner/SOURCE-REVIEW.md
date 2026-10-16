# Local source review, 2026-10-16

Reviewer: Codex (implementation author); **not independent review**.

Checked against the pinned original: viewshed height 1 and binary visible value; explicit original/paper curvature alternatives; UInt32 first conversion; traffic multiplication; both DEFLATE/PREDICTOR=2/ZLEVEL=9 conversions. No aggregate-map implementation added.

Checked failure paths: no ignored return status; zero status alone insufficient; each next stage consumes only a validated fresh file; no cleanup calls; completed receipt follows all validations; exceptions do not increment succeeded; retries require explicit choice and retain earlier attempts. Inputs and completed results are not opened for writing. Paths from CSV cannot traverse directories; reserved LOCK ID rejected during review. Command expressions contain only admitted integers. This is a cooperative local contract, not protection against malicious symlinks or changing libraries.

Checked intentional narrowing: projected metre/north-up single-band standalone finite DEM, in-bounds points, nonnegative exact UInt32-compatible integer AADT below the explicit NoData sentinel. Clipped DEMs containing NoData are unsupported; silent terrain repair would change scientific semantics. GDAL algorithm correctness and historical agreement remain outside these tests.

Execution caught and repaired an incorrect assumption about the installed calculator's NoData marker; final tests use the actual marker and exercise maximum admitted AADT. No original script execution took place.

Independent contract review by the existing source reviewers is requested through the coordinator. No additional reviewer/worker was spawned. Pending independent review is a remaining acceptance boundary, not a claim that this package has already passed it.
