# Publication preparation and exact-copy provenance

This review companion is intended for `research/2026-10-07-rust-count-pilot/review/` beside the separately prepared count-certificate pilot. Preparation does not indicate permission to publish or evidence of an upload.

The review report and both JSON evidence reports are byte-preserved copies of the completed local review artifacts. Their original SHA-256 identities are recorded in `REVIEW-MANIFEST.json`; the original review report is SHA-256 `93469333bb74c647ce6681aca78e548352db6a9d19d62b12bf8c44774c0d79b1`.

Two scripts are derived copies. In each, the one absolute machine-specific package-root directory was replaced with `pathlib.Path(__file__).resolve().parents[1]`. This resolves the enclosing pilot directory from the intended review subdirectory. No input cases, mathematics, assertions, expected identities, or test verdicts were changed. The original and derived script hashes and sizes are both recorded in the manifest. No other redactions were made.

The initial `independent-report.json` records the source snapshot before the author's CLI fix and additional tests. The later `binary-replay-report.json` records the final frozen source and binary and the actual independent Rust executions. These are different evidence stages, not competing claims about a single source snapshot.

The scripts are source code, not compiled executables. The package contains no binaries, credentials, toolchain files, raw machine logs, personal source data, or copied private notes. All test inputs are synthetic exact-number cases. Recorded binary hashes identify previously executed artifacts; executable bytes are not included.

For future reproduction, obtain/build the separately scoped pilot and run these scripts from the intended layout. The replay script checks the archived binary identity before testing; an independently rebuilt binary can differ, so a hash mismatch is a provenance gate rather than a mathematical failure. Both scripts write their report JSON next to themselves. Preserve the archived reports before rerunning, and label any newly generated evidence separately.

These copies were syntax-checked and scanned for absolute local paths during preparation. Neither derived script was rerun during publication preparation, and no new scientific result is claimed.
