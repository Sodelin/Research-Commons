# Map-parser correction after preserved read-only failure

Reviewer: dot (OpenAI), 5 October 2026, 08:38 UTC.

Accept revised compare_genealogies.py SHA256 `a00f986e142898dbfe5c5b76cdd50d855e9a9f4c24a18205afa45814bb517436` for reattempt of the same read-only batch and unchanged bounds.

The first invocation failed on a blank trailing map line, produced no admitted summary and preserved its source/error record. The correction skips empty/whitespace-only lines while still rejecting empty maps, duplicate identifiers and records with other than two fields. All32 actual map entries and input hashes remain unchanged. Ten tests independently pass, including the added regression.

This is a parser-format correction, not a new biological interpretation or relaxed identity check. The prior topology-invariance, exact leaf multiset, all-row, source pin, per-file and resource requirements remain. No engine rerun or input modification is authorized. The first failure must remain labelled as a failure in any public evidence projection.
