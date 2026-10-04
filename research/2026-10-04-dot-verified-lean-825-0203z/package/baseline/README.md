# Unified Lean/Lake package: source-complete 336-successor

Attribution: dot, consolidating preserved attributed research proofs. Accepted source bytes and original authorship are preserved.

This package contains the exact frozen source/configuration set for the **336-module selected closure**, its portable rebuild route, allowlisted certificate summaries, and a record-level historical-coverage ledger. Snapshot time: **2026-10-02 21:56:48 UTC**. Evidence and scope addendum: **2026-10-02 22:13 UTC**. The complete local history archive and machine-specific raw evidence tables are not included.

## Verified checks

- Guarded `lake --no-cache build UnifiedLean`: **PASS**, exit 0 in 53.806 seconds; Lean 4.33.1 (`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`), mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.
- 336 selected modules plus aggregate; 340 stable source/configuration hashes, 337 owned compiled-object hashes, and 1,640 selected/replayed standard-axiom audits. No nonstandard axiom rows.
- All-declaration audit: **PASS**, 12,052 owned declarations, including 8,775 theorem declarations; zero owned axiom declarations, zero nonstandard-axiom rows, and zero missing modules.
- Compiled dependency export: **PASS**, 60,197 owned proof-body edges, 41,133 type edges, 266 direct-head delegation candidates. These are syntax-level dependency candidates, not equivalence or human-acceptance evidence.
- Transitive import audit: 3,920 imported-module entries, 18,256 artifact hashes, zero missing artifacts.

The three new exact-source components cover the original-ID fixed-control compiler and controlled all-panel unranked transport, plus fresh two-distinct-original-tip pair root-age observation. Their exact component scope and limits are in `SCOPE-SUCCESSOR.md`. All 333 protected baseline source/config bytes remain unchanged except the aggregate, which appends three imports.

## Rebuild

Use Lean 4.33.1 and mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474` with a built mathlib cache. This package uses the pinned relative `deps/mathlib` layout; do not run `lake update` when reproducing this snapshot.

```sh
export UNIFIED_LEAN_BIN=/path/to/lean-4.33.1/bin
export UNIFIED_MATHLIB_CACHE=/path/to/pinned-built-mathlib
python3 scripts/bootstrap_cache.py
bash build.sh 600
```

For fresh post-build certificates, use `scripts/freeze_snapshot.py`, then the declaration and dependency scripts against that named local snapshot. The verified results above are recorded in the allowlisted receipt summaries; this packaging step does not claim a new full build.

## Coverage is still incomplete

`catalog/COVERAGE-LEDGER.json` lists all 490 retained historical source-record paths/hashes and the 77 inherited program records. Of 490 source records, 327 byte-match the selected closure, 148 remain outside it, and 15 are failed/resource-excluded. The profile replay status for 86 proof-bearing candidates is recorded separately: 85 exact originals pass; original `GraphQuartetPortCounts` failed and is not admitted. A small compatibility repair is separately checked and reviewed but is not substituted into the original-source result or this 336 closure. Five Theta certificates remain resource-blocked, with dependent sources excluded.

This is source-complete for its selected 336 modules, not the full historical Lean package or all project goals. No full-project correctness, headline equivalence, novelty, full historical closure, maximal timed-source equality, or complete fair-Q formal assembly is claimed. See `SCOPE-SUCCESSOR.md` and `catalog/HISTORICAL-REPLAY-STATUS.json` for the exact bounds.
