# Measured GitHub Lean metadata intake at selected-prefix scale

## Result

At the exact official [Lean 4 v4.33.1 commit](https://api.github.com/repos/leanprover/lean4/git/commits/819816b2e0a3bf405af45ae5c7af2491d8f5bee6), the approved paths are all regular Git blobs ending in .lean under `src/Init/` and `src/Std/`. This is not an inventory of all Lean 4. Neither source content nor a checkout is needed. No theorem count, provenance beyond the Git metadata, Lean replay, or proof status is inferred.

| Measurement | Observed |
| --- | ---: |
| Selected paths | 1,112 (630 Init + 482 Std; 278× the previous sample of 4) |
| Git tree entries examined (ancestor listings included) | 1,358 |
| Git tree object IDs recomputed | 193 |
| Actual connector requests | 4 bounded GitHub Git Tree GETs |
| Total connector batch wall | 524 ms |
| UTF-8 GitHub JSON body bytes, excluding connector wrappers and transport framing | 316,423 |
| Projected metadata capture retained | 160,103 bytes |
| Index retained | 109,143 bytes in 16 shards |
| Index receipt retained | 2,388 bytes |
| Parse, rehash, sort, and shard build, excluding disk writes | median 16.896 ms (25 warm-process trials, min 16.154, max 25.095) |
| Selected rows per median second locally | ~65,815 |

Root and src used complete nonrecursive listings; Init and Std used separate recursive listings. All four responses said untruncated. Per-call times were 410, 364, 514, and 464 ms in the same batch, so they do not add to wall time. This is a point observation on the available connector, not a sustained transfer/rate quota claim. The local benchmark includes reading the small capture and building the index in memory; it excludes the no-clone acquisition and final file writes.

## Verification and scaling design

1. An operator-approved policy pins repository, commit, trusted root Git tree ID, selected path prefixes, and budget. Ref-to-root resolution is part of trusted capture provenance; this adapter independently recomputes each Git tree SHA, not the commit object's SHA. It walks exact ancestor links and reconstitutes every directory from each recursive listing. Missing entries, omitted child trees, a truncated endpoint, and conflicting bytes fail closed.
2. The collector issues a small bounded concurrent batch (four here). When a recursive listing is too large or truncated, discard it as coverage evidence, split the approved prefix on nonrecursive directory boundaries, rehang the child branches, and retry within a total call/entry/byte budget. If the budget, access, or retry ceiling is hit, report the prefix as incomplete, not a complete smaller result. Honor upstream throttling delay when exposed; do not treat this benchmark as a quota. The current demo implements verification and fails closed, not an automatic live collector.
3. Reuse checked immutable captures keyed by approved repo and tree ID. Source membership stays revision-specific. A changed revision reads the comparable approved ancestor/branch tree IDs and reindexes only changed branches; cache exclusions/tombstones under snapshot membership rather than silently dropping old proofs. No branch names or arbitrary discovered repositories become approved.
4. Find paths first, then do declaration/content discovery only on demand as a separate policy tier. The index speaks baseline `{path,sha}`. Shards use the high bits of SHA-256(path); the receipt binds the scope, commit, complete response coverage, row count and individual shard hashes. The global row digest uses lexicographically sorted paths (not shard concatenation). Higher bit counts can reduce per-shard read cost for larger banks. Row IDs are scoped by repository, commit, and canonical path. No theorem or source SHA-256 is inferred from Git blob ID.
5. Suggested scaling limits: start at four in-flight requests per collector and use explicit entry, retained-byte, output-row and request budgets. Source-only discovery cannot schedule retrieval, clone, or execute projects described by the resulting index.

## Replay

```sh
cd pb-scale-providers
python scale_catalog.py --benchmark 25
python scale_catalog.py --out another-empty-output-directory
PYTHONDONTWRITEBYTECODE=1 python -m unittest -v
```

The supplied `generated/` is immutable replay evidence; the CLI refuses to overwrite an existing output directory. `scope.json` is the approved policy sample, `capture.json` is the directory-metadata capture, `acquisition.json` is the measured connector batch, and `benchmark.json` is the measured offline run. There were no source-execution or publication steps.
