# Exact Discovery token fanout prototype (offline)

```bash
python fanout.py build-index /path/to/generated-source-index local.sqlite
python fanout.py query local.sqlite 'TriangleRun' --expect-commit <full-sha> --limit 20
python fanout.py build-tree /path/to/repo <full-sha> local-paths.sqlite
PYTHONDONTWRITEBYTECODE=1 python -m unittest -v
PYTHONDONTWRITEBYTECODE=1 python benchmark.py
```

Use `build-index` for the complete manifest-declared generated v2 source
metadata layer. It checks ordered shard digests, row counts, source commit,
aggregate bytes, shard placement, duplicate paths and evidence state. Run
the independent tree-coverage gate before building from a hosted index.
`build-tree` is a separate path-only mode: it inventories actual pinned
Git paths/blob IDs/modes and does not read source bodies or invent title or
declaration metadata. Neither path verifies Lean or indexes unregistered
provider catalogs. Use `--expect-commit` and `--expect-digest` to refuse
stale caches. SQLite output is local/rebuildable, not a second source of truth.

## Exact coverage claim

The cache matches the current Discovery source-layer ASCII/CamelCase
token semantics, including tokens in JSON keys and hashes. It is **not**
substring, phrase, semantic or Unicode-word indexing. Nonempty queries of
at most 64 distinct exact tokens use AND. It inserts one posting for
each (token,row) pair after applying precisely the scan's tokenizer to
that row's serialized JSON. The query visits the rarest token's full
posting list and returns candidates having each of the other tokens,
in original row order. Therefore no eligible row is dropped in an
intact cache built from the same records; any row missing a query token
is excluded. Result display limit does not cap the exact match count.

No claim is made about missing files outside the loaded layer, publication
lag, unrecorded body text, absent/incorrect declaration hints, transliteration,
or externally modified cache files. Local commit digest pinning does not
prove data availability or toolchain verification.

## Measured local run

Distinguish two test sets:
- The existing generated v2 fixture was validated and compared against
  the current scan implementation, including title and declaration hints.
- The scale run is real **path metadata only** from pinned Git commit
  `45d7d79bcadb456174914ca80329d32c2158d727`: 65,887 rows, 1,581,509
  postings and 55,812,096 SQLite bytes. Loading metadata took 375 ms
  and building the cache 3.251 s. Measured warm medians materialize all
  match IDs, not the final displayed rows. Selective/absent cases took
  .009–.190 ms versus ~772–819 ms for the current retokenizing scan;
  broad cases 11.86–35.51 ms. The broad all-row query `source commit`
  took longer than a pre-tokenized scan (35.51 vs 27.15 ms).
  All ten benchmark query result IDs matched the scan exactly.

For production, keep one cache keyed by index digest + tokenizer version,
consider exact count plus limited ordered result SQL for common-token
traffic, and measure before indexing full bodies or recruiting live providers.
