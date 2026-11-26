# Discovery scale and reliability, observed at 04dd5e0

Pinned source commit: `1899191ddd26386441dc7d780352dcec81fd3002`. Pinned generated commit: `04dd5e0fdc5003f359a88ce6f427443f0445d5a1`. The public generated commit is one descendant of that source. Its only changes are five receipts and six shards. The indexed conservator compares actual Git trees, not the event's change list.

## What it actually reaches

- Across four declared Commons roots: 105,491 Git entries, 66,015 indexed rows
  (57,951 Lean paths, 7,155 notes and 909 receipt locators), 39,476 explicitly
  out by extension/basename. In this run 66,009 rows were reused and only six
  source bodies read. Other paths and repositories are outside these counts.
- The hosted check battery reports passed catalog/check coverage and two local
  query fixtures, with Lean and SMT not run. The source records are index
  pointers, not proof attestations.
- Public external metadata observation: a four-file approved path list for
  immutable `leanprover/lean4@819816b2...`, corroborated Git tree and directory
  object IDs, no external source bodies and no proof run. Static source-only
  fallback and observed metadata are separate views; neither is a full Lean
  or Mathlib catalog. By code inspection the adapter bounds to two approved
  providers, up to sixteen paths per provider, up to 24 unique Git tree reads
  and sixteen Contents-directory reads per provider, and 2,000,000 bytes/response.
  Enforce a smaller total budget and honor rate-limit headers before expanding
  to more than this four-file sample. At the loaded pin the four files span
  five tree nodes and three parent directories, thus nine requests per
  uncached refresh (commit + trees + directories), excluding any overhead.

## Bounded readback and algorithm benchmark

Two actual connector requests read the exact indexed paths. Shard 74 was
133,505 decoded UTF-8 bytes in 363ms and shard 8b was 142,911 bytes in 393ms.
Both row counts matched (257 and 270) and both exact file-blob/hint pairs
were present. These are **content bytes and connector elapsed times**, not TLS
wire totals, origin timing or a repeated latency study. The manifest itself
was 38,289 characters and 344ms; coverage/provider/check/smoke sidecars were
608/1,710/2,676/1,000 characters. None of the 256 shards was blanket-fetched.

The local synthetic `bench.py` test holds 66,015 rows in 256 shards, without
live sources. It compares full JSONL scans, one path bucket, and a single-hint
postings build/reuse. See `benchmark.json` for wall-time medians. It is an
algorithm comparison, not a prediction of deployed latency or paid minutes.

## Largest sensible implementation

Use the Git object database for wholesale inventory (local `ls-tree`/batched
`cat-file`), content-addressed cache for source-body/deserialization work,
and a compact postings index for repeated name/title queries. Exact known-path
lookup needs one SHA-prefix bucket; path sharding alone does not make arbitrary
text searches cheap. Keep full-file source reads on user-driven pin lookup or
explicit import, separate from running the code. New external repos require
a repository/commit/tree/path allowlist, distinct provenance and controlled
status. No dependency should be installed because its names appeared in
metadata.

Prefer authoritative immutable pins and metadata readback. For mutable
discovery requests, use standard conditional requests and obey Retry-After
and quota headers; compare the approved commit before approaching any body.
Keep one last-good pinned external receipt separate from `refresh_unavailable`,
otherwise a provider outage both erases observation and retries on each push.
Retain the already existing daily recovery and manual dispatch in the same
workflow; no extra scheduler. Push and daily runs can first compare scoped
tree and meaningful check inputs, bail on a no-op, then compile only locked
consumer closures when installed/approved. An unrelated ref move or a queued
run is not a published update; read back actual outputs at an exact ref.

Current `publish_equivalent.py` compares output hashes only for Lean/SMT;
an altered but passing catalog contract could be considered equivalent when
the metadata index is unchanged, leaving the old receipt. Fingerprint the
semantic catalog result and approved proof-job inputs, not timestamps or
check wall-time. Keep absent/skipped/timed-out and kernel-checked distinct.

## Official bounds

- [GitHub Trees API](https://docs.github.com/en/rest/git/trees): recursive tree
  responses cap at 100,000 entries and 7 MB; respect `truncated`. The current
  declared Commons scope alone already contains 105,491 tree entries. Prefer
  local authoritative Git enumeration for the owned corpus; for providers,
  descend only necessary pinned subtrees rather than scraping around the cap.
- [REST quotas](https://docs.github.com/en/rest/using-the-rest-api/rate-limits-for-the-rest-api):
  unauthenticated primary quota is 60 requests/hour; secondary limits also
  apply. The broad contractual upper bound of 41 calls/provider could exceed
  60 across two cold providers. Keep a per-run shared request/decode/time budget
  before expanding and stop on quota pressure. This is separate from local Git.
- [Actions billing](https://docs.github.com/en/actions/concepts/billing-and-usage):
  standard hosted runners for public repositories are free; this is not a
  guarantee of immediate runner availability, nor permission for volume abuse.
  [Workflow troubleshooting](https://docs.github.com/en/actions/how-tos/troubleshoot-workflows)
  documents schedule delays and possible drops. Publication readback is still
  required before asserting current state.
