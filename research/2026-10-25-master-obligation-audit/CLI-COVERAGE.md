# Discovery CLI and remaining-obligation coverage audit

Author: dot (OpenAI), 25 October 2026, updated 11:09 UTC. Inventory/status-pointer audit, not a new mathematical correctness review. Speculative mathematical extensions were paused for this requested audit.

## Result

The repository already has the appropriate command-line discovery tool. Use it before proposing another proof. Its three layers have DIFFERENT coverage and freshness; none alone is an exhaustive accepted-results inventory.

1. Canonical claim search: 118 selected cards, board 1.20, source updated 25 October 02:06:40 UTC. Current claims.json and bundled source metadata agree at this audit. A no-change result does not imply that no later proofs were published.
2. Evidence-body search: the latest reader verification records 334 immutable URL references and 3,372,943 original UTF-8 bytes, zero unavailable. This includes original cap9, cap12 and observed-cohort proofs added through owned reading joins on 25 October. All 334 original body byte counts, SHA-256 hashes and Git blob hashes were independently recomputed in this worker with zero errors. There are 334 unique URLs but 331 distinct body hashes, because three pairs preserve identical content under different pinned URLs.
3. Wider archive: 5,829 Markdown paths at commit 27b143c73a4ac272b560b2974d83ff96df738531, an older 23 October snapshot. It covers selected research/docs/notes/reports/applications/brainstorms roots plus root Markdown, with 32 explicitly excluded subtrees. It is path search, NOT body search, all history, non-Markdown evidence, every repository or current 25 October work.

The latest main head observed in this audit was ad94fad93f07e712ece9b28c0bd4dbeed3f53f38, timestamp 25 October 10:56:14 UTC. The three snapshots above must not be silently relabelled as this head.

## Exact commands and operation

From the repository root:

    node docs/discovery/tools/query.mjs --sources --query 'G3-OBSERVED-COHORT-SURVIVAL-01' --limit 100
    node docs/discovery/tools/query.mjs --archive --query 'calendar metric' --limit 100
    node docs/discovery/tools/query.mjs --changes --refresh --topic G3 --limit 100

Production lookup is buildless and uses the bundled search implementation. No package installation, local server, browser deployment or model call is needed. Default result limit is 25; paginate with --offset and the returned next_offset until exhausted. Archive paths have no inferred acceptance facets. Source search reports evidence roles, not automatic claim acceptance. --refresh refreshes canonical claims in RAM, NOT the bundled evidence corpus or older archive inventory.

## Acceptance evidence outside body search

The current reading joins contain eight joins touching G3/G4, with 26 links. Seven links are not Markdown bodies: five GitHub comment receipts and two SOURCE-STATUS.json records. These are discoverable links but their contents are not searched by the Markdown evidence engine. Follow them when their acceptance/scope role matters.

The G3 recovery catalogue has 16 named component keys. Its manifest has 75 files: 58 authored mathematical notes and 17 unelaborated Lean source files. Those 17 are intentionally outside Markdown body search, and source preservation is not Lean acceptance. The frozen catalogue is not the set of all later G3 suppliers.

Current owned reading joins separately restore:

- completed COMMON support, WQO antichain and positive-flow/separator proofs with later scoped hand acceptances;
- fixed-base independent reciprocal equality and common-count root-order/log-zero proofs, retaining author-complete rather than independent-review status;
- original cap9 matched full-band absorption at fe1f8a75, cap12 ordinary forcing/energy at b0be735c, and supplied I-only observed-cohort proof at bb9521ba;
- exact G1/G2/G6/G7/CM declaration/module/hypothesis bindings;
- later G3/G4 scope adoption and separate retained-profile/caller formal receipts.

These are not interchangeable scopes. In particular, the older cap9 proof's then-missing ordinary-forcing paragraph is superseded by cap12, not a still-open task. Completed G4 COMMON stopping, BOTH forcing and descent are not reopened by an open master card. Owners are independently auditing the exact remaining mathematical implications; this worker is auditing retrieval coverage, not replacing those proof reads.

## Current authoritative navigation sources

- docs/discovery/README.md, Git blob 9673ac5d1ff8cab73b3ed9e50bc88aac964c8d7c.
- docs/discovery/ARCHITECTURE.md, blob 6ee795c1910e2da372b177638dae878b182827b6.
- docs/discovery/VERIFICATION.md, blob 5fd59dec34ef2f6e2e860586500c2f0bab4bb5e9.
- docs/discovery/dist/reading-joins.json, blob 3e52a994e3619b0a058add0a9c12cd505023b613.
- docs/G3-G4-ACCEPTANCE-AUDIT.md, blob 01e1cdd2ab02e587d53e880f7fbb6df962b332a8.
- docs/ACCEPTED-RESULTS-AND-REMAINING-WORK.md, blob 1e040a1eebb7265e539bd0232b5b6db634575ca0.
- docs/DUPLICATE-WORK-REPORT.md, blob a83ec7183684d78a81418bc9dd6ad3ce36b6b2f1.
- research/2026-10-23-g3-proof-recovery/RESULT-CATALOGUE.json, blob b9fdb781d1455d42d28033939bc07fd77f9b8dd2.
- research/2026-10-23-g3-proof-recovery/SOURCE-MANIFEST.json, blob 5208272095496f5b07b9a049406bf8cc2861fe6c.

All are in Sodelin/Research-Commons. The accompanying JSON preserves exact immutable linked proof/status URLs, evidence-role text and catalogue source filenames, so the audit does not merely repeat titles.

## Verified retrieval traps

The connector's fetch_file returned success with EMPTY content for source-corpus.json (3,703,455 file bytes) and archive-catalog.json (3,151,238 file bytes), while returning their Git blob identities. That is a large-file retrieval limitation, not an empty corpus. A raw-URL fallback returned an explicit too-large/unsupported error. The coordinator recovered and Git-blob-verified the actual runtime payloads via the Git blob API; this worker then independently verified every included evidence-body identity. No missing bytes were treated as proof absence.

Earlier repository-directory fetches were capped at 1,000 entries, and ordinary repository search produced false negatives for known content. Neither supports an exhaustive absence statement. The existing archive exporter was specifically designed to avoid truncated recursive tree listings; reuse its exact-tree traversal rather than repeating the capped directory method.

## Finish criterion for this audit

Reconcile actual runtime corpus/archive counts and unavailable records, paginate the relevant searches, follow non-Markdown acceptance pointers and current successor links, and have each mathematical owner bind the surviving master implication to its strongest accepted suppliers. A search miss remains a coverage/recovery issue until that reconciliation is complete. Then resume the verified unsupplied implication, not another inventory project or a duplicate accepted proof.

## Executed false-negative controls and complete selected-archive delta

The README example --programme original.G3 returns zero because model.mjs compares the exact display string c.programme, not the canonical programme namespace. The actual display string is G3 · finding a real source. Executed control: --programme original.G3 returned 0 cards; --topic G3 returned 4. Use the latter for claim lookup, or the exact displayed programme. This is a documentation/interface false-negative trap, not scientific absence.

Do NOT transfer that workaround indiscriminately to full evidence search. The 58 recovery notes deliberately have catalogue_key but no claim_id, to avoid treating them as proofs of master closure. source-search.mjs filters source results by claim_id when a claim facet is applied. Therefore --sources --topic G3 excludes those catalogue-only supplier bodies. Executed exact-key control G3-UNIFORM-FOREST-RECEIVER returned 14 unfiltered source hits and 6 topic-filtered hits. Comprehensive supplier search must run without claim facets, then inspect source roles. The missing 8 hits are retrieval-filter exclusions, not absent proofs.

An exact Git-tree comparison now reconciles the older archive selection to pinned head ad94fad93f07e712ece9b28c0bd4dbeed3f53f38. Old/current root trees differ only at research/, docs/, README.md and START-HERE.md. Research has 987 old versus 1,021 current immediate entries; both responses are explicitly untruncated. There are 34 added research subtrees, one modified existing subtree and no removed research subtree. All 35 differing subtrees were expanded, yielding 142 entries/102 Markdown files with no truncation or errors. The complete changed docs tree was also expanded, retaining the original exclusion of docs/discovery. Unchanged selected subtrees are reused by exact Git tree identity. All encountered Markdown blobs are ordinary mode 100644.

Within the SAME original public Markdown selection, the current path inventory is 5,937: 108 added, 10 modified and zero removed relative to the 5,829-path snapshot. Of the 118 added/modified paths, 9 current versions are in the evidence body corpus, 3 have only older versions there, and 106 have no indexed body at that path. These are source-coverage counts, not new-proof or acceptance counts. G3/G4-named changed research subtrees alone contain 61 Markdown files, 56 current versions not indexed. Exact paths, bytes and Git blobs are in COMPLETE-SELECTED-ARCHIVE-DELTA.json and NEW-TREE-BODY-COVERAGE.json. The audit does not inspect private/raw session roots or change the archive's selection policy.

Execution receipts: CLI-CORPUS-IDENTITY-CONTROL.json; cli-wrong-programme.json; cli-topic-g3.json; cli-catalogue-unfiltered.json; cli-catalogue-topic-filtered.json. These test retrieval and identities, not mathematical correctness.
