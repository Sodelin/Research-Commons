# Research Commons discovery reader

A question-first product over the existing canonical claim register. Search by question, topic, disposition or origin; follow exact source and typed connections; copy a source-pinned agent reuse record. Completed hand mathematics stays completed when formalization is missing.

Canonical data/attribution: Sodelin/Research-Commons docs/claims.json, maintained by Dot and scientific owners. This reader preserves that source and adds navigation, search and exact owner-supplied evidence joins. It does not generate scientific answers or certify novelty.

## Run and verify

- `npm ci --ignore-scripts --no-audit --no-fund --logs-max=0` installs the locked DOM-test dependency; production has no package installation/build step.
- `node tools/check.mjs` checks the model and actual DOM journeys.
- `node tools/query.mjs --query 'independent routing' --status established` uses the SAME engine for agent lookup. Add `--refresh` for current canonical source in memory.
- `python tools/refresh.py` refreshes the deliberately public source snapshot and exact provenance.
- `python -m http.server 8766 --directory dist` serves a local preview. Stop only this owned foreground process after use.

The static dist folder is the deployable artifact. MiniSearch is locally bundled and integrity/licence pinned; jsdom is test-only. Deployment follows the registered Sites ID in .openai/hosting.json. Never recreate that Site to repair a deployment. Source pushes and exact saved-version/deployment receipts are separate. For rollback, redeploy a previously saved good version and its recorded source; do not alter canonical scientific records.

See ARCHITECTURE.md for tool comparisons, ownership, security boundaries and update/coverage limits. Source and test evidence do not establish full visual browser/device acceptance. Canonical coverage is currently84 selected cards, not the entire historical research corpus.

Citation lookup considers both the canonical origin field and explicitly tagged prior-work references. The same bibliography adapter feeds the reader, weighted search and agent reuse export. Source refresh validates through the shared model in RAM before writing a snapshot. `node tools/check.mjs` uses explicit suite paths and refuses an empty suite rather than accepting a zero-test glob.

## Search evidence bodies

The same reader now offers an explicit **Load evidence search** action. It loads the public source corpus only when requested; ordinary card lookup does not download it. Search terms and existing topic/status/origin filters then apply to both layers. Evidence results retain immutable source links, canonical claim bindings, evidence roles, content hashes and bounded text excerpts. Loading a newer claim register does not silently relabel the pinned evidence snapshot.

```sh
node tools/query.mjs --sources --query 'calibrated decoder'
node tools/query.mjs --sources --query 'certificate' --status open
node tools/refresh-sources.mjs
```

`--sources` returns source evidence, not claim acceptance. It shares the browser engine and includes both corpus and current-register provenance. `--refresh` updates the claim/filter view in RAM; it does not pretend to refresh bundled evidence. The explicit corpus refresh reads only immutable, publicly accessible first-party Markdown references already in canonical accepted_artifacts. It has four bounded concurrent requests, 20-second request timeouts, a 512 KiB per-document bound and a 16 MiB corpus ceiling; redirects are refused. Bodies stay in RAM until the bounded public-source snapshot is assembled. Failures are listed as unavailable, never silently treated as empty documents. The previous snapshot survives a global-bound failure. Generated corpus source is versioned alongside its builder and exact SHA256/Git-blob identities. No publisher papers, private Subspace cache or private Atlas corpus are mirrored.

Current body coverage includes 145 canonical Markdown artifact references, all58 public G3 recovery notes and the catalogue correction README. The exact generated snapshot and its coverage fields are in dist/source-corpus.json; unavailable sources are explicit. This excludes unlinked archive material and is not whole-archive coverage. Source retrieval never grants job execution authority or converts a source hit into accepted mathematics.

## Wider archive and combinable views

Load **wider archive search** in the same reader to search5,829 public Markdown paths, including unmapped historical work. This snapshot inspects7,794 exact Git trees/105,112 entries from selected public roots, excludes32 dependency/generated/self subtrees explicitly, and preserves immutable URL/Git blob identity. It is filename/path search, not full-text search of those bodies, all Git history, private task coverage or acceptance. The [GitHub archive guide](../../ARCHIVE-SOURCES.md) groups these paths without requiring commit-history reconstruction. Refresh with `python tools/refresh-archive.py`; GitHub GraphQL batches up to25 exact tree objects per request and refuses missing/errored responses and global bounds before replacing the old source inventory.

```sh
node tools/query.mjs --archive --query 'calendar metric' --limit 10
node tools/query.mjs --kind theorem --review accepted_scoped_hand_review --sort subjective_reuse
```

Browser and agent views combine programme, claim kind, mathematical disposition, origin, literal review/authorship state, formal status and historical-novelty source statement. **Dot's subjective reuse order** consumes the existing dated75-card overlay with its reasons/source scope; nine recovered sequence groups have no rank in that snapshot. No importance score is invented, and unassessed novelty/unranked reuse never means low importance, incomplete proof or failed review. Claims may be filtered on all these axes simultaneously. Archive paths use query words only, because unmapped source paths have no inferred claim/review disposition. Catalogue-only body sources are shown with claim facets clear; master-claim statuses are never transferred to those components.

The G3 importer now consumes the canonical top-level recovered_source_catalogues entry using its existing published RESULT-CATALOGUE/SOURCE-MANIFEST contract. It verifies each selected public note's byte count, SHA256 and Git blob before inclusion, excludes17 unelaborated Lean sources, and preserves16 catalogue keys, literal scopes, proof authorship, independent review, formal state, gaps and rejected-intermediate warnings. It includes the current source-recovery README for later corrections. Component bodies are not bound as proofs of unresolved CB-G3-004.

CLI results are bounded to25 by default; use --limit 1..100 and --offset with returned total/next_offset for reproducible pagination. --archive refuses claim facets/current-register refresh; --sources refuses transferred subjective claim sorting. No background service or model call is involved. The public reader source is versioned independently of the canonical registry, without modifying scientific IDs/statuses.
