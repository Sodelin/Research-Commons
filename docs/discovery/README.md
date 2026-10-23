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

See ARCHITECTURE.md for tool comparisons, ownership, security boundaries and update/coverage limits. Source and test evidence do not establish full visual browser/device acceptance. Canonical coverage is currently75 selected cards, not the entire historical research corpus.

Citation lookup considers both the canonical origin field and explicitly tagged prior-work references. The same bibliography adapter feeds the reader, weighted search and agent reuse export. Source refresh validates through the shared model in RAM before writing a snapshot. `node tools/check.mjs` uses explicit suite paths and refuses an empty suite rather than accepting a zero-test glob.

## Search evidence bodies

The same reader now offers an explicit **Load evidence search** action. It loads the public source corpus only when requested; ordinary card lookup does not download it. Search terms and existing topic/status/origin filters then apply to both layers. Evidence results retain immutable source links, canonical claim bindings, evidence roles, content hashes and bounded text excerpts. Loading a newer claim register does not silently relabel the pinned evidence snapshot.

```sh
node tools/query.mjs --sources --query 'calibrated decoder'
node tools/query.mjs --sources --query 'certificate' --status open
node tools/refresh-sources.mjs
```

`--sources` returns source evidence, not claim acceptance. It shares the browser engine and includes both corpus and current-register provenance. `--refresh` updates the claim/filter view in RAM; it does not pretend to refresh bundled evidence. The explicit corpus refresh reads only immutable, publicly accessible first-party Markdown references already in canonical accepted_artifacts. It has four bounded concurrent requests, 20-second request timeouts, a 512 KiB per-document bound and a 16 MiB corpus ceiling; redirects are refused. Bodies stay in RAM until the bounded public-source snapshot is assembled. Failures are listed as unavailable, never silently treated as empty documents. The previous snapshot survives a global-bound failure. Generated corpus source is versioned alongside its builder and exact SHA256/Git-blob identities. No publisher papers, private Subspace cache or private Atlas corpus are mirrored.

Current body coverage: 133 immutable referenced Markdown documents, 1,344,746 original UTF-8 bytes, zero unavailable at this capture. This excludes unlinked archive material and is not whole-archive coverage. Source retrieval never grants job execution authority or converts a source hit into accepted mathematics.
