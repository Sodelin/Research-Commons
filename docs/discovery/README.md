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
