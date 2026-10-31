# Research Commons discovery reader

A question-first product over the existing canonical claim register. Search by question, topic, disposition or origin; follow exact source and typed connections; copy a source-pinned agent reuse record. Completed hand mathematics stays completed when formalization is missing.

Canonical data/attribution: Sodelin/Research-Commons docs/claims.json, maintained by Dot and scientific owners. This reader preserves that source and adds navigation, search and exact owner-supplied evidence joins. It does not generate scientific answers or certify novelty.

## Start here: current results and the CLI

Use the **full-result CLI** below to find current published proof sources, partial results, failed approaches, candidates and correction notes. The older **118-card view**, **334-body bundled source view** and **archive-path view** are separate, narrower snapshots. Installing or running one does not populate the full-result body cache.

The executable tools are available in this repository. They require Git, Python3 and Node.js; the commands below were checked here with Git 2.52, Python 3.12 and Node 24. No npm installation, Lean compiler, background service or account connection is needed for these local searches. This does not mean the tools or cache are already installed on another device.

Run from the **repository root**, after obtaining the repository with its Git history. Choose a fresh output directory for the generated cache:

```sh
cd /path/to/Research-Commons
python3 docs/discovery/tools/index-research-results.py --repo . --commit f5cd8bf256d9d1f2a395abf6730bda4375448b3d --output /tmp/commons-results-wong50
node docs/discovery/tools/query.mjs --research-results /tmp/commons-results-wong50/manifest.json \
  --query actual_root_weight_shifted_limit \
  --research-path research/2026-10-31-clock-jc-root-fuel-composition-verified/source/ResearchCommons/MSCI/JC69RootFuelComposition.lean --limit 10
```

For a later snapshot, use `--base /path/to/previous-cache` with a fresh output directory. The same indexer now handles additions, changed notes and removed paths: it rewrites only affected shards and preserves the prior cache. Run `python3 docs/discovery/tools/test_result_delta.py` from the repository root to check source-only additions and stale-body removal without changing claim cards. An archived base may keep `manifest.json.gz`; the live query command still requires its generated `manifest.json` and shards.

Build the cache once, then reuse the last command with another query. Omit `--research-path` to search across every shard; `--offset` and `--limit` paginate the results. The optional path prefix selects the exact source link, useful when an unchanged candidate body also occurs in an accepted packet. `body_document_url` preserves its original deduplicated body link, and `source_paths` lists the shared locations; equal bytes do not transfer status between packets. A machine without this generated manifest **and its body shards** must build them first; the committed receipt alone is not the cache. To verify the same cache:

```sh
python3 docs/discovery/tools/index-research-results.py --repo . --commit f5cd8bf256d9d1f2a395abf6730bda4375448b3d --output /tmp/commons-results-wong50 --check
```

The latest checked local snapshot here is `f5cd8bf2`: **99,604 full-text paths, 1,063 explicitly path-only paths and 33,769 distinct text bodies**, in 180 shards with 33,878 document records. It includes the [adopted CB-SEQ-005 individual finite-edit interface](../../research/2026-10-31-seq005-package-binding/README.md), after SEQ-001/WONG-002/SEQ-004: **52 mapped IDs,549named declarations and66unbound IDs**. Strict coverage still exits2 with116incomplete integrations; all118scientific statuses remain unchanged. The enlarged aggregate/root pass exact coherent-context verification, all549names and selected1,523-module owned audit. The separate public target19 uses7fresh/12reused objects and its two differing provider objects are explicitly retained; no silent same-source substitution, fresh whole1,837 build/audit or native runtime is inferred. Four recent NANUQ/clock accepted joins retain their exact premises and limits; the fixed-port G4 packet is HAND family review, and frozen bigon/core-curves candidates are distinct from later local checks pending review. Historical pending comments and older receipts retain their dated scope. Its [coverage receipt](result-coverage.json), [exact-source query history](result-query-receipt.json) and [publication-version checks](result-publications.json) record their own immutable input pins. Code availability, a published receipt, a generated local cache and a hosted reader deployment are distinct states. **The hosted reader and its bundled historical corpus have not been refreshed by this work.** This tree index covers the selected public roots, not all Git history, binary bodies, private chats or complete linked repositories; the [reference coverage inventory](result-reference-coverage.json) accounts for those separate source-reference gaps and the optional [exact public-reference body supplement](#exact-referenced-public-bodies-beyond-the-tree-roots).

To see what has been completed and what remains, start with the [current full-scope checkpoint](../../research/2026-10-31-scope-reconciliation-1003z/CURRENT-SCOPE.md), then follow the [canonical scientific claim register](../claims.json) and [exact Lean declaration/binding guide](../EXISTING-LEAN-CLAIM-BINDINGS.md). The 10:03 scope checkpoint preserves the original master obligations and distinguishes the historical 1,833-module acceptance from later scoped integration. Its then-unrebuilt aggregate limitation has the explicit later verification receipt above; dated checkpoints are not live process status. The [later terminal software receipt](../../research/2026-10-31-portable-package-context-b-acceptance/README.md) records the completed actual caller and final binding gates, qualified object reuse and still-incomplete all118 coverage. Individual accepted packets retain their exact theorem and audit scope. Frozen candidates and failed versions remain searchable with later acceptance/correction links; a search hit does not transfer acceptance or close an original master question.

The [portable Lean/Rust source package](../../packages/research/README.md) is available on main. From the same repository root, inspect every claim and exact selected module binding without running proofs:

```sh
node docs/discovery/tools/query.mjs --package-root packages/research --ledger
node docs/discovery/tools/query.mjs --package-root packages/research --modules --query DiscriminatingStatusTransport --limit 10
```

These package queries were executed against the materialized main source. The ledger accounts for all118 IDs and the module query ranks the exact declaration module first; lookup itself does not constitute execution or full completion. The actual public run receipt distinguishes1833/520/1296 success from strict coverage exit2. Full-result tree search still selects the three documented roots; package code uses the separate source-bound package view rather than silently expanding the tree coverage count.

The [70-ID source-binding intake](../../research/2026-10-31-unbound70-source-binding-inventory/README.md) identifies exact qualified suppliers and missing complete-card joins without changing the canonical register. Its first proposed CB-SEQ-001 join reuses original first-occurrence proofs; module availability, new export qualification, independent review and binding adoption remain distinct. The inventory is a dated reproducible intake, not a competing status register or an assertion that open scientific masters are solved.

## Run and verify

These older reader commands run from `docs/discovery/` (`cd docs/discovery` from the repository root). They use the selected card/bundled-source views described below. Use the repository-root full-result commands above for the wider current public research tree.

- `npm ci --ignore-scripts --no-audit --no-fund --logs-max=0` installs the locked DOM-test dependency; production has no package installation/build step.
- `node tools/check.mjs` checks the model and actual DOM journeys.
- `node tools/query.mjs --query 'independent routing' --status established` uses the SAME engine for agent lookup. Add `--refresh` for current canonical source in memory.
- `python tools/refresh.py` refreshes the deliberately public source snapshot and exact provenance.
- `python -m http.server 8766 --directory dist` serves a local preview. Stop only this owned foreground process after use.

The static dist folder is the deployable artifact. MiniSearch is locally bundled and integrity/licence pinned; jsdom is test-only. Deployment follows the registered Sites ID in .openai/hosting.json. Never recreate that Site to repair a deployment. Source pushes and exact saved-version/deployment receipts are separate. For rollback, redeploy a previously saved good version and its recorded source; do not alter canonical scientific records.

See ARCHITECTURE.md for tool comparisons, ownership, security boundaries and update/coverage limits. Source and test evidence do not establish full visual browser/device acceptance. Canonical coverage is currently118 selected cards, not the entire historical research corpus.

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

The historical 93-card successor added five existing feedback-model groups and four genome/ownership groups:93cards total, with all84prior objects unchanged. That historical body snapshot contained229sources/2,228,902original UTF-8bytes/zero unavailable. Historical/scoped formal receipts retain literal detail, including the unretrieved deterministic process-exit fact and separately written source/limit bridges. B05 precursors are not allowed to reopen completed B06 actual-law IAP; its excluded infinite-stream strengthening remains separate. The dated75-card reuse overlay does not rank any of the18later recovered groups. Current coverage is recorded in source.json/source-corpus.json; the broader path inventory retains its own older immutable snapshot.

## Source-link validation and reviewed refresh

Credential-named query **and fragment** parameters are refused, including OAuth fragments, hash-router queries and encoded parameter names/assignments. Ordinary scientific anchors remain valid. This is a URL-parameter boundary, not a general secret-redaction or whole-product security guarantee. The same predicate guards canonical source links, browser rendering, agent lookup and subjective-overlay source URLs. Claim and overlay bodies both validate in RAM before any of the four snapshot files is written. A rejected latest browser source preserves the usable bundled snapshot.

For a reviewed producer release, pin the exact source and expected canonical body hash:

```sh
python3 tools/refresh.py --commit f9a65b24a711f5cff9a920d6b1ede3d34e546923 --expected-sha256 b4c4f52a5e25d7c82df329a403dbacc3a12afd337a847d9f492bf4fe465738c9
```

The bundled canonical snapshot has118cards. The evidence corpus now has328public bodies/3,310,025original UTF-8bytes/zero unavailable, including owned reading-join sources. Live registry updates are fetched separately after validation; this bundled count is not a claim about the current canonical total. All97previously bundled card objects are unchanged;21later canonical cards retain their own exact assumptions/evidence and do not transfer acceptance between population, topology, Wong, cross-scale, feedback or RNA scopes. The dated75-entry subjective overlay leaves43later groups unranked. Node and Python3 are required for the complete verification runner; production remains static and does not need Python. Five refresh-guard controls execute the real shared Node validator with memory-only synthetic fixtures and spied writes; no fixture payload is written.

Bibliography projection stores the normalized safe URL, so equivalent host/default-port spellings deduplicate in both the reader and reuse packet. Distinct scientific anchors remain separate; canonical authored source objects/bytes are unchanged.

Existing formal suppliers are discoverable by exact declaration, including `actual_total_original_strategy_has_bounded_plan`. The owned declaration/module/hypothesis guide at `fa627492d9521a72a604952527d570571fe0fff7` is linked from G1/G2/G6/G7/CM cards and their reuse packets and indexed by the same source search. Its `owned_reading_join_source` binding is navigation, not an accepted-artifact assertion or new proof/package/native acceptance. The first three Lean-reviewed joins retain their original objects unchanged.

## See what changed without reading commits

The reader compares the validated loaded register with its exact bundled snapshot and lists newly indexed cards, changed source fields and cards absent from the loaded register. Each current card opens in the existing detail view; both immutable source pins remain visible. Newly indexed is not newly discovered/proved, and absence is not deletion of historical evidence. Unchanged objects ignore JSON key ordering; array order remains part of the authored source. This is an endpoint comparison, not every intervening revision.

```sh
node tools/query.mjs --changes --refresh --limit 25
node tools/query.mjs --changes --refresh --topic G3 --limit 10
```

The same comparison engine powers browser and agent output. CLI results have bounded limit/offset/next_offset and separate baseline/current source metadata. Claim facets apply to the current card, or the older card when absent; source-body/archive lookup and subjective sorting remain separate views. Network source stays in RAM; canonical source is never written by this command. If a later refresh fails, the browser identifies the actual retained loaded source and keeps its previous comparison rather than labelling it as the bundled fallback.

## Later assessments and older G3 suppliers

The dated110-card subjective top-ten note is linked beside the historical75-card ordering, included in agent reuse records, and searchable as an authored assessment body. It supplements that ordering; the75-entry JSON/ranks are unchanged, and no full110/114 ranking or objective importance/novelty metric is invented.

The G3 detail/reuse view now links six exact older proof/review bodies for COMMON completion/support, the WQO antichain obstruction and strengthened positive-flow/separator results. Later scoped hand acceptances supersede preparation-time pending labels. These are external suppliers, not extra entries in the frozen58-note census or proofs closing total all-input G3 recognition. Their precise limits remain in the join and original sources.

`node tools/refresh-sources.mjs` reuses existing immutable public bodies only after byte/SHA256/Git-blob identity checks, retaining current source bindings and checking any supplied owner pins. Invalid retained bytes are fetched again; conflicting producer pins are refused. The actual refresh reused246 verified bodies and fetched7 new body URLs, plus its existing two catalogue metadata reads. No query/runtime cache is created.

The G3 detail/source/reuse route also includes G3-ARITH-INDEP-RECIP-EQ-01: author-complete fixed-base independent reciprocal-count equality/disequality decision, not independent review, Lean verification or original G3 closure. The source/status and Dot scope receipt remain distinct. Signs, moving bases and unrestricted source NO remain outside this supplier; no new canonical status or accepted-artifact entry is invented.

## Completed conditional P1 transfer

The reader’s P1 cards now link the original19October proof/scoped hand review and Dot’s later correction at342f2ed3d5b2628f846f54b80d07d8305afa1723/docs/P1-P5-ACCEPTED-WORK-ADDENDUM.md. Finite minimax/off-net/two-source conversion is completed CONDITIONAL on the stated uniform squared-Bures risk premise, with exactly n copies per source and explicit finite-precision slack. The sharper uniform original-class risk/increment premise remains unsupplied; do not rederive the completed conversion. Upper13, lower domains and P5 remain unchanged.

Nanowire CB-NANO-001/005 now link the reviewed fixed60-site ALL-PAIR whole-curve decidability theorem and existing hand review. Two fixed profiles remain outside the EVERY-field quantifier; the original-instance decision/certificate remains unsupplied. In-principle whole-curve separation requires both margin classes nonempty and does not certify a finite observation menu or fixed tolerance. No new execution or device claim follows.

The G3 reading/source/reuse view also links G3-ARITH-ROOT-ORDER-LOGZERO-01:author-complete two-way arithmetic classification with ONE common reciprocal count. It supplies neither a log-zero algorithm nor undecidability or full physical-source recognition. The independent-count equality-only supplier remains separate. Its existing owner accepted the earlier equality-supplier source association, not whole-reader or mathematical independent acceptance.

## 25 October successor reconciliation

Canonical snapshot edf623827aa478cfa6190ad230cb194e6fda8571, board1.20:118IDs retained. Complete byte identity SHA256092fd2729486b3b860763a1c962dfe837c93f5a02f3f6af6f44abc53a05a420b / Gitblob2916937c16974b610f1548deae19465694c63fc1. Only CB-MEMORY-004 and CB-G4-006 objects differ from the previous bundled register: later calibration formal/execution evidence and partial finite-original-equation checking respectively. Mathematical statements and other116objects preserved. Calibration original known-rate IID formal binding is distinct from universal Rust refinement; G4 partial checking does not certify full descent or original finite-I stopping.

Three dated owner-review bodies added to the SAME reading joins and evidence search: G3/G4 progress adoption atf5de412d, NetCS/recovery comparison at35bb3123, and terminal retained-profile review atb5f0e6e. Complete public bytes/Gitblob identities verified before corpus inclusion. These are attributed owner source/review records, not a new independent paper/proof review. Cap9 source-linear versus cap12 ordinary-energy, supplied I-event versus total ONE-witness palette, completed G4 branches versus every-finite-rival gate remain explicit. No duplicate derivation/build is requested. Existing public source links allow deeper proof/receipt reading without promoting the owner reviews into new canonical claims.

Corpus331immutableURLreferences/3,330,048UTF8B/zero unavailable. Prior328bodies reused after identity checks;3new owner-review bodies fetched, plus existing recovery-catalogue metadata. Old58-note/17-source-only census and separately pinned5829archive paths are historical selected scopes, not exhaustive current history. Actual terminal jobAPI120423643520 independently confirms completed/failure at0b9e1cc1; the owner's detailed review separates successful profile step from later caller failure and records superseding particular callers. No compiler rerun/artifact download/model/native job.

62implementation records pass across6explicitmodules, including formal-evidence export and successor/retired-task scope regressions. These validate consumer behavior, not scientific acceptance. Actual visual/device/accessibility acceptance remains unverified.

## Original successor proof-body integration —25October2026

The same G3 reading/source/reuse join now links three complete ORIGINAL supplier proofs behind the dated owner adoption, rather than only its review summary. Full bodies were read and independently checked for bytes/SHA256/Gitblob identity; no independent mathematical correctness review is claimed. Matched cap9 source-linear proof atfe1f8a75:12383B/SHA2565801efb496cf76f7a0259513bb334c12b9688645792d7a32b35861bbb696a8e1/blobcf49b419fc4aa2ca52e87385c6a08f829903a424. Resonant cap12 ordinary-energy proof atb0be735c:13183B/SHA256200bb6bab172bcb56a42bf2f95ab5d2f711a0e918b8edbf8be32056b970faceb/blob1253e4fe588b1c62cf2bf9ce2a23e6877baf6896. Observed-cohort proof atbb9521ba:17329B/SHA25687e880abbe52641321cc170bb7861f087e5eaafa6e485826003e6100eb520641. Literal stable keys are now searchable in ORIGINAL full text.

Older linear proof’s then-missing ordinary-forcing paragraph is superseded by its completed cap12 successor; cap9 is not silently upgraded. The I-only theorem requires a supplied unconditional event/known channel, actual proper CLOSED bridge and same original source/tuple; no new observation or total ONE-witness finite-bank selector is supplied. These author-hand/self-reviewed proofs remain separate from independent correctness/Lean/execution and total G3. Canonical118/board1.20 unchanged, no competing claim IDs.

Corpus334immutable URLreferences/3,372,943UTF8B/zero unavailable:331prior verified bodies reused,3original proofs fetched plus existing catalogue metadata. Frozen58-note census and5829path inventory remain separate, dated/non-exhaustive.63consumer records pass across6explicitmodules, including all3stable-key retrievals, exact identities/claim bindings and successor-gap distinction. No proof/compiler/native/model/device job or original-owner task was repeated. Actual visual/device acceptance remains unverified.


## Lookup safeguards verified — 25 October 2026, 11:09 UTC

The documented programme example has been corrected: `--programme` matches the full literal display field, such as `G3 · finding a real source`; `--topic G3` selects the G3 cards. `--programme original.G3` returns zero and must not be interpreted as an empty research programme.

For comprehensive supplier-body discovery, run `--sources --query ...` WITHOUT claim facets first. Catalogue-only recovery bodies intentionally carry catalogue keys rather than claim IDs; adding `--topic G3`, `--status open`, or another claim facet can exclude those completed supplier bodies. In a verified runtime check, G3-UNIFORM-FOREST-RECEIVER returned14 unfiltered source hits versus6 with the G3 topic facet. The narrower filtered view is not a full programme-source inventory.

Paginate using total/next_offset. Distinguish card freshness, immutable body snapshot freshness, and the older archive path pin. A zero `--changes` result only compares card objects; it does not say no proofs or source-status records changed. JSON status documents, issue comments and source-only Lean files require their own linked checks outside this Markdown-body index.

Current copied runtime and all334 corpus body byte counts/SHA256/Gitblob identities were checked during the coordinating audit. This verifies retrieval integrity, not mathematical correctness or exhaustive coverage. Latest research additions after the archive pin require a Git-tree delta check; contents-directory listing can cap at1000 entries. Do not infer missing mathematics from an empty/truncated retrieval.


## Programme and output navigation

The read-only companion uses `docs/programmes.json`, `docs/dissemination.json` and the SAME current checkout's `docs/claims.json`. It does not rename existing claim facets or alter mathematical acceptance. Run from the repository root:

```sh
node docs/discovery/tools/programmes.mjs --programmes
node docs/discovery/tools/programmes.mjs --programmes --id PROG-G1-G7
node docs/discovery/tools/programmes.mjs --outputs --id OUT-NANUQ-001
```

Results include exact local file SHA256 identities, bounded output states and the joined canonical claim objects. This is a local-checkout view, not automatic remote refresh or evidence that any worker is executing. Empty claim bindings mean “not mapped here,” not “no work exists.” The older `tools/query.mjs` and deployed reader remain unchanged. See [definitions and gates](../PROGRAMMES-AND-DISSEMINATION.md).

## Every published result: full-tree CLI search

Follow the shared [every-result completion workflow](../../communications/2026-10-30-every-result-discoverable-2341z.md). The 118 claim IDs and their status fields remain the canonical claim register. A source body can be useful without having a claim card: partial proofs, failed approaches, counterexamples and superseded results belong in discovery with their original labels and correction links.

The complete local body index uses the existing `source-search.mjs` engine. It inventories every Git entry under `research/`, `handoffs/` and `communications/` at an immutable commit, deduplicates identical blobs while retaining every path, and shards UTF-8 bodies. It includes Markdown, Lean, JSON receipts, logs and source code; it executes none of them. Dependency/cache subtrees, binary/archive representations, non-UTF8 bodies and files larger than16MiB remain path-only with explicit reasons in `manifest.json`. Linked external repositories and deleted historical commits need their own pinned inventories. This is complete accounting of the selected tree, not a claim that binary or oversized bodies have full-text coverage.

```sh
# Use a fresh output directory outside the checkout; the full corpus can be large.
python3 docs/discovery/tools/index-research-results.py --repo . --commit HEAD --output /tmp/commons-result-index
python3 docs/discovery/tools/index-research-results.py --repo . --commit HEAD --output /tmp/commons-result-index --check
node docs/discovery/tools/query.mjs --research-results /tmp/commons-result-index/manifest.json --query JC69Factorization --limit 10
```

Queries support `--offset` and `--limit` across all shards. Source-only results have no inherited claim acceptance; output joins existing canonical claim references by source path where available. Claim-status/topic facets are deliberately refused in this body view because they can hide unbound suppliers. Read the returned source's authorship, review, formal/execution evidence and supersession text before reuse. A source hit is neither a new discovery count nor proof acceptance.

The deterministic `--check` verifies complete tree accounting, every body hash/Git blob, shard bytes and path correspondence; it also fails when the requested current research tree differs from the indexed tree. Run it after publishing results. Rebuild after a failure; an unchanged claim-card diff does not establish source freshness. Preserve the original source and publish corrections with supersedes links.

The tools and coverage receipt can be committed independently of generated local body shards. A successful local query or a committed receipt does not update the hosted reader, its bundled334-body corpus, or its older archive-path snapshot. No deployed full-text refresh is claimed by this change.

For a publication that only adds paths, extend an existing index without replacing its earlier immutable source bindings:

```sh
python3 docs/discovery/tools/index-research-results.py --repo . --commit NEW_COMMIT40 --base /tmp/commons-result-index --output /tmp/commons-result-index-next
node docs/discovery/tools/query.mjs --research-results /tmp/commons-result-index-next/manifest.json --research-path research/2026-10-30-clock-jc-bounded-qa-2350z --query counterexample
python3 docs/discovery/tools/check-result-publications.py --repo . --index /tmp/commons-result-index-next --publication NEW_COMMIT40
```

Extension refuses modified or deleted prior paths; use a full rebuild in that case. Hash-verified unchanged shards are reused with their original immutable URLs. Incremental additions may repeat a previously stored body under a new path; distinct body hashes and search document counts are separate. `--research-path` is an explicit optional prefix filter; unfiltered search remains available. Publication coverage reports original versions that differ from the current tree as explicit gaps rather than silently equating them. Private inventories are not copied into this public index.

### Exact identifiers and references beyond the selected roots

Exact catalogue keys, immutable source URLs/paths, lexical declaration names and literal identifiers rank ahead of related token matches. This ordering applies across body shards, while broad matches remain paginated. Lexical declaration detection is retrieval evidence, not a Lean ownership or acceptance audit. The corrected `all_size_anchor_nonnegative` query returns its defining `CoefficientTransport.lean` at offset0; the older offset100 observation remains historical in the receipts.

The selected roots are not every user result. [Canonical reference coverage](result-reference-coverage.json) reconciles claim, programme, dissemination and reading-join links, including docs/packages and linked repositories outside those roots. It distinguishes bodies in the separately pinned334-body corpus, identical blobs in the current tree, unbound external bodies, unversioned links and other explicit gaps. These labels describe retrieval coverage, never mathematical openness or acceptance.

```sh
python3 docs/discovery/tools/reconcile-result-references.py --repo . --manifest /tmp/commons-result-index/manifest.json --output /tmp/reference-coverage.json
node docs/discovery/tools/query.mjs --reference-coverage --query packages --limit 10
```

`--reference-coverage` reads the committed reference receipt; the generation command accepts a freshly checked body manifest. Its metadata inputs come from that exact Git commit, with byte hashes. Historical query-run counts are preserved with an explicit correction where an earlier `unique_text_bodies` field actually counted indexed documents. Current coverage distinguishes distinct blob hashes from document records and paths. No whole-history, full-binary, private-task or all-linked-repository coverage is claimed.

## Local package declaration-check bridge

The local tooling also joins this SAME search model to the portable package.
`--package-root` takes an existing `packages/research` checkout; it verifies its
producer lock and every selected Lean source, preserves all canonical IDs and
returns exact declarations, owners, source identities, historical printed types,
runtime state, scientific obligations and the existing checker command. It does
not recompute or override the Rust strict-completion gate. A named declaration
check is separate from a scientific solver and from native/provider refinement.

```sh
node docs/discovery/tools/query.mjs --package-root /path/to/packages/research --query CB-MEMORY-004
node docs/discovery/tools/query.mjs --package-root /path/to/packages/research --ledger > coverage.json
node docs/discovery/tools/query.mjs --modules --package-root /path/to/packages/research --query DiscriminatingStatusTransport
node docs/discovery/tools/check-claim.mjs --package-root /path/to/packages/research --claim CB-MEMORY-004 --execute --receipt new-observation.json
node docs/discovery/tools/query.mjs --package-root /path/to/packages/research --observation new-observation.json --query 'CB-MEMORY-004 UNKNOWN'
```

A separate explicit local evidence view makes scoped checks searchable even when
no canonical claim card or package module has been updated:

```sh
node docs/discovery/tools/query.mjs --scoped-evidence /path/to/scoped-evidence.json --query pointSet_eq
```

The manifest names local source files, a named type/axiom log and an owned-audit
JSON, each with a SHA256. Paths must remain inside the manifest directory. The
reader verifies file hashes, selected-module uniqueness, named ownership, the
matching named/owned axiom rows and empty rejection lists before using the same
source search engine. It returns the exact local source identities, printed
types, selected scope and limitations. It does not run Lean, independently
authenticate the receipt or prove that a listed source produced that audit, and
it never changes claim, native-runtime or full-package status. Multiple explicit
manifests can be searched together; ordinary claim facets deliberately do not
apply to this view. Example manifests and their actual bounded receipts accompany
the local handoff rather than replacing the published historical corpus.

Without `--execute`, the check adapter only prints its plan. Execution uses the
existing Rust checker with offline Cargo, actual usable pinned Rust/Lean compilers
(including the official direct Lean release without an elan installation),
an existing exact audited target build, a 45-second limit and a 4 MiB output
limit. It installs nothing and starts no remote build. Missing prerequisites,
rejections and limits return UNKNOWN/exit2. Only the actual complete scoped
checker receipt can produce CHECKED_SCOPED_DECLARATIONS; successful process exit
alone cannot. Observations are explicit local files with hashes and an explicitly
limited metadata-file match field, not authenticated acceptance. That comparison
does not establish checker/runtime/Cargo/toolchain or whole-environment identity.
Observations are never written into canonical cards.
The original source/observer/target/history/IDs/one-bank premises stay in the
source declarations and authored scope fields. Historical printed types are
labelled separately; missing type rows require the actual named check. Checked
contexts must include the entire transitive project dependency closure and contain
no duplicate modules. A larger explicit audited context is allowed when it remains
dependency-closed and every listed source hash matches. Only declared
Lean/Init/Std/Mathlib provider namespaces are external; an unknown missing project
import refuses. Canonical package source
URLs are emitted only for clean checkouts with the supported repository origin
and canonical packages/research location; otherwise local source hashes remain.

New proof bodies can now be ingested even when no claim card changed. Use a
complete bounded local Git-tree delta between two full commit IDs in an existing
Research-Commons checkout, then merge into a NEW corpus:

```sh
node docs/discovery/tools/ingest-git-delta.mjs --repo /path/to/Research-Commons --from COMMIT40 --to COMMIT40 --base docs/discovery/dist/source-corpus.json --output new-supplement.json
node docs/discovery/tools/merge-sources.mjs docs/discovery/dist/source-corpus.json new-supplement.json new-corpus.json
node docs/discovery/tools/query.mjs --sources --corpus new-corpus.json --query 'endpoint freedom'
```

This path reads changed Markdown blobs in research/handoffs/communications from
exact local Git objects, verifies byte/SHA256/Git-blob identity, records excluded
and unavailable paths, and refuses over 2,000 changed paths or 100 selected
bodies. Each body is bounded to 512 KiB and each corpus to 16 MiB. New documents
retain a source-only navigation role without inferred claim acceptance or master
status. JSON/status files, comments, Lean bodies, unchanged older omissions and
other roots need their separate readers; this is not full archive coverage.
Existing bodies, canonical records and deployed snapshots are preserved. Use
unfiltered source search and pagination before narrowing with claim facets.
The shared browser/CLI source index also searches immutable URL paths. A new
source directory key can therefore find its body even when that key occurs in
neither its prose nor the canonical claim register.

Node supplies this adapter because the reader already shares its validated model
and ranking engine across CLI/browser; the existing Rust package remains the
execution/completion authority. The adapter adds no duplicate mathematical engine
or taxonomy, no model service, no installer and no deployment dependency.

`--modules` searches the same source engine over exact package module identities,
imports, source provenance, recorded supplier names and any source-matching external
context receipt. This finds suppliers that have no direct named claim mapping,
without inventing a canonical claim binding. Claim facets, claim observations and
register refresh are deliberately refused in this source-only view. An external
60-source receipt can be current while the full1500/520-name/all118 gates remain
pending; historical source-only headers do not override a later exact matching
receipt. Reading that metadata is neither a new compiler execution nor automatic
cache admission. Reuse the closed context instead of rerunning it because the
broader package is unfinished.


### Exact referenced public bodies beyond the tree roots

The same `--research-results` query can join an explicit, verified reference-body
supplement with `--reference-bodies CORPUS`. It uses the existing source search
engine, exact-identifier ranking and **one global pagination sequence**. Each
extra hit returns its own repository, exact revision, Git blob, SHA256, license
observation and canonical reference association. The association is a citation,
not a transfer of claim acceptance or a runtime proof.

[Reviewed public input identities](referenced-public-inputs.json) bind the 128
previously unbound first-party reference records to **120 distinct immutable
source bodies**. Anchor variants explain repeated references. The four exact
public repository pins are in that receipt; repository visibility and missing
root-license observations are explicit. Owner-authorized research indexing does
not invent an open-source license. Eight additional exact Commons source
versions from docs/packages and a changed historical research note are joined
alongside them. Two other-owner references stay link-only. Missing cited files
are reported as `repository_artifact_missing_at_pinned_ref`, separately from
real files outside the selected roots; no replacement evidence is guessed.

Materialize only the reviewed public bodies using an authorized connector or
existing pinned checkout, retaining this layout below a chosen `BODY_ROOT`:
`OWNER--REPOSITORY/40-CHAR-COMMIT/original/path`. No downloaded source is executed.
The offline intake verifies every byte length, SHA256 and Git blob against the
published input receipt. The canonical-reference coverage receipt supplies the
exact citations; the intake also accepts its already-covered successor.

```sh
python3 docs/discovery/tools/index-referenced-bodies.py --repo . \
  --verified-inputs docs/discovery/referenced-public-inputs.json \
  --body-root BODY_ROOT --references docs/discovery/result-reference-coverage.json \
  --output /tmp/commons-reference-bodies.json
node docs/discovery/tools/query.mjs \
  --research-results /tmp/commons-result-index/manifest.json \
  --reference-bodies /tmp/commons-reference-bodies.json \
  --query path_projects_strict_of_distinct_owners --limit 25
python3 docs/discovery/tools/reconcile-result-references.py --repo . \
  --manifest /tmp/commons-result-index/manifest.json \
  --reference-bodies /tmp/commons-reference-bodies.json \
  --output /tmp/reference-coverage-current.json
```

[The exact-source query receipt](referenced-body-query-receipt.json) records all
128 distinct supplemental documents and their matching immutable identities.
[Supplement coverage](referenced-body-coverage.json) records input/output hashes
and current limits. These generated bodies are local CLI inputs. Committed code,
committed receipts, prepared source payloads and the unchanged hosted 334-body
reader remain different delivery states. This is not every linked repository,
all history, private source coverage or every unpublished manuscript. Continue
the [shared contributor workflow](../../communications/2026-10-30-every-result-discoverable-2341z.md)
for every new result and verify its exact body, not a related fuzzy hit count.
