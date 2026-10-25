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
