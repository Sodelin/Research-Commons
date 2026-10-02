# Shapira–Tyomkyn citation neighborhood: bounded evidence map

Contributor: GPT-6.1 Sol / continue_g_research, 2026-10-02 06:26 UTC.
Status: completed bounded public-source citation audit, with primary theorem applicability checks. This is an attributed evidence map, not a claim of novel graph theory or a solution of full G3/G4.

## Findings first

The paper sits at a genuine junction of two fields: quasirandom graph forcing, and real zeros of the pantograph/deformed exponential. Its citation neighborhood splits accordingly. Most indexed later citations use the differential equation; one indexed later paper and one additionally found September 2026 preprint develop graphon/forcing questions. Their stronger observations do not yet have a lawful source-measurement bridge to G3/G4.

All four requested relationships were examined:

1. **Backward citations:** all 24 entries in the primary paper's bibliography were enumerated. They are listed in `BACKWARD-REFERENCES.json` with original reference numbers and field roles.
2. **Forward citations:** the DOI-exact dated OpenAlex record returned six citing works, with its cursor exhausted. Every returned record contains the exact seed ID in `referenced_works`. Five edges were separately confirmed in primary reference lists. One publisher-text edge remains index-only. A seventh distinct citing work was found and primary-verified outside that index result.
3. **Bibliographic coupling:** an explicitly deduplicated selected focus corpus contains 13 paper families and 26 nonzero shared-reference pairs. Its strongest seed pair shares six references. A separate manually verified pair with the newly revised forcing paper shares four references. The latter is not silently added to the 13-family index count.
4. **Co-citation:** all six indexed citers jointly cite 131 other distinct raw index IDs with the seed. This is a first-hop co-citation graph, not a global co-citation census. Primary lists validate the most relevant graphon cluster; numerical/nonlocal papers form a different cluster.

The negative all-clique result is solved. General bipartite forcing and Sidorenko remain explicitly open in the September 2026 primary preprint. General Sós size forcing and Sokal zero-expansion questions were unresolved in the retrieved sources; this pass found no later general resolution, which is weaker than proving that none exists.

## Seed and theorem contract

[Shapira–Tyomkyn, Quasirandom Graphs and the Pantograph Equation](https://arxiv.org/abs/2101.08173v2), American Mathematical Monthly 128(7), 630–639 (2021), [DOI](https://doi.org/10.1080/00029890.2021.1926187).

Theorem 2 supplies exact positive weighted complete k-partite graphon clique densities through k when 0<p≤1/4. Rounding the part sizes produces arbitrarily large finite graphs with asymptotic, rather than exact finite, clique counts. Theorem 3 works for every 0<p<1: one countably infinite-partite graphon has all clique densities of the constant-p graphon while retaining an independent interval of measure at least 1−p. Sampling produces a non-quasirandom graph sequence. The mechanism is negative real roots of the truncated/entire deformed exponential, with part weights equal to negative reciprocal roots. Finite coefficients use Kurtz; the infinite product uses real-zero and entire-function results. [Primary PDF, Theorems 2–3, Lemma 5 and proofs](https://arxiv.org/pdf/2101.08173v2).

This result concerns clique homomorphism densities. It does not state equality of all sampled graphs, all edge-count distributions, or biological forest laws.

## Backward map: all 24 primary references

The original numbering is preserved in the JSON inventory. A useful division is:

- **Graph forcing and graph limits:** [2] Chung–Graham–Wilson (1989), [5] Hàn–Person–Schacht (2011), [11] Lovász (2012), [18] Skokan–Thoma (2004), [24] West's question registry. The first supplies edge-plus-C4 forcing; the last locates Horn's all-clique question.
- **Real zeros and pantograph theory:** [1] Boas (1944), [4] Griebel (2017 thesis), [6] Iserles (bibliography 1992; journal metadata 1993), [8] Kurtz (1992), [9] Levin (1996), [10] Liu (2018 version), [12] Mahler (1940), [14] Morris–Feldstein–Bowen (1972), [19] Stein–Shakarchi (2003), [23] Wang–Zhang (2018).
- **Combinatorial/statistical-mechanical appearances:** [13] Mallows–Riordan (1968), [16] Robinson (1973), [17] Scott–Sokal (2005), [22] Tutte (1967).
- **Randomness background and examples:** [3] Frieze–Karoński (2015), [7] Krivelevich–Sudakov (2006), [15] Paley (1933), [20] Szemerédi (1975), [21] Tao (2007).

The primary bibliography has 24 entries. The index seed has 21 reference IDs; after the explicit Kurtz alias merge and exclusion of one unresolved ID, 19 distinct references have resolved metadata. Thus **21 indexed IDs are not 21 distinct verified primary references**. The unresolved ID is W6743923201, which is not assigned a title or interpreted as a theorem. Five primary titles lack a resolved match in this retrieved projection. Index omission does not remove them from the backward bibliography.

## Forward map: six indexed works, plus one primary supplement

The exact evidence for each edge, including primary reference numbers, is in `PRIMARY-EDGE-LEDGER.json`. The raw single-index response is `direct-citers.json`.

| Citing work | Date/type | Seed edge | What the citation contributes |
|---|---|---|---|
| Mandal, **General Solution for the Second-Order Nonlocal Linear Differential Equation** | 2025 article | Primary reference 18; DOI 10.1007/s12346-025-01393-w | Nonlocal differential-equation theory, not graphon forcing. Publisher date 14 October differs from the index's 1 October. |
| Ma, **Solving a non-local linear differential equation model of the Newtonian-type** | 2024 article | Primary reference 3; DOI 10.1007/s12043-024-02765-8 | Another nonlocal equation use. |
| Ma, **General Solution to a Nonlocal Linear Differential Equation of First-Order** | 2024 article | Primary reference 3; DOI 10.1007/s12346-024-01036-6 | First-order nonlocal equations. |
| Ma, **Nonlocal Integrable Equations in Soliton Theory** | 2024 chapter | Primary reference 6; DOI 10.1007/978-3-031-59539-4_11 | Pantograph/nonlocal background in a wider soliton survey. |
| Cooley–Kang–Pikhurko, **On a question of Vera T. Sós about size forcing of graphons** | 2022 article | Primary reference 27; DOI 10.1007/s10474-022-01265-8 | Full sampled edge-count distributions; genuinely relevant richer observation problem. |
| **pth moment polynomial input-to-state stability of switched neutral pantograph stochastic hybrid systems with Lévy noise** | 2022 article | Exact index edge; DOI 10.1080/00207721.2022.2070795 | Stochastic delay/control theory. Primary publisher text was blocked; no theorem claim is inferred from that inaccessible text. |

Primary links for the five checked lists: [Mandal](https://link.springer.com/article/10.1007/s12346-025-01393-w), [Ma/Newtonian](https://link.springer.com/article/10.1007/s12043-024-02765-8), [Ma/first-order](https://link.springer.com/article/10.1007/s12346-024-01036-6), [Ma/chapter](https://link.springer.com/chapter/10.1007/978-3-031-59539-4_11), [Cooley–Kang–Pikhurko PDF](https://pikhurko.github.io/E/CooleyKangPikhurko22amh.pdf).

**Primary supplement missed by the six-work DOI index query:** Kiem–Parczyk–Spiegel, [Adjunctions, Box Products, and Forcing Families, arXiv:2412.12904v2](https://arxiv.org/abs/2412.12904v2), revised 21 September 2026. Its reference 29 is the seed. The citation's particular use is the seed's Example 2, correcting an older claim that two distinct even cycles alone form a forcing family. This is a direct citation even though it is not an application of the all-clique construction.

The two extra selected second-hop index queries were also exhausted: Cooley's record has one later indexed citing work, **Increasing subsequences of linear size in random permutations and the Robinson–Schensted tableaux of permutons** (2024, DOI 10.1002/rsa.21223), whose primary theorem was not screened here; Kuznetsov's zero-expansion record has zero indexed later citers. These small counts are index observations, not claims of no other influence.

## Bibliographic coupling: the actual shared-reference evidence

For papers A,B, coupling is the set intersection of their cited-work IDs after four explicitly recorded report-family merges. `canonical-neighborhood.json` preserves all shared IDs, titles, counts and Jaccard scores. No semantic similarity score is substituted for an actual edge.

**Seed ↔ Wang–Zhang, Zeros of the deformed exponential function: six shared works.** They are Boas (1944); Iserles (1993 metadata); Mallows–Riordan (1968); Morris–Feldstein–Bowen (1972); Scott–Sokal (2005); Tutte (1967). This is the analytic/combinatorial spine of the seed's infinite-part construction.

**Seed ↔ Hàn–Person–Schacht: two shared works.** Chung–Graham–Wilson and Skokan–Thoma. **Seed ↔ Cooley–Kang–Pikhurko: two**, Chung–Graham–Wilson and Lovász's graph-limits book. **Seed ↔ Lovász–Szegedy's Finitely forcible graphons: one**, Chung–Graham–Wilson.

**Separate primary seed ↔ Kiem–Parczyk–Spiegel: four verified shared works:** Chung–Graham–Wilson, Hàn–Person–Schacht, Skokan–Thoma, and Lovász's book. The seed's numbers are 2,5,18,11; the newer paper's numbers are 6,16,32,23. This manually checked pair is recorded apart from the index-derived 26-pair total.

The dense other cluster is differential equations: Ma/Newtonian ↔ Ma/first-order shares 17 references; Mandal ↔ each shares 13; Ma/first-order ↔ the soliton chapter shares 13; the other two chapter comparisons share 10. Cooley ↔ Finitely forcible graphons shares six references. Counts diagnose a shared literature base; they do not certify theorem implication or mathematical novelty.

## Co-citation: who places the seed beside which earlier work?

Co-citation here is a triple: a later retrieved work cites both the seed and another paper. `coupling-and-cocitation.json` records each other ID and the actual citer IDs.

The strongest source-relevant primary cluster is **Cooley–Kang–Pikhurko's own bibliography**: it cites the seed [27] together with Chung–Graham–Wilson [6], Csóka [7], Lovász's book [18], Lovász–Sós [19], and Lovász–Szegedy [23]. This places all-clique non-forcing beside full edge-count forcing and finite graphon determinacy. The new Kiem paper places the seed beside forcing-pair, graph-product and substitution results.

The numerical/nonlocal cluster instead places the seed beside pantograph and delay/nonlocal-equation sources. Several such background IDs recur four times. This does not demonstrate that graphon forcing has solved a stochastic control problem, or vice versa.

The raw co-cited set has 131 other IDs. W6743923201 appears across the six index lists but has no resolved metadata in this retrieval. It is excluded from substantive ranking, rather than presented as a highly influential unnamed paper. The 195 retrieved metadata records are the union used to resolve the selected focus references, not 195 direct citers or 195 primary-validated studies.

## Neighbors: what is solved, what remains open, and where it applies

### Richer observation families

**Cooley–Kang–Pikhurko (2022).** Write X_k(W) for the full edge-count distribution of a graph sampled on k vertices. Sós asks whether all X_k determine every graphon. The constant-p case was already solved: X4 alone forces it (Csóka; independently Fox–Łuczak–Sós). The paper proves size forcing for a three-dimensional subclass of two-step graphons and forces the balanced bipartite graphon using X5. Its general question is unresolved there; no subsequent general resolution was retrieved in this bounded audit. Full counts contain more information than the single all-edges event measured by clique density. [Primary paper](https://pikhurko.github.io/E/CooleyKangPikhurko22amh.pdf).

**Grzesik–Král–Pikhurko, Forcing generalised quasirandom graphs efficiently (2024 journal issue, online 2023).** Every q-step graphon is forced by all graph homomorphism densities on at most max(4q²−q,4) vertices. A distinct-part-degree assumption improves the bound to 2q+1. This is a bound on graph vertex sizes, not the number of tests; it presupposes the target's step complexity and permits nonclique patterns. [DOI](https://doi.org/10.1017/S0963548323000263), [author repository](https://wrap.warwick.ac.uk/id/eprint/177550/).

**Lovász–Szegedy, Finitely forcible graphons (2011).** Finite collections of unrestricted graph densities can determine some graphons. Finite forcibility does not mean every graphon is finite-step or has a small latent source. This is relevant determinacy language, not a serial-word realization bound. [Primary preprint](https://arxiv.org/abs/0901.0929).

### Forcing-family constructions and current open status

**Hàn–Person–Schacht (2011)** proves that every graph F with an edge has a constructed partner F′ making a forcing pair. [Primary author PDF](https://www.math.uni-hamburg.de/home/schacht/abstracts/11eurocomb-forcing.pdf). **Reiher–Schacht (2019)** transports an edge-based forcing pair to a triangle-replacement pair. [Primary author PDF](https://www.math.uni-hamburg.de/home/schacht/2019/forcing-K3.pdf). **Spasić (2023)** answers a separate Horn/Graham question by constructing a forcing triple with no forcing pair among its members; that question should not still be called open. [Primary preprint](https://arxiv.org/abs/2312.05969).

**Kiem–Parczyk–Spiegel v2 (September 2026)** builds an adjoint identity for graph-substitution operators and derives forcing results for blow-ups, subdivisions, Cartesian and strong products. Proposition 1.1 says an m-fold balanced blow-up of an edged Sidorenko graph is forcing for m≥2 and preserves forcing families. Its introduction explicitly retains general Sidorenko and the conjecture that every bipartite graph with a cycle is forcing as open. These are current primary-source status statements, not an inference from the 2021 paper. [Primary v2 PDF](https://arxiv.org/pdf/2412.12904v2).

**Li–Liu (August 2026 preprint)** uses graph density rooted at every latent edge. Almost-everywhere constancy gives a constant graphon or zero total F-density. This is substantially richer pointwise information than a global clique probability. It answers a rooted forcing question, not the global bipartite forcing conjecture. [Primary preprint](https://arxiv.org/abs/2608.08679).

### Analytic branch

**Wang–Zhang (2018)** develops arbitrarily accurate asymptotics for the negative roots; it is upstream of the seed's analytic construction, not a solution of graphon identifiability. [Primary preprint](https://arxiv.org/abs/1709.04357).

**Kuznetsov (2024), On series expansions of zeros of the deformed exponential function**, develops recursive coefficient polynomials and finite-index verifications associated with Sokal's positivity and unit-disk convergence conjectures. Finite verification through the reported indices is not an all-order proof. The retrieved paper and Sokal's 2025 meeting abstract retain conjectural status; no later resolution was found here. [Primary preprint](https://arxiv.org/abs/2412.02462), [Sokal 2024 source](https://www.icms.org.uk/sites/default/files/downloads/sokal.pdf), [SIAM 2025 abstracts](https://www.siam.org/media/sare0ojk/an25_abstracts.pdf). A neighboring Riemann–Hilbert solution remark in that abstract collection belongs to a different talk and is not counted as a resolution of this conjecture.

## Applicability to the full G3/G4 tasks

The common-scope record remains authoritative: [shared scope](https://github.com/Sodelin/Research-Commons/blob/331f641cf4947317a64804df67ba00ab6668941c/research/2026-10-02-dot-shared-scope-0549z/SHARED-SCOPE.md).

**G4:** the paper's fixed graphon with all clique densities is a real all-prefix indistinguishability example in its own observation class. A countably infinite latent color system, arbitrary part weights and zero within-color edge probabilities are not an admitted finite positive biological source. Clique densities also discard mergers and full labelled forests. The literal relaxed club-to-merger proposal was exactly tested and fails at four roots; its separate independently checked packet is [the source-adapter diagnostic](https://github.com/Sodelin/Research-Commons/tree/69f12a77cb3535011533c2e06e2b48d123ababc6/research/2026-10-02-dot-graphon-source-adapter-0610z). This report does not revive that proposal.

The promising transfer from forcing theory is conditional: derive each needed graph-pattern statistic from a finite **legal full-forest observation menu**, uniformly over arbitrary unknown positive serial words, while preserving source IDs and one coherent source. Then apply an already proved forcing theorem. A hidden latent-color oracle, separate realization per row, repeated unknown box, or known hidden word-length bound is not that derivation. The newer substitution identities construct forcing graphs, but do not establish that biological observations measure their densities. Therefore they currently discharge no full G4 stopping obligation.

**G3:** q-step graphon forcing bounds concern observed density families and a supplied target complexity. They do not bound the length of an unknown positive serial word in a coupled source wrapper fiber. Full G3 still needs effective joint feasibility/parametric elimination, or an input-derived bound on one realizing source for the entire menu. Neither pointwise chain recognition nor generic finite-dimensional matrix factorization provides that missing source-faithful bound.

Thus no new full-master closure or general higher-cap obstruction is claimed. Further work should attempt the existing legal-observation/bounded-witness obligations; increasing the literature or cap count without a bridge is not a replacement.

## Reproducibility, scope limits and stopping record

- Exact DOI seed: W3124313441. Date filter: publication date≤2026-10-02. Official API, public read-only requests, no credentials. `direct-citers.json` retains raw response metadata, six records and null final cursor. The fetch script verifies every seed-ID edge.
- `QUERY-LOG.json` records exact request URLs. Its broad title-search result totals are unscreened search hits, **not included-paper counts**. Only selected exact-title matches entered the focus corpus.
- Explicit aliases: Cooley journal/conference/preprint; Lovász–Szegedy journal/preprint; Wang–Zhang journal/preprint; Kurtz duplicate index records. References are merged by these declared families, not by opportunistic title resemblance.
- `canonicalize.py` computes the 13-family/26-pair map. `verify_neighborhood.py` checks the saved counts, exact citation edges, alias policy and strongest coupling without network calls. Its receipt is included.
- Coverage is a complete dated first hop in **one seed record of one index**, all 24 primary backward bibliography entries, selected second-hop neighbors, and targeted primary/version searches. The missed September 2026 citer proves that this is not global completeness. No full union census of every scholarly index or every co-citation neighborhood was completed.
- Publisher citing-page and one article text encountered a Cloudflare challenge. They were left unresolved. API metadata and openly available primary papers are reported at their actual evidence levels.
- Source snapshots contain bibliographic metadata and our own summaries, not republications of complete papers. A compact metadata projection accompanies the raw first-hop response.
- This bounded deliverable closes the requested four-category audit at the declared scope. Its remaining gaps are explicitly identified; they are not filled by unlimited recursive citation chasing or assumptions of novelty.

