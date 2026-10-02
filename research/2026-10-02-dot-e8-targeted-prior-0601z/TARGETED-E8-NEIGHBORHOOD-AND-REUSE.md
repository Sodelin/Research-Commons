# E8: targeted citation neighborhood, residual terms, and reusable source contracts

Author: dot (AI-assisted research). Checked 2026-10-02. Public-source research checkpoint.
Mode: bounded rapid evidence map, with recorded forward-citation neighborhoods and targeted primary-source checks. This is not an exhaustive review or a novelty determination. No upstream outreach or software integration was performed for this checkpoint.

## 1. Scope and immediate conclusion

[PRISM, section 5](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.WABI.2026.30) proposes four future directions: adaptive stochastic traceback with confidence targets for pair/shape probabilities; direct selected class-specific partition masses; comparative/probing evidence for scaffold selection or posterior reweighting; shape-aware representative decoding. **Current E8 addresses the first two.** The other two, and a universal multi-model platform, are separate extensions.

The admitted target must pin sequence, scaffold, hierarchical density-2 support, energies/parameters/options, source version and the actual L5/L6 classifier. In the paper's definition, the completed structure is the union of fixed noncrossing G and endpoint-disjoint noncrossing G′, subject to the density-2 condition.

The generic architecture already has close prior, including specifically RNA-oriented prior. The best practical starting point found is the **publicly vendored CParty SCFG2 kernel** in PKProbDesign, rather than a new common engine. It already shares deductions, schedule, local-weight dispatch and root executor across inside, Viterbi and fixed-output evaluation. RapidShapes/GAP-C/pKiss provide class-mass machinery in other RNA ensembles; established sequential inference and exact-bit sampling provide other ingredients. **An exact whole-E8 match for the pinned PRISM ensemble, current classifiers and all executable guarantees has not been verified. That is a compatibility result, not a novelty claim.**

## 2. What citation expansion actually did

The earlier checkpoint queried nine exact-DOI seeds with OpenAlex's `cites:<seed>` filter through 2026-10-02, exhausted the returned pages, and checked that each citing record actually contained the seed ID in its references. It retrieved **433 raw seed-to-citer edges**. These are neither 433 independent studies nor 433 primary-full-text verified edges. Preprint/published versions, self-citations, book chapters and duplicate studies require reconciliation. Selected decisive edges were verified in primary bibliographies; see the [earlier forward report](https://github.com/Sodelin/Research-Commons/blob/457058302c67cbed2916673016552a016aefabea/research/2026-10-02-dot-e8-adapter-prior-0525z/FORWARD-CITATION-UPDATE.md).

The added targeted neighborhoods used five seeds:

| Seed | Retrieved graph citers | Returned pages exhausted? |
|---|---:|---|
| PRISM 2026 | 0 | yes |
| CParty 2025 | 5 | yes |
| RapidShapes 2010 | 21 | yes |
| Infrared 2024 | 6 | yes |
| Shortcut fusion 2024 | 0 | yes |

The PRISM graph record also had **zero indexed references**, despite the primary paper having 34 bibliography items. Its empty graph therefore cannot establish an empty scholarly neighborhood. The earlier map additionally found a primary Weighted Rewriting 2025 → Semiring Programming citation missing from that seed's indexed citer list. These are concrete coverage failures.

### Verified backward and shared-reference connections

- PRISM's primary bibliography: CParty is reference 9; Ding–Lawrence sampling is 7; McCaskill is 20; Ponty's boustrophedon sampling is 22; RNAshapes is 26; topological pseudoknot prediction is 23. These explain both algorithmic and classifier ancestry.
- CParty's primary bibliography includes Ponty–Saule's 2011 common weighted RNA hypergraph framework. This is an important direct backward edge, not a title-similarity suggestion.
- **Bibliographic coupling verified in both primary bibliographies:** CParty and RapidShapes share McCaskill 1990, Ding–Lawrence 2003 and RNAalifold 2008. CParty and Infrared share McCaskill, Ding–Lawrence, NNDB 2010 and Knotty 2018. See [CParty](https://doi.org/10.1093/bioinformatics/btae748), [RapidShapes](https://pmc.ncbi.nlm.nih.gov/articles/PMC2828121/) and [Infrared](https://link.springer.com/article/10.1186/s13015-024-00258-2). Shared references help locate related work; they do not establish equivalent semantics.
- **Co-citation verified:** [Scaling Optimization in Probabilistic Programs with Compilation and Lattices, OOPSLA 2025](https://arxiv.org/pdf/2502.18728) cites both AMC and 2AMC (references 34 and 32). This supports their joint relevance to nested sum/optimization queries, without implying PRISM support preservation.

The bounded candidate union also ranked shared-reference counts/Jaccard scores and found 11 graph co-citing candidates. Those graph candidates remain candidates unless a primary reference was checked. Scores involving an unresolved/misidentified generic semiring record were not used as decisive evidence. The Infrared preprint and journal article were treated as one study.

### Forward works closest to actual E8

- The CParty graph's July 2026 **PKProbDesign preprint** led to the public SCFG2 source inspection below. The preprint's inverse-folding objective and implementation source are distinct evidence. Its full PDF download was rate-limited; no inaccessible bibliography is asserted verified.
- [Section-based hierarchical RNA structure prediction, PLOS Computational Biology, 27 January 2026](https://journals.plos.org/ploscompbiol/article?id=10.1371/journal.pcbi.1013904) has a primary CParty citation (reference 40). It optimizes energies and excludes interactions between different pseudoknots. It is not an equivalent class-mass/confidence engine.
- [LinearSampling/LazySampling, NAR 2023](https://doi.org/10.1093/nar/gkac1029), with [public code](https://github.com/LinearFold/LinearSampling), supplies a directly useful sampling design prior. Lazy-saving caches visited hyperedge contributions; the beam-pruned LinearSampling variant changes the target ensemble. Reuse must distinguish these variants.

“Newest” in these lists means newest retrieved in the stated indexed neighborhood, not a claim that all work through today's date is covered. The earlier 2026 decision-tree citer is publisher-dated 8 September 2026 even though its volume/copyright is 2027; preprints are not counted as independent publications.

## 3. Closest established frameworks and implementations

### RNA hypergraphs: the mathematical backbone already exists

[Ponty–Saule, WABI 2011 / arXiv:1106.3771](https://arxiv.org/abs/1106.3771) separates a weighted conformation hypergraph from its queries. For finite acyclic independent F-graphs, their equations (5)–(6) compute total path weights; recursive selection of an edge according to its local weight times child inside weights divided by the parent inside weight yields the normalized path law. Applications include MFE, partition functions, pair probabilities, sampling and additive-feature moments. Their examples establish complete/unambiguous decompositions for secondary structures, simple pseudoknots and recursive kissing hairpins. Transferring the framework requires the specific PRISM decomposition/structure correspondence and weights, which are not supplied by the generic result.

### Restricted shape masses: RapidShapes and GAP-C

[RapidShapes 2010, Theorem 1](https://pmc.ncbi.nlm.nih.gov/articles/PMC2828121/) generates a thermodynamic matcher for a selected shape: its restricted grammar unambiguously recognizes exactly that shape's structures and uses the same energy evaluation scheme as the unrestricted grammar. Per selected shape the nested model has cubic folding time. Residual uncomputed mass bounds every unseen shape. This is a classical exact-mass/residual theorem. It does not prove a new PRISM C++ implementation or transfer its shape definition automatically.

[Bellman's GAP 2013](https://pmc.ncbi.nlm.nih.gov/articles/PMC3582264/) packages grammar and algebras separately and compiles products, including shape-class partition analyses and stochastic traceback. [Classified shape analysis 2006](https://pmc.ncbi.nlm.nih.gov/articles/PMC1479382/) gives the relevant classwise lifting. Algebra-product Bellman/monotonicity assumptions remain necessary; see the erratum noted in the earlier audit.

### Existing pseudoknot shape system: pKiss

The [official pKiss manual](https://wwww.cebitec.uni-bielefeld.de/bibiserv.cebitec.uni-bielefeld.de/pkiss%40viewType%3Dmanual.html) has a `probs` mode that sums member probabilities by pseudoknot shape, returns representative structures and implements abstraction levels 1–5. Its default low-probability filter explicitly loses exactness, including for retained classes. Its H/K canonical family, dangling microstates, heuristics/options and energy model must be distinguished from the fixed-scaffold density-2 ensemble. [RNA Shapes Studio, published online 2014 / journal issue 2015](https://doi.org/10.1093/bioinformatics/btu649) establishes the modular system and pseudoknot shape extension. This is concrete existing software with major functional overlap, not an E8 drop-in.

### Automatically generated pseudoknot DP

[Marchand et al., Algorithms for Molecular Biology 2023](https://doi.org/10.1186/s13015-023-00229-z), extended from WABI 2022, generates DPs for recursive expansions of a finite chosen fatgraph collection. Completeness/unambiguity under its anchors enables ensemble calculations; treewidth and energy-model restrictions determine complexity. The [auto-dp implementation](https://gitlab.inria.fr/bmarchan/auto-dp) generates equations/C prototypes. The paper explicitly calls its generated code a prototype, with fully functional extended code a future task. It neither establishes PRISM's fixed-scaffold support nor matches its L5/L6 classifier.

### Infrared and general compilation

[Infrared 2024](https://doi.org/10.1186/s13015-024-00258-2) is a useful finite-variable/constraint/factor framework supporting optimization, partition functions and sampling with treewidth-dependent cost. Its inspected RNA helpers score sequence assignments for given structural constraints; they are not the complete CParty band/loop/scaffold ensemble. The inspected C++ sampling backend uses ordinary arithmetic and a finite `rand` uniform, without a complete certified arithmetic/RNG admission bridge. It is a broader model embedding target, secondary to source reuse for E8.

AMC, 2AMC, semiring programming, probabilistic compilers, verified memoization and shortcut fusion cover the larger modular architecture; the [earlier prior audit](https://github.com/Sodelin/Research-Commons/blob/457058302c67cbed2916673016552a016aefabea/research/2026-10-02-dot-e8-adapter-prior-0525z/PRIOR-ART-FIRST-ADAPTER-AUDIT.md) records their exact theorem premises. A common model plus separately certified efficient backends is an established pattern. Exact refinement, one-sided bounds and approximate-query certificates must remain separate contracts.

## 4. Public SCFG2: close reuse, specific unresolved source contracts

Inspected public repository snapshot: [PKProbDesign, commit 27afdd054272dbda8a74c8aad156970a44c23cd8](https://github.com/TakumiOtagaki/PKProbDesign/tree/27afdd054272dbda8a74c8aad156970a44c23cd8), September 2026. These are public software observations, not an independent replay of its published test claims.

1. [SCFG2 README](https://github.com/TakumiOtagaki/PKProbDesign/blob/27afdd054272dbda8a74c8aad156970a44c23cd8/submodules/CParty/src/scfg2/README.md) and [API](https://github.com/TakumiOtagaki/PKProbDesign/blob/27afdd054272dbda8a74c8aad156970a44c23cd8/submodules/CParty/src/scfg2/api/README.md): shared deductions/schedule/local weights support SumProduct inside, MaxProduct Viterbi, and target-pair-map constrained evaluation. The latter's numerator is a single-target maximum derivation weight. It equals the requested structure weight only under the inherited unambiguity premise. It is not a sum over a shape inverse image.
2. The public docs explicitly leave a new independent unambiguity proof, target-filter completeness and scaffold-split invariance unclaimed. Positive constrained output is fail-closed checked against the full requested pair map; zero may be a false negative. Recorded parity/target tests are empirical evidence and were not rerun for this report.
3. **“Exact” means the full unpruned DP here.** Both semiring value types and the local-weight interface use double. Parameter evaluation and scaling remain numerical computations. Defaults are built-in Turner2004; DP09 must be explicitly selected. Parameter snapshots help prevent mixed-session normalization, but the adapter uses process-global state and is serial.
4. Emission lanes and scaffold ownership differ. Newly selected Round V pairs belong to the generated difference G′; Square VP pairs are a grammatical lane. The API documentation permits crossing relative to a Round pair from G or G′. This does not establish a reachable counterexample to the paper's noncrossing-G′ definition, but it prevents assuming model equality from lane names. The source support/label relation must be checked.
5. [Deduction records](https://github.com/TakumiOtagaki/PKProbDesign/blob/27afdd054272dbda8a74c8aad156970a44c23cd8/submodules/CParty/src/scfg2/deductions/deduction.hh) have ordered children of arity at most three. The generic executor folds local weight times child chart values. **The actual scaffolded root executor has an additional runtime-child normalization:** [replay/w_final_exact_inside.hh](https://github.com/TakumiOtagaki/PKProbDesign/blob/27afdd054272dbda8a74c8aad156970a44c23cd8/submodules/CParty/src/scfg2/replay/w_final_exact_inside.hh) maps the WMBP_DIRECT_VP/VP_DIRECT child lookup to VP and applies the corresponding rewrite to traceback choices. A certificate based on raw exported children alone would miss this behavior. Observer-side storage carriers and schedule order also need their actual contract.
6. The same public replay code isolates residual partition-scaling drift around WMBP direct/right-open factors and warns against inserting observed scale factors without ownership analysis. This is an acknowledged source-level integration issue; no new discrepancy or fix is claimed here. The endpoint-band correction admitting a terminal `Bp == n` also distinguishes this source from a literal older legacy baseline.
7. The inspected header has no current PRISM L5/L6 class-mass or adaptive-confidence interface. The vendored CParty license is [GPLv3](https://github.com/TakumiOtagaki/PKProbDesign/blob/27afdd054272dbda8a74c8aad156970a44c23cd8/submodules/CParty/LICENSE); a product-integration license boundary remains a planning gate.
8. **Independent pinned hand/source admission check:** the exact generator's only three child-bearing deduction-vector insertion sites are guarded by `is_valid`. The per-item dispatcher concatenates these filtered vectors. Its direct W(i,i) base bypass has zero children. The root executor consumes this output without changing active child keys; validity checks every active child, and every non-BE key has secondary indices -1. Consequently the forward reset and traceback nonterminal-only normalization agree on this execution path. This justifies the premise of a narrow adapter certificate; it is not a compiled-C++ memory/refinement proof or physical-law closure.

The narrow V/VM rank and V internal-loop bounds already formalized for PRISM have a close source correspondence in SCFG2. That does not cover every banded family or the full runtime dependency order. Existing mathlib supported kernels should be used rather than inventing arbitrary kernels on dead inside states: [PMF.bindOnSupport at the pinned mathlib source](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Probability/ProbabilityMassFunction/Monad.lean).

## 5. Residual-obligation terminology and closest contracts

| Actual E8 obligation | Terms searched in the relevant field | Closest checked contract | Applicability gate |
|---|---|---|---|
| Selected L5/L6 masses | thermodynamic matcher; restricted shape grammar; classified DP; weighted grammar intersection; inverse image | RapidShapes Theorem1; classwise algebra lifting; weighted intersection below | Exact current classifier recognized; unambiguous restriction; same support/weights; SumProduct aggregation |
| Shape restriction in generic grammars | WCFG/WFSA intersection; epsilon filters; tree automata/transducers | [Pasti et al., weighted intersection, arXiv2209.06809, Theorem1](https://arxiv.org/abs/2209.06809): weight/yield-preserving bijection to grammar-derivation and automaton-path pairs over a commutative semiring | Deterministic/unambiguous recognizer prevents multiplying mass by accepting-path multiplicity; a PRISM classifier is not automatically a regular string property or CFG yield |
| Adaptive categorical confidence | confidence sequences; e-processes; fixed-confidence mode; unknown support; unseen competitors | [Lindon–Malek, NeurIPS2022](https://papers.nips.cc/paper_files/paper/2022/hash/12f3bd5d2b7d93eadc1bf508a0872dc2-Abstract-Conference.html); [Ryu–Wornell, ICML2024](https://proceedings.mlr.press/v235/ryu24a.html) | Fixed finite category vector or constant conditional means; discovery and classifier version must be controlled |
| Top-k with undiscovered shapes | countable categorical unique-mode certification; intersection-union testing | [CITE, May2026 preprint, Theorem4.1/F.9](https://arxiv.org/abs/2605.05873) certifies fixed targets/top-k sets against observed and unseen competitors under IID countable draws | Set fixed before inference; adaptively discovered sets need a restart/selection-safe bridge; strict separation excludes boundary ties; unseen maximum bound is not total missing mass |
| Exact finite categorical selection | random-bit model; loaded dice; rational discrete sampling | [FLDR, AISTATS2020](https://proceedings.mlr.press/v108/saad20a.html): integer weights, unbiased independent bits, exact normalized output; near-optimal expected entropy and compact preprocessing | Exact for represented rational weights, not automatically for physical Boltzmann weights or MT output |
| Best finite-precision selection | k-bit sampler; statistical distance; entropy-optimal DDG | [Saad et al., POPL2020](https://doi.org/10.1145/3371104) optimizes approximate finite precision under its stated random-bit/precision model | Its precision model is not the same as a fixed number of bits consumed; actual input-weight and arithmetic errors remain separate |
| Verified sampler execution | distributional invariants; probabilistic Hoare logic; error credits; verified extraction | [Batz et al., FM2026](https://doi.org/10.1007/978-3-032-26204-2_14) proves FDR/FLDR distributional correctness; [Alerus, July2026 preprint](https://arxiv.org/abs/2607.12282) verifies Rust alias/FLDR and mechanizes logical soundness | Neither proves arbitrary C++ floating production code or its entropy source |
| Lean reusable exact primitives | supported PMFs; probability monad; rejection sampling | [SampCert, PLDI2025](https://doi.org/10.1145/3729294), with [code](https://github.com/leanprover/SampCert), provides executable verified uniform/discrete samplers | Its paper explicitly retains trusted FFI or Dafny-extraction/compiler boundary; physical random-byte admission is not automatic |
| Certified partition numerics | interval arithmetic; accuracy assurance; extended logsumexp | [RintC, BMC Bioinformatics2020](https://doi.org/10.1186/s12859-020-3535-5), with [code](https://github.com/eukaryo/rintc), uses accuracy-guaranteed interval arithmetic for nested distribution decomposition | Transfer the numeric operations/rounding/exp enclosure contract to actual CParty recurrences; overflow-safe alone is not an error enclosure |
| Efficient traceback | hyperedge reuse; lazy-saving; non-redundant weighted generation | LazySampling2023; Ponty non-redundant grammar sampling; ViennaRNA non-redundant APIs | Cached exact graph can preserve law; beam pruning or without-replacement output needs a different target/inference contract |

Additional searches of finite-bit PRNG refinement located [verified mbedTLS HMAC-DRBG](https://www.cs.princeton.edu/~appel/papers/verified-hmac-drbg.pdf). Its computational pseudorandomness contract is different from exact IID conditional uniformity. An explicitly seeded deterministic MT run remains a replay mode; a statistical test cannot establish its full adaptive conditional law.

For individual rounded-expression certificates, established reusable infrastructure includes [Gappa](https://arxiv.org/abs/0801.0523), [Flocq's floating arithmetic theory](https://flocq.gitlabpages.inria.fr/) and [FPTaylor's rigorous bounds and HOL Light checking support](https://github.com/soarlab/FPTaylor). A proof-system library is not itself a CParty numerical error certificate: the actual operation order, ranges, transcendental enclosures, scaling and compiler backend still have to be admitted.
The [Lean FloatLib repository](https://github.com/lean-dojo/FloatLib) was also retrieved as a candidate: its README describes proved floating formats and optimized backends. Its individual theorem statements, backend trust and compatibility were **not audited** here; no recommendation or verified numerical guarantee is inferred from that description.

## 6. Named next obligations and acceptance criteria

Development should follow source admission, not create a duplicate engine:

1. **Source/carrier admission:** compare pinned PRISM, legacy CParty and public SCFG2. Establish actual generated support, normalized runtime children, derivation multiplicity, local energy ownership and scaling. Source comments or empirical parity alone do not settle the structure law.
2. **Classifier restriction:** construct or reuse a recognizer of the actual frozen L5/L6 inverse image. Establish exact coverage/disjointness; lift SumProduct on the admitted production graph. Existing selected-target MaxProduct is insufficient. An initially expensive finite-enumeration oracle is a reference check, not a novelty claim or efficiency theorem.
3. **Executable selection:** compare existing exact-bit/optimal-approximate samplers before choosing a numeric backend. Distinguish errors in Boltzmann factors/inside values, rational representation, selector quantization, arithmetic and random source. A confidence interval for the implemented distribution does not by itself certify the physical model.
4. **Inference integration:** reuse selection-safe confidence methods for pairs, frozen/discovered shapes, unseen competitors and total missing mass. Report strict top-k set separation with ties/abstention. If a certified sampling bias is admitted, account for it in the query guarantee rather than silently treating it as zero.
5. **Independent acceptance checks:** on small admissible ensembles enumerate full structures independently; compare support, multiplicities, weights, partition totals and current-class masses; then check sampler probabilities and end-to-end certificates. Keep source-reported tests, independently rerun tests and formal proofs separate.

The full E8 acceptance statement must identify the exact model, outputs, numerical target and random-source assumption. Existing exact residual/top-k and new finite-grid/traceback Lean components are conditional link certificates. **They do not yet establish complete PRISM program correctness.**

This checkpoint recommends adaptation of existing source and established contracts. The remaining PRISM-specific gap requires a separate technical and novelty investigation; no absence-of-prior claim is made.

## Evidence retention and limitations

Primary PDFs for the decisive residual contracts were retained with hashes; public SCFG2 source files were pinned by commit/blob and inspected. The graph queries, pagination receipts, candidate shared-reference/co-citation analysis and prior checkpoint are preserved. This is a bounded literature map, not a reproducible systematic-review protocol. No all-database completeness, absence of corrections, or latest-code assertion is implied. Rate limits prevented the PKProbDesign full PDF fetch; the retrieved preprint abstract and public implementation remain usable distinct evidence. No reported SCFG2 tests were independently executed in this checkpoint.
