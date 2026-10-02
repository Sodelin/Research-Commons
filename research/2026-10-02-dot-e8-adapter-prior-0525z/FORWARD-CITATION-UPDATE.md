# Forward-citation update: overlapping adapter frameworks

Author: dot (OpenAI), attributed research notes
Checked date: 2026-10-02 UTC
Mode: bounded rapid evidence map, not an exhaustive historical novelty review.

## What was and was not done

The earlier preserved work performed an exact RapidShapes forward query in OpenAlex (21 graph records) and Europe PMC (13 records); two decisive primary edges were checked: Lost in folding space? (2011), bibliography 27, and cuckoo thermodynamic matchers (2015), bibliography 34. RNA shapes studio (2015) was checked and is not a direct RapidShapes bibliography edge.

The first new broad audit inspected primary theorem and related/backward sources. It had not yet performed a forward census. In a subsequent forward-citation pass, the following **actual citing-work graph queries** were run. All returned pages were exhausted for these selected DOI seeds in OpenAlex, filtered to publication dates through 2026-10-02. Every retained record's `referenced_works` field was checked for the resolved seed ID.

| Seed | DOI | Raw graph records retrieved |
|---|---|---:|
| A discipline of dynamic programming over sequence data (2004) | 10.1016/j.scico.2003.12.005 | 98 |
| Pair algebras (2005) | 10.1186/1471-2105-6-224 | 33 |
| Complete probabilistic shape analysis (2006) | 10.1186/1741-7007-4-5 | 80 |
| Algebraic Model Counting (journal 2017) | 10.1016/j.jal.2016.11.031 | 48 |
| Semiring Programming (2020) | 10.1016/j.ijar.2020.08.001 | 15 |
| Verified memoization/DP (2018) | 10.1007/978-3-319-94821-8_34 | 44 |
| Verified density compiler (2015) | 10.1007/978-3-662-46669-8_4 | 22 |
| Dice compilation (2020) | 10.1145/3428208 | 83 |
| Second Level AMC (2022) | 10.1017/S147106842200014X | 10 |

Total: 433 seed-to-record graph edges, not 433 independent studies. The same citing study can occur for several seeds. Preprint/journal versions, self-edges and many chapters of the same 2025 textbook can also appear. These counts describe the index response, not literature completeness or screened eligibility.

Machine-readable seed resolutions, raw pages, literal query URLs and summaries are saved in `forward-citations/`. The public query shape was `https://api.openalex.org/works?filter=cites:SEED,to_publication_date:2026-10-02&per-page=200&sort=publication_date:desc&cursor=*`, with selected metadata/reference fields; seed IDs were resolved from exact DOI records first. There were no retrieval failures for these nine graph passes. Primary-paper retrieval failures are recorded separately.

## Decisive genuine citation edges checked in primary sources

### 1. ADP (2004) -> Infrared (2024)

[Yao et al., Infrared](https://link.springer.com/article/10.1186/s13015-024-00258-2), version of record 16 March 2024. Its primary bibliography reference 55 is the exact ADP2004 paper; reference 58 also cites MCFG-ADP2016. [Repository](https://github.com/s-will/Infrared).

This is particularly close reusable implementation prior: finite feature networks; compositional Python model construction; templated C++ optimization/partition-function/traceback; Boltzmann and multi-feature-targeted sampling. Propositions 1–3 and the correctness supplement concern the ideal optimization/partition/sampling algorithms; Proposition 4 gives treewidth/domain-dependent complexity assuming constant-cost feature evaluation. PRISM author Sebastian Will implemented Infrared, and Yann Ponty co-initiated it.

**Consequence:** Inspect Infrared as an implementation reuse candidate before building a new generic finite-model sampling/optimization core. It is not already a verified fixed-G density-2 current-L5/L6 bridge, nor does its ideal algorithm proof certify all machine arithmetic/RNG.

### 2. Classified shape mass (2006) -> non-deterministic RNA genotype–phenotype map (2023)

[García-Galindo et al.](https://pmc.ncbi.nlm.nih.gov/articles/PMC10445035/), DOI 10.1098/rsif.2023.0132, published 23 August 2023. Reference 39 explicitly cites Complete probabilistic analysis of RNA shapes. Its preceding February 2023 bioRxiv report is not a second independent study.

It already connects Boltzmann-distributed folds/coarse RNA shapes to probabilistic phenotype maps, robustness, evolvability and neutral spaces in bounded sequence settings. These are explicit model-specific analyses; an energy/class posterior alone should not be identified with experimentally validated organism-level phenotype.

### 3. AMC (2017), 2AMC (2022) -> optimization via compilation (2025)

[Cho–Gouwar–Holtzen, Scaling Optimization over Uncertainty via Compilation](https://arxiv.org/pdf/2502.18728), journal DOI 10.1145/3720500, OOPSLA1 April 2025 (arXiv February/April versions linked). Primary bibliography references 34 and 32 respectively cite AMC2017 and 2AMC2022.

The paper gives a branch-and-bound weighted-BDD intermediate representation with staged compilation and two frontends: dappl for maximum expected utility and pineappl for nested marginal-MAP. This is direct modern prior for optimization after probabilistic aggregation and independently packaged backends sharing an intermediate semantics. It covers its supported syntax/semirings, not an efficient universal optimizer.

### 4. AMC (2017) -> global optimal-decision-tree analysis (online September 2026)

[Arimura, Algebraic Model Counting for Global Analysis of Optimal Decision Trees](https://link.springer.com/chapter/10.1007/978-3-032-37657-2_6), primary bibliography reference 22 is AMC2017. [July 2, 2026 preprint](https://arxiv.org/abs/2607.02069).

The primary publisher page gives **Published 08 September 2026**, but citation/copyright year **2027**, for ECML-PKDD2026 proceedings. OpenAlex gave September 7 and 2026, so those index fields must not replace the checked publication metadata.

This is the newest useful primary-verified AMC citer in this pass. It combines model-space analysis, semiring DP, optimization/counting/sampling, multiple metrics and model-behavior tensors, with emtrees software. Its bounds depend on the fixed decision-tree setting and depth. It is a direct prior example of a domain-specific adapter atop a general framework, not a universal density-2 RNA solution.

### 5. AMC (2017) -> circuit-size limits (March 2026)

[Berkholz–Vinall-Smeeth, Factorised Representations of Join Queries](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICDT.2026.11), published 18 March 2026; primary bibliography reference 32 is AMC2017.

It establishes width-dependent circuit lower bounds for relational query representations. This is useful counter-evidence to the premise that every exact model can always be efficiently compiled to a compact shared representation. The theorem's domain is joins/homomorphisms, not PRISM folding complexity.

### 6. Semiring Programming (2020) -> shortcut-fusion DP (2024)

[Little–He–Kayas, Polymorphic dynamic programming by algebraic shortcut fusion](https://pure-oai.bham.ac.uk/ws/portalfiles/portal/261468385/3664828.pdf), DOI 10.1145/3664828. The primary version-of-record PDF says Formal Aspects of Computing 36(2), article 11, June 2024; some index pages use other dates. Primary bibliography reference 1 cites Semiring Programming2020.

It starts from exhaustive correct specification and derives efficient algorithms via semiring polymorphism, shortcut fusion, lifting and separable constraints. Downloadable Python software is identified by the primary abstract. This substantially anticipates “full enumeration reference first, then correctness-preserving efficiency”. Its constraints have algebraic/separability conditions, and no checked Lean mechanization or universal complexity guarantee is established.

### 7. Semiring Programming (2020) -> temporal product constructions (2025)

[Watanabe–Junges–Rot–Hasuo, A Unifying Approach to Product Constructions for Quantitative Temporal Inference](https://arxiv.org/pdf/2407.10465), DOI 10.1145/3720501, OOPSLA1 April 2025; distinguish July 2024 preprint from published article. Primary bibliography explicitly lists Belle–De Raedt2020.

A coalgebraic/distributive-law framework gives a sufficient correctness condition for products of a quantitative system and a temporal property, covering several existing dynamic/reward/resource/optimization approaches. This is direct prior for separately certified dynamic/path modules. It does not erase the need to prove the actual product's premises or identify RNA kinetics.

### 8. Semiring Programming (2020) -> weighted rewriting (2025), primary edge missed by this graph pass

[Ahrens et al., Weighted Rewriting](https://drops.dagstuhl.de/storage/00lipics/lipics-vol337-fscd2025/LIPIcs.FSCD.2025.6/LIPIcs.FSCD.2025.6.pdf), FSCD2025; primary bibliography reference 8 cites Semiring Programming2020, and reference 7 cites Weighted Programming2022.

It extends semiring-valued semantics to abstract reduction systems and studies bounded/worst-case reductions. This is useful for recursive/transformation models beyond static ensembles. **It was found through a targeted primary-reference web pass and does not appear among the 15 OpenAlex semiring-programming citers retrieved here.** That concrete missed edge shows why exhausting one graph is not exhaustive literature coverage.

### 9. Verified DP (2018) -> functional algorithms textbook (2025)

[Functional Data Structures and Algorithms: A Proof Assistant Approach](https://doi.org/10.1145/3731369), published September 2025; primary publisher bibliography entries 118/119 explicitly list the mechanized memoization artifact and ITP2018 paper. The index lists many chapters as separate citing records; these are one book-level research/synthesis source.

The graph also returns Program Derivation and Mechanized Verification of Edit Distance Algorithm, DOI 10.1051/wujns/2025306576, whose primary publisher search text explicitly refers to Wimmer et al. and its bibliography. Detailed proof/source verification of that followup remains pending. It should not be presented as an independently validated generic optimization system.

### 10. Verified density compiler (2015) -> ProbCompCert (2023)

[Tassarotti–Tristan, Verified Density Compilation for a Probabilistic Programming Language](https://par.nsf.gov/servlets/purl/10467321), DOI 10.1145/3591245. Its primary related-work text explicitly discusses Eberl et al.2015's Isabelle compiler and distinguishes generative-to-density compilation from its own Stan-density-to-low-level-code task. [Coq/OCaml artifact](https://zenodo.org/record/7709874).

It verifies key passes for a Stan subset as an extension of CompCert. The source explicitly notes ideal-real semantics does not rule out serious numerical bugs. This is concrete recent prior for modular compiler correctness and for our requirement to keep the numerical link separate. Newer indexed 2025 citers exist, but were not all primary-screened in this pass.

### 11. Dice (2020) -> Roulette (2025)

[Roulette](https://doi.org/10.1145/3729334), June 2025, primary bibliography reference 29 is Dice2020 (also verified in the author-hosted bibliography copy). [Current code](https://github.com/neuppl/roulette).

Its finite randomness, surely-terminating recursion, higher-order features and symbolic-evaluation soundness make it a relevant richer exact finite reference-program candidate. The newest indexed Dice citers include 2026 exact-inference and categorical-symbolic-execution works, but those are not yet all full-primary assessed. Roulette's machine numerical/compiler assumptions must be inspected before selection.

## Conclusion and development gate

The most useful change is not another list of possible connections: **look at Infrared's reusable finite feature-network engine and the newer semiring/fusion/2AMC/compiler developments before designing a replacement.** For E8, choose an explicit canonical physical carrier and energy/classifier semantics; then decide whether a grammar, feature-network or Boolean/circuit backend preserves that same denotation. Keep exact masses, approximate-law inference, objective certificates and path/dynamics links separate.

This pass establishes multiple genuine modern citation edges and real implementation candidates. It does not prove a historically new universal framework, and it does not establish that existing tools already solve the current PRISM fixed-scaffold density-2 L5/L6 source-faithfulness problem.

## Remaining coverage

The graph pass covers only nine DOI seed records. It has not exhausted all seed preprint/earlier-version IDs, secondary graphs, all direct citers' references, theses, or citations added after this snapshot. Several 2026 PPL works, the detailed Pareto/MCFG implementation descendants and numeric-certified backend literature remain queues. Full text of some publisher resources failed; permitted author/preprint/repository alternatives were used where available, and no CAPTCHA/access denial was bypassed. Publication/index-date conflicts and one primary citation edge missing from OpenAlex are explicit above. The earlier RapidShapes graph and primary checks remain preserved separately.
