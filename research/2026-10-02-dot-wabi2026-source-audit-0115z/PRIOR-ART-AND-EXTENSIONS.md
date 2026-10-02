# WABI 2026: bounded prior-art and extension audit

Prepared by dot, 2 October 2026. Primary-source rapid evidence map for the G/HG/Bio1/Alt-G program. This is a source and assumption audit, not a new theorem, simulation, benchmark, or global novelty determination.

## Result and coverage

All **31/31 research articles** in [LIPIcs volume 390, WABI 2026](https://doi.org/10.4230/LIPIcs.WABI.2026) were inventoried by official title and abstract; their official PDFs were retrieved. Front matter is excluded. Articles 22 and 31 are extended abstracts and should not receive the proof-depth confidence of a full paper.

Full-text inspection was deliberately uneven:

- **8 primary deep audits:** 1, 10, 11, 16, 20, 23, 25, 29. Relevant theorem/model sections, assumptions, limitations, and concluding directions were inspected
- **10 focused follow-up inspections:** 3, 4, 8, 12, 15, 17, 19, 21, 30, 31. Relevant result/limitation/discussion passages were inspected; this is not a claim of full proof revalidation
- **13 title/abstract and software-header screens:** 2, 5, 6, 7, 9, 13, 14, 18, 22, 24, 26, 27, 28. Precise theorem claims from these papers are not admitted beyond their inspected abstracts

The audit retains **9 locally deduplicated core extension families**. **One is an already cataloged Bio1 direction**, sharpened here, and **8 are additional candidates relative to that catalog**. Among the eight additions, **7 have an explicit author-stated unresolved direction** and **1 is a project-generated adaptation target**. This is a bounded program-queue count, not the number of all open questions in WABI, not eight globally novel conjectures, and not an exhaustive novelty promise. **Zero globally unique new conjectures are established by this audit.** Three additional author-stated questions are placed in reserve, outside that core count.

The prior Bio1 catalog was checked directly: [BIOLOGICAL.md](https://github.com/Sodelin/Cross-Scale-Causal-Formalization/blob/main/research/open-problem-catalogs-2026-09-30/BIOLOGICAL.md), file blob 41f92ca6c0c2d09ebabaa574b2b2052064e7b298. NetCS and its sparse-query/statistical-bridge direction were already present. “Additional” here means absent from that inspected catalog and the supplied program comparison, not absent from every past conversation or repository.

## Program contracts that prevent false transfers

G1 is contextual source replacement retaining forests, histories and shared registers. G2 is same-source forward/compiler projection with live ancestors. G3's accepted capped-Poisson attainment through six and true closure-boundary algebraic obstruction from seven do not close finite common-source recognition. G4's accepted sharp-six branch recovers two unknown pads around a supplied known positive independent bigon; arbitrary unknown-box/multicell full-kernel stopping remains distinct. G5/HG1 recover the displayed rooted cluster union/S from exact rooted calendar-law panels on positive temporal cut-child sources, with M3 sufficient for binary sources and M_(k+1) sufficient under indegree at most k. These are not finite-DNA results, optimal-panel claims, or quartets-only concordance-factor theorems.

G6 concerns honest finite-data certificates/abstention; G7 concerns exact design over a declared menu and cost; Bio1 requires an observation-provider contract, adaptive recovery and error composition. Alt-G transfers must preserve source, observation, action and target. The proposed third-level picker should initially be a method/measurement selector with explicit applicability and calibration gates. No paper below identifies RNA Potts interactions, tumor perfect phylogeny, variation-graph homology and NMSC ancestry as the same latent process.

No inspected WABI result refutes the accepted exact G1–G5/HG1 statements under their supplied contracts. The strongest challenges concern **how empirical providers are optimized, calibrated and composed**, not those exact-law theorems. No paper inspected closes G3's common-source finite recognition or G4's unrestricted all-copy stopping.

## Eight primary evidence audits

### 1. NetCS: reuse the solved conditional problem; move effort upstream

[Dai and Molloy, article 1](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.WABI.2026.1), especially §3, Corollary 1, §3.4 and §5.

The input includes the tree of blobs and unrooted binary gene trees. The output is a binary semidirected level-1 network; the stated procedure reconstructs nontrivial blobs of **degree at least five**. Lemma 1 assumes NMSC gene trees sampled independently on the species set, with the inherited quartet-test assumptions. In particular, T3 requires class-1 quartet-nonanomalousness: common inheritance satisfies the noted condition, independent inheritance need not. Distinct expected quartet concordance factors on 4-blob restrictions are also part of the classifier contract.

Corollary 1 gives statistical consistency, fast-mode O(n log(n) k) time and O(n log n) queried four-taxon sets; the slower analytical version is O(n² log(n) k). Fast mode operates where quartet errors are below its tolerance and quarnets are reconstructed perfectly. The actual robustness-oriented implementation tests all candidate pivots and is O(n³ log(n) k), as §3.4 and §5 explicitly say. Do not report that implementation as universally O(n log(n) k).

The conclusion confirms the practical bottleneck: estimated tree-of-blobs error substantially degrades both NetCS and NANUQ+, even though conditional blob reconstruction is fast and accurate. Independently inferred hybrids may also be mutually incompatible; the implementation resolves candidates greedily and may fail to produce the whole network (§3.4).

**Reuse:** NetCS's conditional method, sparse-query lower-bound comparison and actual simulations already belong to Bio1. **Surviving target:** a finite-sample provider/recovery composition that includes tree-of-blobs uncertainty, quartet estimation error, shared-gene dependence, missingness and hybrid compatibility. This is a sharpening of existing Bio1, not a newly counted question. **Drop:** another claim that sparse known-TOB level-1 reconstruction is new. G5's rooted calendar observation and arbitrary-level cut-child source are different contracts.

Software: [TREE-QMC](https://github.com/molloy-lab/TREE-QMC), [study scripts/data](https://github.com/junyandai/netcs-study), with archived source identifiers in the official paper. No software was run here.

### 20. Turnpike: exact assignment certificates under an explicit separation regime

[Elder, Marçais and Kingsford, article 20](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.WABI.2026.20), Lemma 6, Proposition 10, Theorem 15, §3.7, limitations on p. 20:3 and §5.

The problem is linear one-dimensional point reconstruction from a complete unlabeled multiset of positive pairwise distances, up to translation/reflection. Lemma 6 and Proposition 10 characterize exact realizability by an assignment/multi-matching satisfying triangle equalities. An integral assignment is a realizability witness. Fractional LP feasibility by itself is not an exact point reconstruction or unique-source certificate.

Let η=ε+R/2. Theorem 15 assumes **2η < sep_y and 6η < gap_star**, where sep_y is the minimum separation between distinct true distance values, and gap_star is the minimum nonzero true additive-relation residual. At threshold gap_star/2 it recovers the multiplicity-qualified two-partition relation. Read this as the paper's matched rounded-representative/multiplicity contract; it does not automatically certify arbitrary preprocessing of repeated independently perturbed observations. The authors explicitly exclude missing/duplicated measurements and identify the true, unobserved gaps as a limitation. They give data-driven calibration, but that is not a proof that an observed feasible solution establishes the truth-level separation premises.

The bounded-noise theorem preserves the combinatorial input. It does not remove Turnpike ambiguity or prove a polynomial-time noisy solver. The paper records strong NP-hardness for noisy variants. O(n⁶) triangle variables constrain scale. Circular Beltway experiments are related-variant evidence, not covered by this linear theorem.

**Reuse:** assignment-first, regression-second architecture; exact certificate/heuristic distinction; separated relation recovery. **New candidate A:** an observable, sound certificate-or-abstain contract that does not simply assume access to unknown true gaps, with explicit handling of multiplicities. This is a project-generated G6/Alt-G target requiring its own closest-prior comparison. **New candidate B:** characterize triangle-LP integrality (author-explicit open direction, §5). Sparse/basis/separation enforcement is a practical companion, not an extra conjecture counted here.

Full version: [arXiv:2603.18283](https://arxiv.org/abs/2603.18283). No code repository is declared in the inspected proceedings PDF; do not presume a ready implementation from the experimental section.

### 23. Exact optimization can converge confidently to the wrong tree

[Satas, Myers and Shah, article 23](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.WABI.2026.23), §2, Theorem 7, Lemmas 9–10, Proposition 12 and §5.

Source: a rooted binary perfect-phylogeny tree with a trunk edge, positive edge probabilities summing to one; each mutation independently chooses an edge and is inherited by its descendants. Observation errors independently flip entries with false-negative α and false-positive β, both in (0,0.5). MFCP hard-assigns every observed mutation to one tree edge and minimizes positive weighted flip costs.

**Theorem 7:** for every positive weight pair and every such α,β, there exist a true tree and edge distribution for which the objective is not Fisher consistent. Lemma 9 gives a strict three-leaf counterexample. Lemma 10 extends to an NNI-neighbor pair, with an assignment of the two roles; its exact quantifier should not be replaced by “every fixed tree is wrong at every parameter.” Proposition 12 proves positive misleadingness for some instance: more mutations lead to a unique incorrect tree. This is not merely optimizer failure.

Remark 4 explains that jointly maximizing likelihood over trees **and hard mutation assignments** under this uniform error model falls in the same weighted-flip family. It is not repaired simply by renaming the objective “maximum likelihood.” The authors only speculate about marginalizing assignments/edge lengths as an alternative; they do not prove that every marginal approach is consistent.

**Reuse/challenge:** introduce a separate objective-calibration/Fisher-consistency gate in Bio1/G6 and the method selector. Solver optimality, likelihood-model fit, latent identifiability and statistical consistency must have separate outputs. **New candidate:** a computationally practical consistent provider under a specified generative/error model, with conditions identifying when the hard-assignment bias matters; §5 explicitly leaves this open. The amount of optimum-to-truth topological displacement and real-data consequences are related secondary questions, not counted again.

Software: [phylo_inconsistency](https://github.com/shahcompbio/phylo_inconsistency), public repository verified through the connected GitHub read API. This code is a falsification/control resource, not a consistency certificate.

### 25. Optimal pairwise incompatibility construction is solved; many-tree construction is open

[Lafond, article 25](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.WABI.2026.25), definitions in §2, Theorem 6, Propositions 8–9, §3.5 and §5.

Input rooted trees may be **nonbinary**, but contain no unary internal vertices; leaves are labeled. Theorem 6 constructs their cluster-incompatibility graph in **O(n+d)** time without knowing d beforehand, where d is output edges. §3.3 extends to unrooted splits; §3.4 handles unequal leaf sets using an explicit augmentation. These extensions are already solved. The graph represents conflicts between tree clusters/splits; it does not prove which conflicts reflect hybridization rather than ILS/noise.

For k trees, applying the pairwise algorithm gives **O(k²n+d)**. The authors explicitly ask for **O(nk+d)** or a proof that it cannot be achieved. Only pairs averaging o(n) incompatibility edges need an improved bound; if d=Ω(k²n), pairwise processing is already output-optimal. The complexity target is much more precise than “faster network inference.”

**Reuse:** an immediate Bio1/HG structural conflict oracle and provenance-preserving diagnostic backend, after the output tree/cluster contract is matched. **New candidate:** the author-stated k-tree optimal-output-sensitive question. Expected conflict density under ILS/hybridization is a separate reserve direction, not counted as part of a proved probabilistic guarantee. **Drop:** inventing a new pair-tree graph builder or claiming output edges identify a causal mechanism.

Software: [incompa-tree](https://github.com/manuellafond/incompa-tree). Public repository and README verified. C++/CMake; Newick trees in, relabeled trees and per-pair edge lists out. It already accepts a file of multiple trees by enumerating pairs; that is not the open O(nk+d) solution. README blob 0ee3338a9cdeed41a9b2676945e5f99a58854a1e. No compilation/execution here.

### 10. Tumor pruning: reusable lower bounds, with an objective-truth firewall

[Luque et al., article 10](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.WABI.2026.10), §2, Lemma 3/Corollary 4, Theorems 5 and 11, §§4.5–4.7 and §6.

The formal data model assumes false negatives only and optimizes 0→1 flips to a perfect phylogeny. It also empirically stress-tests low false-positive noise; that experiment does not widen the formal optimality model.

The incompatibility graph on zero entries encodes initial conflicts. Lemma 3/Corollary 4 relate its minimum vertex cover to the minimum number of flips resolving those **initial** conflicts. New conflicts may arise after flips, so OPT_init is not OPT. Theorem 5's polynomial-time lower bounds satisfy OPT_init/2 ≤ L ≤ OPT_init and remain useful where earlier matching bounds can be arbitrarily weak. Theorem 11 gives L1 ≤ L2 ≤ OPT for an extended LP and shows examples where L2 exceeds OPT_init. The theoretically stronger LP is not invariably faster; the paper's experiments favor a lighter bound in relevant regimes.

**Reuse:** admissible lower-bound interfaces, LP reuse across branch nodes and hybrid solver selection in G7/Alt-G. The bounds cannot be transplanted to G3/G4 without a proved conflict-graph reduction. **Challenge:** article 23 separates global objective optimality from true-ancestry consistency. It does **not** refute these pruning theorems; its main theorem requires β>0, unlike article 10's β=0 formal model. Stronger dynamic-conflict pruning and correlated/adversarial-noise benchmarks are author directions, merged into the broader objective/provider lane rather than counted as new independent conjectures.

Software: [faster-tphyl-reconstruction](https://github.com/jdluque/faster-tphyl-reconstruction); public repository and README verified. Python 3.10, pybnb/Cython and LP options including open-source OR-Tools PDLP and Gurobi. README blob 754e4f6b142db18680a2b9f2980a0ad1dcae392f. Exact input/output and runtime suitability still need a bounded future pilot.

### 11. RNA sparsity becomes useful through treewidth, not an ancestry claim

[Gardelle, Bulteau and Ponty, article 11](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.WABI.2026.11), Theorems 1–2, Corollary 3, §4.1 and §5.

This is edge-activated DCA/Potts generative modeling of aligned RNA columns, not NMSC lineage routing. Theorem 1 learns the greedy maximum-likelihood model after T steps in O(nN² + tw² 5^tw N² T + T C(tw;N)), using the coupling graph's treewidth. Theorem 2 samples its Boltzmann distribution in O(tw² 5^tw N) given a tree decomposition. Low treewidth is an empirical property of the examined models, not guaranteed for arbitrary RNA families or a consequence of sparsity alone.

The 41 tested RFAM families were selected using alignment-length, sequence-count, divergence, consensus-status and paired-position conditions (§4). Thus “all RNA evolution is now FPT in practice” is not supported. §4.1 explicitly leaves a well-calibrated stopping criterion open, because activated couplings can include direct base pairing, neighborhood relationships and negative selective pressure; counting every non-consensus contact as an error is not an appropriate target definition. §5 proposes non-greedy coupling choices.

**Reuse:** exact bounded-treewidth marginal/normalization/sampling backend, after an Alt-G source/observation adapter is specified. **New candidate:** a calibrated stopping/abstention criterion for a declared coupling target under the fitted model, with width and cost accounted for. This connects G6/G7 to a concrete biological model. Exact DP learning/sampling itself is already done.

Software/data: [eaDCAstar](https://codeberg.org/samuel-gardelle/wabi26-eaDCAstar), with an archived snapshot named in the official paper. No installation or source implementation verification here.

### 16. DivQuant: promising uncertainty estimates are explicitly heuristic

[Schmitz and Rahmann, article 16](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.WABI.2026.16), §§2.3–2.6, especially §2.4.2, and §4.

DivQuant extrapolates a population fingerprint from a small sample with a known sampling fraction/population size. It uses a convex quadratic Neyman-χ² objective and test inversion for richness intervals, plus entropy estimation from the recovered fingerprint. The rare/abundant split improves tractability.

The decisive source qualifier is §2.4.2: small expected counts, replacing Pearson's statistic by Neyman's for convexity, and flexible fingerprint-bin choice weaken the χ² derivation. The authors explicitly call interval construction **heuristic rather than fully derived asymptotic procedure**. Near-nominal empirical coverage across tested distributions is valuable evidence, not a nonasymptotic coverage theorem. §4 identifies a homogeneous-distribution corner case with essentially one informative bin, and says N must be known; plausible-N sweeps are a practical proposal, not a proved nuisance-robust confidence procedure.

**Reuse:** an uncertainty-aware richness/entropy provider and a counterexample to equating optimization plus nominal intervals with a G6 certificate. **New candidate:** rigorous coverage/abstention under a declared sampling model, including the concentrated-fingerprint and population-size assumptions. The authors explicitly seek tighter statistical analysis and entropy interval accuracy. An open-source QP-backend port is a practical implementation option, not another conjecture.

Software: [DivQuant](https://gitlab.com/rahmannlab/divquant), paper-pinned commit 2baab79d; Snakemake workflows. The paper uses the Python Gurobi API/free academic license. Do not assume that a commercial Gurobi license or an equivalent verified open-source backend is already available.

### 29. Homology relations give a canonical observable quotient

[Lisiecka, Cicherski and Dojer, article 29](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.WABI.2026.29), §§2.2–2.5, Theorems 1–2 and 4–6, §4.

The source is a bidirected variation-graph representation of a fixed collection of genomic sequences, with orientation/reverse-complement semantics and all adjacency induced by its represented genomic paths. Two representations are equivalent when they induce the same **nucleotide-position homology relation**. This is representation-dependent; the paper explicitly distinguishes it from guaranteed evolutionary homology.

Theorems 1 and 2 give unique, up-to-isomorphism singular and compact representatives in each homology-equivalence class. Safe unitig compression preserves the relation. Proposition 3's Jaccard-derived distance is a metric on relations; on raw graph representations the analogous distance lacks identity of indiscernibles because different equivalent graphs have distance zero. Theorem 4 constructs unique singular/compact reconciliation for the **intersection** of two same-sequence-set relations. Theorems 5 and 6 bound its implementation by O((P1+P2) log P1) time and O(P1+P2) space, with P_i the total path length in the input graph's node representation.

**Reuse:** a concrete Alt-G exemplar of observation-equivalence, normal forms and property-preserving transformations. It is not a theorem that G1 forests/histories/registers may be discarded. **New candidate:** a valid less-conservative union/consensus homology reconciliation preserving sequence/orientation constraints and exposing unsupported relationships; the authors explicitly leave it to future work because intersection can delete genuine homology missed by one graph. Global novelty and the exact closure/operator choice remain unresolved.

Software: [vgrecon](https://github.com/anialisiecka/vgrecon), public repository/README verified, C++11 and gfalace pipeline dependency. README blob 35e4293c9587e1b722045dab85b758de6ecd48d6. It provides intersection reconciliation and relation-cardinality computation, not the proposed consensus extension.

## Focused secondary sources

- **3, GSI:** [official source](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.WABI.2026.3), Theorem 1 and §4. Joint spectrum→peptide→protein inference avoids discarding spectrum information between stages. GSI is NP-hard even under bounded-degree/equal-weight restrictions and has a MILP formulation. Useful Bio1 lesson: an irreversible preprocessing interface may lose target information. Weighted-objective calibration and chimeric-spectrum handling are explicit directions, but no consistency theorem is supplied. [Code](https://github.com/BenoistEmile/GSI)
- **4, variable-order DBG contigs:** [source](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.WABI.2026.4), Theorem 8, §3.1.6 and §6. Full reconstruction has explicit frequency/coverage conditions; the paper says real data never meets those conditions in practice. Its per-node misassembly analysis assumes uniform frequency fluctuations, broken by nonuniform/allele-specific coverage. Useful as a G6 provider-contract example; local adaptive thresholds/polyploid extension remain author directions. [Ryu](https://github.com/ddiazdom/ryu)
- **8, pangenome personalization:** [source](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.WABI.2026.8), Theorem 2 and §5. Two paths on a DAG optimize a declared local score via DP/min-cost flow or greedy. The 4/(3+α) greedy ratio needs nonnegative, diminishing second-use weights satisfying the stated α bound; experimental negative penalties fall outside that theorem. Recovered paths are expressly not phased haplotypes. A reusable G7/menu-cost optimization template, not biological full-source recovery. [2paths](https://github.com/fmfi-compbio/2paths)
- **12, maxStacks inverse folding:** [source](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.WABI.2026.12), Theorems 3, 5, 12–13 and §7. Locked sequences certify unique folding in the specified stacked-base-pair model. Linear-time construction assumes sufficiently long helices, with logarithmic degree/helix-count thresholds; Turner-model validity is empirical. This is a valuable certificate-construction template, including general pseudoknots, without solving unrestricted inverse folding. **Reserve:** exact/FPT treatment parameterized by total small-helix length is author-proposed; unrestricted maxStacks inverse-folding hardness remains open in the paper. [Artifact](https://doi.org/10.5281/zenodo.20266457)
- **15, natural-genome small parsimony:** [source](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.WABI.2026.15), §5 and the cost/state-space construction. Extant genomes and the supplied phylogenetic tree suffice for the formulation; bounds restrict ancestral marker frequencies/adjacencies without simply presupposing a putative ancestral set. This is an Alt-G comparison for sound state-space bounding, not G3/G4 stopping. Some practical instances did not obtain a conclusive optimum certificate. **Reserve:** finite indel/rearrangement cost tradeoffs and tighter safe pruning. [SPP-DCJ-exact](https://github.com/gi-bielefeld/spp_dcj_exact)
- **17, DiscrimAlign:** [source](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.WABI.2026.17), Propositions 5–7 and §5. Learns alignment scores through a logistic classification objective; it is explicitly not designed to optimize alignment accuracy. Local likelihood concavity is not global concavity/unique parameter identification; complete label separation can make parameters diverge. Useful objective/estimand/conditioning gates for the selector. Maximizer geometry, sensitivity and statistical tests are author questions, left outside the core count. [Code](https://github.com/BioGeMT/DiscrimAlign)
- **19, median complexity:** [source](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.WABI.2026.19), Theorems 10, 12, 18, 20 and §6. NP-completeness for (ℓ,6) with ℓ≥4 and (3,12) extends into the stated larger even-k regions. **Reserve:** (3,4)-Median is explicitly still open. The 4/6/12 thresholds concern rearrangement-median parameters, not G root counts or panel sizes; this branch is mathematically distinct and low immediate transfer.
- **21, exact spaced-seed filters:** [source](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.WABI.2026.21), optimization formulations and §5. Hit-plus-coverage thresholds are computed by ILP/DP for a declared bounded-substitution model. Extra incidental hits in a presence-only index can break MinCov|Hits exactness; the paper supplies a concrete false-rejection mechanism and conservative safe-MinCov repair. Import that gate before using the word exact for an upstream Bio1 sequence provider. [Code](https://gitlab.com/rahmannlab/seed-optimization)
- **30, PRISM:** [source](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.WABI.2026.30), §5. Posterior structural-class summaries can reveal a shifted pseudoknotted motif lost by a base-pair centroid. The ensemble is conditional on a fixed pseudoknot-free scaffold and restricted to hierarchical density-2 structures; class masses/base-pair probabilities are sampled, not universally exact. **Core addition:** the authors explicitly propose adaptive sampling until a specified probability/frequency confidence threshold, or direct selected class masses. G6/Bio1 transfer needs optional-stopping-valid simultaneous control and scaffold uncertainty kept separate. [PRISM](https://github.com/TheCOBRALab/PRISM), public README verified, blob 3dfaa8e9fd19189fdbabde9e9550ff719deadbd3; C++/CMake. The README contains inherited HFold/CParty wording, so command/source version matching should precede a pilot
- **31, catfish-LP, extended abstract:** [source](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.WABI.2026.31). LP-guided equation rejection and subflow constraints augment a heuristic minimum-flow decomposition pipeline on a DAG with one source/sink. This is a G7/Alt-G candidate falsification/pruning architecture, not a proved exact global MFD solver; near-ILP experimental quality does not establish optimality. A full-version proof/source check is required before importing any asserted safe contraction. [Code](https://github.com/Shao-Group/catfish-LP), [full-version DOI](https://doi.org/10.64898/2025.12.11.693570)

## Core extension ledger and priority

These are **targets/families**, not conjectures already known to be globally novel. An author direction is evidence of an unresolved issue in that paper; it is not evidence that nobody else has solved it since.

| Family | Provenance and local novelty | Concrete surviving output | Program | Priority |
|---|---|---|---|---|
| E0. Coupled TOB/blob provider certification | Existing Bio1 direction, sharpened by article 1 | Honest end-to-end success/abstention with TOB, quartet and compatibility events included | Bio1/G6/G7 | Highest existing biological lane |
| E1. Consistent tractable tumor provider | Author-explicit open direction, 23 §5; new relative to checked catalog | Consistency theorem or exact failure certificate for a specified marginalized model and implementable algorithm | Bio1/G6; Alt-G tumor contract | Highest new conceptual lane |
| E2. Observable Turnpike certificate/abstention | Project-generated adaptation of 20; novelty unresolved | A computable valid condition excluding reliance on unknown true gaps, with multiplicity/preprocessing semantics fixed | G6/Alt-G | High, tightly scope before proof |
| E3. Triangle-LP integrality | Author-explicit open direction, 20 §5 | Useful structural integrality class or certified fractional obstruction, not empirical integrality rate | Alt-G/G7 | Medium theory; source/code gate |
| E4. k-tree incompatibility O(nk+d) | Author-explicit open problem, 25 §3.5 | Optimal algorithm or model-specific lower bound; improve sparse-pair regime | Bio1/HG diagnostics/Alt-G | High practical backend + sharp theory |
| E5. Calibrated eaDCA stopping | Author-explicit missing criterion, 11 §4.1 | Target-specific stopping/abstention with width/cost and positive-vs-negative coupling interpretation | G6/G7/Alt-G RNA | Medium, model admission first |
| E6. Richness/entropy interval validity | Author-explicit statistical tightening, 16 §4 | Coverage/abstention under a declared finite sampling law, concentrated fingerprints and N treated honestly | G6/Alt-G | High calibration control; not universal richness solver |
| E7. Valid homology consensus | Author-explicit union/consensus direction, 29 §4 | A well-defined orientation/sequence-safe less-conservative reconciliation and its certificate | Alt-G, G1 comparison | Most distinctive new transfer |
| E8. Adaptive RNA class-mass certification | Author-explicit adaptive/direct-mass direction, 30 §5 | Confidence-stopped conditional class probabilities; preserve scaffold and density-2 conditioning | G6/Bio1/Alt-G | Medium; inexpensive defined prototype after authorization |

E0 is not counted as an additional open family. E1–E8 are eight additions, seven author-explicit and one project-generated. E2 and E3 are independent obligations: observable noise certification does not imply LP integrality, and LP integrality does not establish the unknown truth-level gap premise. E5 and E8 concern different models/targets (learning sparse Potts couplings versus Monte Carlo masses in a constrained folding ensemble); they share a generic stopping template, but cannot be collapsed into one model theorem.

**Most practical immediate reuse:** article 25's implemented optimal pairwise conflict graph, followed by article 10's admissible-bounds interface. These are imported results/tooling, not new scientific conjectures.

**Most exciting challenge:** article 23 exposes a pipeline failure that more data and a better optimizer cannot fix. It motivates an objective-calibration gate before any method is elevated to a source-recovery provider.

**Most distinctive extension:** article 29 gives a fully specified observation-equivalence/normal-form exemplar and a concrete conservative-consensus gap. Its relation can be audited without assuming coalescent semantics.

**Most direct continuation of the biological program:** improve and certify the TOB→blob composition, rather than rebuild NetCS or flatten gene-quartet frequencies into a displayed-quartet oracle.

**Keep in reserve, not counted in E1–E8:** small-helix exact/FPT maxStacks design (12); finite indel/rearrangement cost/state bounds (15); the classical (3,4)-Median complexity question (19). These are genuine author-flagged directions but weaker immediate matches. Other author directions in screened papers were not exhaustively counted.

## What to drop or stop claiming

1. “Fast sparse level-1 blob reconstruction given TOB is new”: already NetCS, and already in Bio1
2. “Optimal two-tree incompatibility construction needs invention”: article 25 solves it, including unrooted/nonbinary/unequal-leaf-set versions under its definitions
3. “A globally optimal tumor tree objective is statistically true”: article 23 supplies counterexamples under its positive α/β model; keep article 10's exact optimization theorem intact
4. “DivQuant's nominal 95% interval is a rigorous G6 finite-data certificate”: the paper explicitly labels its construction heuristic
5. “An exact MinCov|Hits optimizer makes every indexed filter exact”: extra incidental hits change the admissible observation patterns; use the stated conservative repair or another proved adapter
6. “Treewidth-FPT exact RNA normalization/greedy learning/sampling is new”: article 11 already provides it for its coupling graph model
7. “Homology-equivalence canonicalization and intersection reconciliation are open”: article 29 proves them; union/consensus is the surviving direction
8. “PRISM samples arbitrary pseudoknots or its class posterior proves evolutionary ancestry”: fixed-scaffold density-2 folding is its contract
9. “Turnpike combinatorial feasibility means unique latent recovery or observed-data verification of true separation”: neither follows from the stated theorem
10. “Genome median, RNA helix, network level, root-count, or panel-size thresholds are interchangeable”: they parameterize different problems

## Import/selector gate

For every proposed provider, record: source law/class; observed object and preprocessing/index semantics; target or observational quotient; optimizer objective and solver certificate; identifiability assumptions; consistency/calibration status; failure/abstention event; numerical/exactness status; cost regime; and source/software version. Apply this before any new computation. The paper-level pitfalls above are directly useful selector tests, not mere related-title matches.

Repository visibility was independently verified for 10, 23, 25, 29 and 30 through harmless GitHub metadata reads, and READMEs were inspected for 10, 25, 29 and 30. Other software links are paper-declared availability, not fresh executable verification. No packages were installed, no author software was executed, no simulations or biological calculations were run, no proof development occurred, and no external outreach was sent. License compatibility, implementation fidelity and runtime claims need separate checks before an authorized pilot.

## Search boundary and stopping condition

This unit is a bounded proceedings audit. Its denominator is the 31 named WABI 2026 research articles. It is not a systematic review of every venue/year, forward citation graph or subsequent author update. Within this unit, stopping after complete abstract screening and focused inspection of the high-yield matches is appropriate; distant branches should enter a larger queue only when a concrete import, contradiction, assumption weakening or measurable gain appears. Full proofs were not independently re-proved. The linked proceedings and author tools are primary evidence; repeating their metadata across services would not independently verify a theorem.

The all-31 inventory accompanies this report. A separate source manifest records official URLs, authors and PDF SHA-256 hashes. Cached PDFs/text are research inputs and are not needed in the public publication packet.
