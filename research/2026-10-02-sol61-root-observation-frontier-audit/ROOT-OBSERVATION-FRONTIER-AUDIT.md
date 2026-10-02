# A bounded comparison of root counts, observation panels, and phylogenetic network frontiers

Prepared by dot, 2 October 2026. This is an attributed primary-source comparison and static software audit, not a novelty determination or a new computational result. No software was installed or executed for this comparison.

## Bottom line

There is no single highest universal “root level” established by this search. Four distinct quantities must be kept separate:

1. The number of **entering ancestral lineages** in the current G4 source experiment
2. The number of **sampled taxa/copies in an observed panel**, such as a quartet or quintet
3. A hybrid vertex's **indegree**, the number of incoming parental arc occurrences
4. **Network level**, the maximum number of reticulations within a blob

A further distinction is essential: simulating one realization, computing an exact forward probability/distribution on a supplied source, and proving inverse recovery or an optimal observation cutoff are different accomplishments. None supplies the others automatically.

The strongest fresh reuse hit is Cummings et al.'s 2026 symbolic NMSC compiler. Its inverse study excludes every 2-cycle, so it does not settle serial-bigon stopping. Older general network probability computation already handles arbitrary binary topologies and multiple sampled alleles. On the topology axis, a 2025 theorem already covers special **non-planar networks of arbitrary level**, so “level 2” is not a universal frontier either.

## Contracts used for comparison

The current G4 result is a uniform exact six-entering-root recovery theorem for two unknown ordinary pads surrounding a **supplied known positive bare one-bigon**, under private independent serial two-port coalescent source semantics. Its [pad-recognition report](https://github.com/Sodelin/Research-Commons/blob/5011af5f5b8543e8e78cb558e58e57ab918de5c0/research/2026-10-01-sol61-g4-allcopy-2237z/KNOWN-BOX-PAD-RECOGNITION.md) and [sharp-six report](https://github.com/Sodelin/Research-Commons/blob/5011af5f5b8543e8e78cb558e58e57ab918de5c0/research/2026-10-01-sol61-g4-allcopy-2237z/KNOWN-BOX-SHARP-SIX.md) are recorded at commit 5011af5f5b8543e8e78cb558e58e57ab918de5c0. Full labelled forests are exposed by legal topology tomography. Its concrete observation uses six entering A copies and three references, hence nine total copies. Six is a worst-case minimal cutoff for this specific inverse branch, not the highest n handled by the field. Arbitrary unknown bare or multi-cell all-copy stopping remains a different open problem.

The supplied G5/HG result uses exact **rooted calendar-law** panels on positive temporal cut-child sources without planarity. Binary M3 obtains the full displayed rooted cluster family/S; indegree at most k has a sufficient (k+1)-panel bound. That is neither a finite-DNA result nor a quartets-only CF result nor an optimal sample-size claim.

These working contracts are the basis of the comparisons below, not claims attributed to external papers.

## 1. The 2026 quintet paper: theorem audit

Joseph Cummings, Maize Curiel, Bryan Currie, Bryson Kagy, Udani Ranasinghe, and John A. Rhodes, *Identifiability of phylogenetic networks and quintet concordance factors*, arXiv:2608.03544v1, submitted 4 August 2026. The rendered manuscript gives an internal date of 24 August 2026. [Full text](https://arxiv.org/html/2608.03544v1), [versioned record](https://arxiv.org/abs/2608.03544v1).

### Model and observation

The source is rooted NMSC with independent inheritance. Finite lengths are positive coalescent lengths, hybrid probabilities lie strictly between zero and one, and an infinite ordinary edge above the root completes coalescence. The root is taken to be the least stable ancestor; structure above it has no topological effect. The baseline samples one labelled lineage per taxon. CFs discard metric gene-tree lengths and root locations, leaving unrooted binary topological gene-tree probabilities. A quintet is the complete 15-coordinate law for a five-taxon subset, not just the five collections of quartet marginals.

The inverse computation considers five-taxon binary level-1 networks **without 2-cycles**. After eliminating cherry-blob equivalences, it studies 190 rooted topologies: 108 with a fully resolved blob tree, 73 with a four-way blob-tree node, and nine with a five-way node. All inverse identifiability results are within the stated model/classes; generic or algebraic conclusions must not be upgraded to uniform recovery at every positive parameter.

### Exact result map, paraphrased

- **Proposition 4.1:** Replacing a rooted cherry by an arbitrary 3-blob with the same two descendant leaves gives exactly the same stochastic sets of gene-tree topology distributions as the local parameters vary, with upstream parameters fixed. This is actual equality of stochastic images, applying to arbitrary m-tet CFs; it is stronger than merely equal ideals. It is a structural obstruction under the one-per-taxon observation contract.
- **Theorem 4.7:** For a fully resolved five-taxon tree of blobs, quintets generically detect a central 3-cycle. When it is present, additional cherry 3-cycles are algebraically indistinguishable and roots are constrained to specified cut-edge/cycle/pendant or cherry-cluster regions. When no central cycle is present, the root is identified except for ambiguity inside a cherry cluster containing a 3-cycle; a cherry 3-cycle can be detected when the root is in that cluster. Hybrid nodes in 3-cycles remain ambiguous beyond the constraints imposed by root location. Full ideals were certified for these cases, so the algebraic classification is complete, although semialgebraic distinctions are a separate question.
- **Theorem 4.8(1):** For the four-way blob-tree case, the 4-cycle hybrid is identifiable. Parts (3) and (4) provide root recovery or regional constraints depending on which taxon group is hybrid; a DE-cluster 3-cycle is detectable only when the root is in that cluster, and its hybrid remains ambiguous. **Critical caveat for part (2):** the stated inability to distinguish cases with the hybrid ancestral to D and E describes the currently found low-degree invariants/matroids. The authors explicitly do not certify equality of the full ideals and provide numerical evidence that all seven rootings may be distinguishable. Do not cite that part as a proved universal nonidentifiability theorem.
- **Theorem 4.9:** In the five-way blob-tree case, both root and hybrid locations are identifiable. The theorem's reference to a “4-blob” is evidently a textual slip: the setting, Figure 6(iii), discussion and proof concern a 5-cycle/5-multifurcation.
- **Section 5:** Extending quintet results to larger networks is deferred. Even a larger source with no 2-cycles can induce 2-cycles on five-taxon restrictions. The authors expressly omit their analysis and announce subsequent work.

### Proof/computation limitations

The authors use polynomial parametrizations in X=exp(-length), compute low-degree invariant ideals, and then seek completeness certificates through primality plus matching ideal dimension and Jacobian rank. They use variable elimination, Gröbner bases, or algebraic-matroid circuits where needed. Partial low-degree invariants alone are not a full ideal certificate. Some four-cycle cases appear to require missing invariants of degrees 13, 29 or 62 and could not be symbolically settled by the available computations. This is a warning against claiming exhaustive inversion merely from finite search or agreeing truncated invariant sets.

These observations and theorem descriptions are attributed to the above authors; the arXiv paper is distributed under CC BY 4.0.

## 2. The 2026 forward compiler: actual source and reuse

[Repository](https://github.com/jcu237/SymbolicCoalescentModel), inspected main commit [a502e3a447e6a05d59a39bd81c20f484ee40cde3](https://github.com/jcu237/SymbolicCoalescentModel/commit/a502e3a447e6a05d59a39bd81c20f484ee40cde3), dated 29 July 2026. [MIT license](https://github.com/jcu237/SymbolicCoalescentModel/blob/a502e3a447e6a05d59a39bd81c20f484ee40cde3/LICENSE). The following is a static source audit, not an execution result.

- [SCM/SCM.m2](https://github.com/jcu237/SymbolicCoalescentModel/blob/a502e3a447e6a05d59a39bd81c20f484ee40cde3/SCM/SCM.m2) supplies `makeProb`/`makeProbability`. Input is a known directed source graph, one supplied unrooted target gene tree (possibly a strict subset of source leaves), an edge-probability table and a hybrid table. Output is the target's symbolic rational-polynomial or numerical probability. The core recursion has no explicit n=5 check.
- Finite ordinary edges enumerate **rooted labelled forests compatible with a rooting of the target tree**. `probOfForestInEdge` gives c(F)/product(binomial(k,2)) times the Tavaré lineage-count transition. Hook-length/linear-extension counts are implemented in `buildOrdersTree` and `buildOrdersForest`. Consequently this is a direct prior source for more than count-only propagation.
- A hybrid is processed after its descendants have become pendant current ancestors. Every bipartition has weight gamma to the number sent to one parent times (1-gamma) to the number sent to the other. This routes **live ancestral blocks after coalescence**, not independent fresh coins for each original sampled label.
- [SCM/updateGraphs.m2](https://github.com/jcu237/SymbolicCoalescentModel/blob/a502e3a447e6a05d59a39bd81c20f484ee40cde3/SCM/updateGraphs.m2) contracts each formed subtree to a leaf carrying the concatenated labels in both network and target tree. The above-root base case sums all root placements with their ranked-history counts. It does not assume a uniform distribution for n>5.
- [SCM/miscGraphFunctions.m2](https://github.com/jcu237/SymbolicCoalescentModel/blob/a502e3a447e6a05d59a39bd81c20f484ee40cde3/SCM/miscGraphFunctions.m2) has an important convenience limitation: `getGeneTrees(k)` explicitly returns an empty list for k>=6. The 3-, 4-, and 5-leaf targets are hardcoded. This does **not** refute the general core, but a six- or nine-copy pilot needs a supplied target or a separately verified enumerator.
- The shipped hybrid update destructures exactly **two distinct parent vertices**. General indegree needs a proved reduction, as the paper discusses via zero-length additional hybrid edges. Literal parallel incoming arc occurrences cannot simply be passed as duplicate graph edges and presumed preserved. They need a representation proof, for example distinct unary-parent paths with correctly composed survival products. Zero-duration guard representations must not silently be admitted as new positive physical sources.
- Repeated samples require separate injective leaf tags together with the shared species-edge coalescent segment. Merely reusing a taxon name or adding unrelated extra leaves is not that semantics. Since label blocks are canonized by concatenating and sorting characters, use collision-free tags or a verified block-encoding adapter. Numeric internal-node names also need to avoid the generated `-hybrid-10` identifiers.
- The public source contains parameter files, graph families and ideal scripts. The ideal scripts depend on `MultigradedImplicitization` and/or `Matroids`; forward SCM uses `Graphs`. Those packages and the working-directory-relative imports need to be handled in any approved pilot. There is no evidence in this static inspection of a calendar-law output or a inverse stopping certificate.

### Immediate reuse decision

This compiler is an independent forward-control candidate for a proved G4 adapter. It overlaps the labelled-forest finite-edge and independent-routing mechanisms and should be credited. It does not supply G4's legal tomography theorem, the supplied-known-bigon/two-pad inverse uniqueness, a sharp six cutoff, or the arbitrary unknown all-copy stopping result. It also does not subsume G5/HG's calendar-law boundary recovery.

A bounded pilot proposal, **not started**, is: first certify parallel-arc and repeated-copy translations; then test a tree, one independent bigon and two serial independent bigons on known sources; check normalization and sampling restriction, plus one symbolic or numerical target cross-check. Common shared-coin routing is a separate control and cannot be obtained by merely reusing the independent formula. Do not begin expensive full nine-copy enumeration as the first test.

## 3. Earlier primary comparisons

### Allman, Degnan, Rhodes (2011): species-tree roots

[Identifying the rooted species tree from the distribution of unrooted gene trees under the coalescent](https://arxiv.org/abs/0912.4472), DOI 10.1007/s00285-010-0355-7. Four species with one sample each do not identify the root. With five or more species the full unrooted gene-tree topology law identifies the rooted species tree and its internal coalescent branch lengths. A pendant length becomes identifiable when that species has multiple gene samples. Five is a sufficient/minimal threshold in that source/observation setting, not a maximum tractable n and not a reticulation result.

### Yu, Degnan, Nakhleh (2012): a general repeated-allele forward control

[The probability of a gene tree topology within a phylogenetic network](https://journals.plos.org/plosgenetics/article?id=10.1371/journal.pgen.1002660). Their general forward method, implemented in PhyloNet, allows any binary source-network topology, multiple hybridizations and multiple sampled alleles per species. It converts the source to a MUL tree and sums valid allele mappings/coalescent histories. Crucially, duplicated MUL branches mapping to one original population edge are not treated as independent coalescent populations: their original-edge mapping couples the calculations. This is a potentially closer repeated-copy control than an unproved one-leaf-per-taxon encoding. Arbitrary forward computation still does not prove inverse uniqueness or an optimal panel cutoff. No execution or benchmark was performed here.

### Allman, Baños, Garrote-Lopez, Rhodes (2024): quartets on level-1 networks

[Full preprint](https://arxiv.org/html/2401.06290v1), [published article](https://doi.org/10.1007/s11538-024-01339-4). The published theorem numbering differs from the original arXiv HTML. The original Proposition 22 and Theorem 24 show generic topology recovery with explicit small-cycle exceptions and invisible 2-cycles. Importantly, collections of **quartet** CFs across at least five taxa already generically identify 4-cycle hybrid directions. Thus the statement that “quartets fail to recover a 4-cycle hybrid” needs its sampling/context qualifier. Three-cycle orientation has identifiable and nonidentifiable positive-measure parameter regions; it is not resolved by a blanket generic argument. Multiple samples remove some singleton-group obstructions. The retained target is semidirected topology, not calendar timing or G4's full forest experiment.

### Allman, Ané, Baños, Rhodes (2025): arbitrary network level in a restricted class

[Beyond level-1](https://arxiv.org/html/2504.21116v1). Definition 7 defines C_k by reduced, galled, tree-child blobs whose isolated hybrid cycles have at least k edges. Its k is **minimum cycle size**, not maximum network level. Theorem 5.7: for binary C_4 networks, two samples per taxon and generic parameters under independent/common NMSC, quartet CFs identify semidirected topology and lengths of internal tree edges in blobs; for C_5 the stated result holds with one sample under the coalescent models. Proposition 5.8 supplies a more restricted one-sample topology theorem. These classes include non-planar networks of arbitrary reticulation level. All-blobs tree-child is stronger than merely calling the whole rooted network tree-child. Reduced/class assumptions must not be interpreted as recovery of arbitrary inserted 2-blobs. This is useful structural prior art and a source of model-specific conditions, not G5/HG calendar-law recovery.

### Holtgrefe et al. (2025): displayed quartets identify a canonical quotient

[Distinguishing level-2 networks with quartets and inter-taxon quartet distances](https://arxiv.org/html/2507.17308v2). Theorem 5.4(a) characterizes exactly when outer-labelled-planar, galled semidirected level-2 networks differ in displayed quartets: precisely when their canonical forms differ. Part (b) gives the parallel characterization by pairwise NANUQ distances for bloblets with at least four leaves. Some distinct networks have one canonical form. Theorem 4.7 gives circular decomposability on bloblets; broader global distance behavior and level-3 extensions are conjectural. A displayed-quartet set and exact CF law are not the same observation, and this theorem suppresses roots. It is reusable as an observation-quotient/control methodology, not as full unrestricted-source or rooted-calendar identifiability.

### msprime (2022) and official current documentation: simulation scale

[Baumdicker et al., msprime 1.0](https://doi.org/10.1093/genetics/iyab229), [open primary article](https://pmc.ncbi.nlm.nih.gov/articles/PMC9176297/). The paper describes simulation of millions of whole chromosomes and a succinct tree-sequence representation. This is a forward simulation scale statement, not enumeration of the exact law across all tree topologies or an inverse cutoff theorem. [Current ancestry documentation](https://tskit.dev/msprime/docs/stable/ancestry.html) supports sampled populations, multiple samples, explicit sampling times and initial states. [Admixture documentation](https://tskit.dev/msprime/docs/stable/demography.html#admixture) routes each current lineage to an ancestral population. Explicit ploidy and time-unit choices are necessary. An independently routed admixture model is a candidate numerical control for compatible G4/G5 physical sources after an adapter proof; it does not justify common-coin semantics or supply exact inverse certificates.

## 4. Practical upgrades before new computation

1. **Reuse established forward engines**, with attribution: the 2026 symbolic forest compiler for transparent target probabilities and PhyloNet's older repeated-allele formulation as an independent semantics control.
2. **Prove the source adapters first**: original incoming arc occurrences, private cells, reused parameter rows, live-block routing, distinct copies and forest grafting must commute with the translation.
3. **Use independent/common controls explicitly**: [PhyloCoalSimulations](https://github.com/JuliaPhylo/PhyloCoalSimulations.jl) implements network coalescent simulation with possible inheritance correlation; its 2023 paper introduces a Dirichlet-based bridge between common and independent inheritance. This is a more natural stochastic comparator for the cap-four inheritance separator than assuming every simulator has both extremes.
4. **Separate observations in every report**: count transitions, complete labelled forests, rooted topology, unrooted CFs and calendar laws require different sufficient-statistic and restriction proofs.
5. **Retain exact inverse certificates**: a forward implementation or numerical failure to find alternatives is not the finite stop certificate. Shared-parameter incidence, positive-domain branch selection and all-copy injectivity remain theorem obligations.

For scale intuition only, a full nine-distinct-label unrooted binary topology distribution has (2*9-5)!! = 135,135 entries; the rooted analogue has 2,027,025. These combinatorial counts do not apply unchanged to every partial-forest observation, and they are not measured compiler timings. Selected witnesses/restrictions can be much cheaper than complete law enumeration.

## Search boundary

This was a bounded title/author/algorithm search and direct inspection of the named primary papers, their cited computational methods, the 2026 source repository and two official Julia repositories, plus official msprime documentation. It was not a systematic review, exhaustive citation graph search, benchmark, installation audit or independent theorem reproof. The searches did not establish a maximum feasible exact n, a maximum general network level or absence of more recent related results. The 2026 paper is a preprint, and its numerical distinguishability evidence was not rerun. The conclusions above are conditional on matching the specified source, observation and recovery target.
