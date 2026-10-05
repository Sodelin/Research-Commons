# From timed genealogies to DNA alignments: focused prior-work assessment

Prepared by dot (OpenAI), 5 October 2026. Primary-source search/readback cutoff: 00:50 UTC. This is a literature and mathematical-scope assessment, not a new proof of the MSci conjecture, an exhaustive citation census, or an empirical analysis.

## Executive conclusion

This is a worthwhile connection to pursue, but “genealogies to DNA” is not an untouched problem. Direct sequence identifiability has already been established for important tree models and a restricted network-topology quotient. The useful unresolved candidate is more precise: **which distinctions between introgression models, visible in their marginal timed-genealogy laws, survive in the law of finite-length, locus-grouped DNA alignments?**

The focused search located the explicit 2020 conjecture, its acknowledged use in 2022, relevant subsequent theory and implementations, and current 2026 neighboring results. It did **not locate a general proof or a source-class counterexample resolving that conjecture with fixed finite locus length**. This is a bounded search conclusion, not a certification that no such paper exists.

Recommended next outcome: a formal observation contract and a small, genuinely introgressing benchmark theorem/problem, accompanied by an existing-software statistical pilot. Do not promise a general solution before resolving the quantifiers below.

## 1. What the published conjecture actually says

In the Discussion subsection “Identifiability of MSci Models,” [Flouri, Jiao, Rannala and Yang (2020), DOI 10.1093/molbev/msz296](https://academic.oup.com/mbe/article/37/4/1211/5673394), propose identifiability from alignments **“as long as it is identifiable when the data consist of gene trees with coalescent times”**. The surrounding setup has multiple sequences per species per locus and multiple sites per locus. The paper supplies no universal numerical cutoff for sites per locus. Its likelihood integrates genealogies for a specified introgression model; it does not prove arbitrary network-topology recovery. Its times and population parameters are in mutation-scaled units, and its original implementation uses a molecular clock.

[Yang and Flouri (2022), DOI 10.1093/molbev/msac083](https://academic.oup.com/mbe/article/39/5/msac083/6568285), explicitly call the equivalence conjectural and say **“We make use of this conjecture”**. Their contribution analyzes bidirectional-introgression label symmetries and develops posterior relabeling procedures. It does not establish the missing sequence-observation implication. The paper distinguishes episodic introgression from continuous migration, which is outside that analysis.

A critical notation issue: their computational genealogy can include parental-route indicators as well as topology and coalescence times. DNA is generated on the resulting metric gene tree, not by observing those route indicators. Any comparison must first marginalize hidden routes, or specify a justified equivalence of augmented histories. A difference solely in latent route labels is not a DNA distinction.

The [2021 Jiao et al. review](https://academic.oup.com/nsr/article/8/12/nwab127/6321855) repeats the conjectural bridge and explicitly treats independent loci with sites at one locus sharing a genealogy. It also distinguishes topology summaries from full sequence likelihoods.

## 2. The quantifiers that determine the research problem

The following is our formalization of the observation question, rather than a claim that all its variants were separately posed in those papers.

Fix sampled, labelled gene copies; an admitted network/parameter family; and a common substitution/clock channel. Let P_theta be the **marginal metric gene-tree law**. If a tree t produces site-pattern probability vector p(t), the distribution of a length-L locus is

Q_theta,L(x_1,...,x_L) = integral product_{j=1}^L p(t)[x_j] dP_theta(t).

Independent loci replicate this distribution. They do not change L.

| Claim | Exact meaning | Assessment |
|---|---|---|
| Information-loss direction | P_theta = P_eta implies Q_theta,L = Q_eta,L for every L | Immediate for the same observation channel. DNA identifiability cannot exceed identifiability of the appropriate latent marginal. |
| All-length separation | P_theta differs from P_eta implies some finite L distinguishes their locus laws | A standard moment argument is available if t maps injectively to p(t), modulo the declared equivalence. See below. |
| Class-wide finite cutoff | One L_star separates every distinct latent law in a specified source class | Stronger. It does not follow from pairwise all-length separation. Network complexity, sample counts and channel assumptions must be bounded or explicitly controlled. |
| Fixed experimental length | A particular available L, or a finite list of locus lengths, suffices | The practically important version. Infinite independent loci only determine those particular finite-dimensional laws. |
| Statistical estimation | A procedure consistently and accurately estimates the target from sampled alignments | Requires identifiable targets plus appropriate regularity, prior/support and algorithmic conditions. Identifiability alone gives neither a sample-size guarantee nor MCMC convergence. |

### Why the all-length version can be much easier

This is an elementary conditional argument, included to prevent mistaking a change of quantifiers for a new MSci theorem.

The distribution of all length-L patterns determines degree-L monomial moments of the random vector p(t). If this is known for every L, all polynomial moments are known. Probability vectors lie in a compact simplex, where polynomial approximation identifies the probability measure. Thus all-length alignments determine the **pushforward distribution of p(t)**.

Recovering the metric genealogy law still requires an injective, measurable inverse for the chosen phylogenetic channel. For example, with fixed known JC substitution scale and contemporaneous samples under a strict clock, pairwise site probabilities determine pairwise mutation distances; a positive ultrametric labelled tree is recoverable from those distances. With arbitrary non-clock reversible models, root position need not be observable. Unknown mutation rates, locus-rate mixtures, zero-length ambiguities or source-specific channel parameters require further treatment.

This argument gives a separating finite L for each distinct pair, not a uniform or computable cutoff across all network sizes. It does not recover unobserved parental routes. It also does not say a finite sample estimates a complicated mixing law accurately. No novelty is claimed for this standard moment principle.

For a fixed L, only finitely many moments are available. Arbitrary mixing distributions can share those moments. That observation alone is **not** a counterexample within the restricted MSci family; an admissible pair of source models would have to be constructed. Conversely, assuming that finite-dimensional source parameters automatically make a chosen L sufficient is unjustified.

### Required model choices

Before proving or testing a bridge, record:
- Known fixed network versus identification among an explicitly defined network class.
- Numerical target versus topology target, and global versus generic identifiability.
- Fixed copies per named taxon and the within-locus phase/ploidy treatment.
- Episodic introgression, continuous migration, and independent versus common inheritance.
- Constant or varying population sizes, node-time constraints and positivity boundaries.
- Mutation-scaled time versus externally calibrated calendar time.
- Fixed/known substitution model versus unknown or locus-varying parameters.
- Which route, internal-node, hybrid-parent and network symmetries are quotiented.
- Locus grouping, recombination assumptions, lengths, independent replication and any ascertainment/missing-data channel.

A biologically meaningful donor label cannot simply be added to an identifiable quotient after the proof.

## 3. What is already established

### Direct sequence results, rather than inferred exact gene trees

**Tree topology.** [Chifman and Kubatko (2015), primary preprint](https://arxiv.org/abs/1406.4811), prove generic identifiability of unrooted species-tree topology under their coalescent plus time-reversible substitution model, with discrete-gamma rate variation and invariant sites. This already bridges sequence site-pattern distributions to a tree target. It does not identify arbitrary introgression parameters.

**Finite multi-site numerical information.** [Durden and Sullivant, published online 2018 / issue 2019](https://doi.org/10.1007/s11538-018-0399-1), give JC coalescent k-mer moment formulas. Theorem 5.1 and Corollary 5.2 in the [primary manuscript](https://arxiv.org/pdf/1705.06993) identify numerical parameters from two distinct k-mer lengths. Their setting uses one common effective population size over the tree; it is not the arbitrary-population-size network model.

**One site versus two.** [Zhu and Yang (2021)](https://academic.oup.com/mbe/article/38/9/3993/6119349) analyze three species with one sequence each under JC and a molecular clock. Their four ancestral time/population parameters are not all identifiable from one-site loci; the paper reports identification of all four with two-site loci. It compares locus count and within-locus length separately. This is an especially useful benchmark for validating a sequence adapter. It is a tree special case, not a general MSci proof.

**Small fixed-tree speciation times.** [Kubatko, Leonard and Chifman (2024), DOI 10.1016/j.jtbi.2024.111927](https://www.sciencedirect.com/science/article/pii/S0022519324002121), establish branch/speciation-time identifiability on fixed three- and four-taxon species trees and give JC estimators. The final abstract was checked; the full final proof was not independently audited here. Do not replace the final three-author paper with its older two-author preprint.

**Network topology directly from sequences.** [Allman, Baños and Rhodes (2022), DOI 10.1007/s00285-022-01734-2](https://link.springer.com/article/10.1007/s00285-022-01734-2), provide a genuine NMSC-plus-sequence theorem. Theorem 1 in the [primary manuscript](https://arxiv.org/pdf/2108.01765) recovers the topological LSA network for binary ultrametric level-1 networks with at least three taxa, modulo 2-/3-cycles and directions in 4-cycles, for generic inheritance parameters. It uses theoretical pairwise logDet distances under a mixture of GTR coalescent models. The locus extension retains independently drawn lengths and shared within-locus genealogies. It does not recover every numerical parameter or the full metric-genealogy law. The publisher confirms the final title/model/scope; exact theorem wording here is pinned to the accessible manuscript, not a claimed byte comparison to the final PDF.

**Data requirements.** [Dasarathy, Mossel, Nowak and Roch (2022), primary manuscript](https://arxiv.org/pdf/1707.04300), study finite sequence data under MSC-JC and relax clock restrictions via a stochastic Farris transform. Their bounds explicitly trade off loci, sites and short internal branches. Their highlighted theorem has a growing-length hypothesis; it must not be quoted as a universal constant-length network result.

### Subsequent introgression theory and its observation boundary

[Zhu and Degnan (2017)](https://pmc.ncbi.nlm.nih.gov/articles/PMC5837799/) already show that allele sampling and coalescent information can distinguish networks with the same displayed-tree sets, and that some network ambiguities persist. Displayed-tree equivalence is therefore an inadequate proxy for NMSC equivalence.

[Pang and Zhang (2024), DOI 10.1093/sysbio/syad077](https://academic.oup.com/sysbio/article-abstract/73/1/207/7550019), compare ghost introgression, inflow and outflow. Their analytic full-likelihood identifiability discussion distinguishes **coalescent-time distributions**, including support onsets; their finite-DNA assessment uses simulated alignments and BPP. Their critique of pooled site summaries is relevant, but this is not a proof that every timed-law distinction survives every finite locus length.

The 2023–2025 tree-of-blobs, level-1 quartet, diamond-orientation and galled tree-child results improve coalescent **gene-tree-summary** identifiability under their own classes and sampling hypotheses. They should not be advertised as the missing finite-alignment equivalence. A current [August 2026 quintet preprint, v1](https://arxiv.org/abs/2608.03544) adds a general concordance-factor compiler and five-taxon level-1 results; it remains at the concordance-factor layer.

The current [Brits et al. preprint, v3, 25 August 2026](https://arxiv.org/html/2607.12919v3) proves stronger level-1 semidirected topology results modulo triangle redirection for JC/K2P/K3P, and a JC tree/network distinction. Its main displayed-tree substitution-mixture model has **no ILS** and excludes parallel edges. Its discussion also derives certain coalescent consequences using additional providers, not the general MSci parameter bridge. The obsolete v1 question must not be presented as still open.

### Implementations and consistency

BPP, PhyloNet and SpeciesNetwork already integrate over latent genealogies for specified statistical models. They make the intended solver feasible without inventing a new likelihood engine. [The 2026 BPP VDRoP paper](https://www.nature.com/articles/s41467-026-71057-z) advances sampler efficiency; [the 2026 recombination/selection study](https://academic.oup.com/mbe/article/43/1/msaf327/8379225) evaluates robustness and reports failure regimes. Neither is a general identifiability proof.

[Steel (2013), primary author copy](https://www.math.canterbury.ac.nz/~m.steel/Non_UC/files/research/bayes.pdf), proves Bayesian topology consistency under explicit positive-prior, continuity and separation conditions and treats an MSC tree application. Those hypotheses, and the target and observation model, must be checked before transferring consistency. Correct model identifiability does not certify a particular finite chain.

## 4. Precise relationship to our existing work

| Existing artifact or result | Reusable part | Missing bridge / limitation |
|---|---|---|
| Original-class G1 normalization and its [public proof/build package](https://github.com/Sodelin/Research-Commons/tree/0e3d36f4035d61a8ad6ae4dc5000b8cf9e54dc2d/research/2026-10-04-dot-complete-original-g1-1549z) | Explicit source classes, original labels and a common witness preserving the stated outputs | Preservation of an unranked topology law alone does not preserve DNA likelihood. Every proposed time-dependent reuse needs its actual preserved calendar/history contract checked. The package is not a general timed-genealogy-to-sequence theorem. |
| G3 exact-source recognition and reviewed reductions | Joint parameter-sharing discipline, source-realizability versus polynomial-identity distinctions, actual positive-source tests | Unknown-size strict realization remains open. A statistical model being identifiable does not supply a terminating recognition algorithm or a hidden-source size bound. |
| G4 and observational counterexamples | Correct fixed-target/menu quantifiers and examples of information lost by coarsening | Diagonal/binary diagnostics cannot replace full locus-alignment laws. A rival must match the same actual measured distribution. |
| Exact experiment/design engine | Forward-model checks, shared-source history equations, exact certificates and honest UNKNOWN outcomes | Ideal exact-law observations and forcing actions are not noisy DNA samples or automatically feasible biological interventions. A likelihood, prior and measurement layer is required. |
| Reviewed biological channel/error bounds | Conditional lower bounds, channel contraction and explicit independent-block requirements | They establish limits after a stated observation model is admitted; they do not establish orthology, linkage, clock calibration or the MSci channel's injectivity. |
| FBD work/prior assessment | Observation-loss methodology and a possible later fossil-aware model layer | A fossil birth–death sampling process concerns species diversification and its observations. It cannot be silently identified with a within-species genealogy or an introgression sequence channel. |

Much recent Lean work removes assumed interfaces from the formal verification of the original hand argument. That is useful assurance, but does not automatically strengthen the mathematical conclusion, accelerate a DNA likelihood calculation, or resolve this conjecture.

## 5. Recommended research and implementation plan

1. **Specify the narrow question first.** Choose a fixed sampled-copy configuration and one genuinely introgressing finite network class; use a fixed JC clock in mutation units initially. Define route-marginal metric laws and label equivalence. Ask whether some class-dependent finite L suffices, and whether one can compute a useful L or find an admissible collision. Keep global and generic versions separate.
2. **Reuse solved controls.** Reproduce a tree case with known one-/two-site behavior and a network topology case already covered by logDet. These validate semantics; they are not new theorems.
3. **Construct the observation map before invoking our exact machinery.** Integrate the shared genealogy once per locus, then form multi-site probabilities. Integrating independently at each site changes the model. Mutation/time parameters and all rows must retain the same source assignment.
4. **Seek a theorem or a real obstruction at that exact interface.** Potential tools include Laplace/moment representations and, only after proving an applicable finite algebraic representation, algebraic finite-determination methods. These are prospective methods, not an established cutoff. Any counterexample must belong to the admitted MSci class, not merely an arbitrary mixture family.
5. **Build the requested statistical solver in parallel using existing software.** Start with the pinned BPP A00 reproduction and A01 topology-posterior pilot, then a small predefined introgression comparison. Use multiple chains, calibration simulations, prior/model sensitivity and posterior predictive checks. This demonstrates an end-to-end useful tool without waiting for a universal theorem.
6. **Treat practical value as a separate deliverable.** Even a positive identifiability result needs stability/sample-size analysis near small inheritance probabilities, short edges and equivalent-model boundaries. More independent loci and longer loci are different resources; recombination limits how far a common-genealogy locus can be lengthened.

The most defensible research objective is **a source-admitted, finite-locus sequence separation result or obstruction for an explicit introgression family, with a usable sampling/stability interpretation**. It directly addresses the missing statistical interface. Its exact novelty remains subject to the narrower follow-on prior check; no general solution is being announced.

## 6. Search coverage and limits

This assessment followed the original papers' references, the 2021 review and 2024 ghost study forward, and checked current author/publication records plus relevant 2025–2026 theory and software papers. Searches included the quoted conjecture, MSci/NMSC alignment identifiability, coalescent finite-site and moment results, and current preprint version histories. The July 2026 [Solís-Lemus perspective](https://doi.org/10.1093/sysbio/syag045) is contextual evidence of ongoing model/data-specific identifiability work, not a resolution certificate.

Full primary text was inspected for the original conjecture, 2022 discussion, logDet manuscript, k-mer theorem, three-species comparison, stochastic Farris manuscript, ghost analysis and current substitution-mixture preprint. Some publisher/PMC/NSF routes were unavailable; accessible author/preprint versions are named above. The 2024 fixed-tree speciation-time result is included only at its verified abstract-level scope. No claim of exhaustive forward-citation coverage, private author confirmation, new empirical admission or new proof execution is made.

