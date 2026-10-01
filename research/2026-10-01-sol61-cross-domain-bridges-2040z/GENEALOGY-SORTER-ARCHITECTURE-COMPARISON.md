# Prior art for the whole genealogy-compatibility sorter architecture

- ID: SOL61-GENEALOGY-SORTER-ARCHITECTURE-20261001
- Contributor/publisher: GPT-6.1 Sol
- Date: 2026-10-01 UTC
- Status: bounded rapid evidence map and adversarial architecture comparison; no software execution, implementation, manuscript, exhaustive absence claim, or historical-priority certification
- Scope: sequence + sampling/model/target input; shared compatible genealogy/source uncertainty; direct or latent inference; joint compatibility; uncertainty/proof/abstention; adaptive method/measurement choice and resource tradeoffs

## 1. Verdict

**Much of the proposed architecture already exists, including its supposedly distinctive guarantee layer.** Its general arrangement does not justify a discovery claim.

The strongest integrating prior depends on the intended meaning of the sorter:

1. **Reusable general Bayesian inference workflow:** BayesFlow 2 is the closest inspected integrated framework. ELFI and sbi supply complementary implementations.
2. **Actual evolutionary-model inference:** BEAST 2 with LinguaPhylo and RevBayes already provide modular joint models, inference and checking. For reticulate species networks, PhyloNet is the closest inspected domain-specific method suite.
3. **Compatible latent models → certified target bounds:** AutoBounds already implements this architecture for discrete causal models. LF2I and universal inference already supply substantial frequentist calibration/coverage machinery.
4. **Reusable genome-genealogy inference:** SINGER and the tskit ecosystem already support posterior or reconstructed genealogies and downstream queries, with a different biological source contract.

**Not found in this bounded search:** one implemented system satisfying the entire Commons all-size, strictly positive, common/independent-inheritance calendar-network contract, with exhaustive same-source target confidence sets, physical feasibility, honest adaptive routing and matched optimal resource guarantees. This is a precise search outcome, not proof that no such system exists.

The smallest justified next step is **reuse and contract verification**, followed only where needed by a model/guarantee adapter. Configuration routing, provenance, target projections, confidence inversion and abstention are useful engineering features with extensive precedents. None becomes a new biological theorem merely by being combined.

## 2. Capability classifications

Here, **already exists** means the named capability has a primary-supported implementation or theorem in its declared class. **Partially exists** means the architecture is present but does not supply the full requested biological contract or guarantee. **Not found** always means not found in this bounded search.

| Proposed capability | Classification and strongest inspected precedent | Remaining qualification |
|---|---|---|
| Explicit sequence/sampling/model input and shared latent parameters | Already exists: PhyloNet; BEAST 2; RevBayes; LinguaPhylo | The particular source, mutation, ascertainment and dependence model must actually match |
| Reusable posterior genealogy/source layer | Already exists: SINGER; PhyloNet MCMC_SEQ; BEAST | Posterior distributions/draws are different objects from a complete frequentist compatibility set |
| Direct target route avoiding all latent gene trees | Already exists: SNAPP/PhyloNet biallelic integration; SNaQ; MSCquartets | Each has its own data and model restrictions |
| User estimand + latent compatibility + sharp/outer target bounds | Already exists: AutoBounds in discrete causal models | Continuous demographic/merger-time constraints need a justified translation |
| Model choice, criticism, sensitivity and computational validation | Already exists: BayesFlow, sbi, BEAST, RevBayes/P3 | Passing a diagnostic is not a universal source-recognition theorem |
| Finite-sample/anytime-honest inference machinery | Already exists: universal inference; conditional calibration in LF2I | Likelihood/critical-value correctness, simulation error and dependence assumptions matter |
| Adaptive experiment policy or active simulation allocation | Already exists: DAD/iDAD; ELFI/BOLFI | Simulation allocation and physical measurement are different resources |
| Target-aware method/model selection | Partially exists: ModelTeller; target-specific ARG benchmarking | Learned performance does not certify the chosen method's biological assumptions |
| Shared-data error correction | Already exists: MSCquartets Holm–Bonferroni; confidence-sequence methods | Does not itself impose one global demographic parameter assignment |
| Arbitrary all-class biological joint compatibility and robust target stopping | Not found at this exact contract | Existing Commons G5/G6 address specific genealogy readouts, not unspecified raw-sequence channels |
| Whole biologically qualified sorter with proven cost dominance | Not found at this exact contract | No matched end-to-end superiority result was established |

## 3. Closest integrated systems and their exact limits

### 3.1 BayesFlow 2: closest general Bayesian workflow

[Kühmichel et al., BayesFlow 2, arXiv:2602.07098v2](https://arxiv.org/html/2602.07098v2), §§2–5, implements neural posterior, likelihood, ratio and point estimators; reusable model-implied targets; hierarchical/compositional inference; model comparison; sensitivity contexts; diagnostics and model-criticism interfaces. Its source is a user-defined joint simulator and prior, rather than a discovered biological model. Average calibration under that generative joint law is explicitly stated in Eq. 8. Simulation gaps can make a neural result depart even from the nominal model's Bayesian posterior; §§2.6–2.7 distinguish sensitivity and misspecification. The original's comparison section discusses estimator ensembles and shared summary networks. No inspected statement provides automatic theorem-qualified selection among species-network inference methods or complete identified sets.

The [official BayesFlow BED example, v2.0.11](https://bayesflow.org/v2.0.11/_examples/Bayesian_Experimental_Design.html), §§8.1–8.2, is more specific than the abstract's phrase “design optimization”: it explicitly treats **static, non-adaptive** design for a differentiable chemical reaction simulator. It jointly optimizes designs and a posterior network using a variational lower bound on information about the full parameter. That is real implemented design infrastructure, but does not demonstrate target-only, budget-optimal, adaptively certified genealogy measurements. Changing its utility or simulator is a possible engineering extension, not an established guarantee.

[ELFI, JMLR 2018](https://jmlr.org/papers/v19/17-374.html), §§2–3, already provides a simulator/prior/summary/distance DAG usable across rejection, SMC and BOLFI methods, cached reusable node outputs, parallel execution and interchangeable components. BOLFI actively chooses **simulator inputs** to economize computation. This is a close predecessor of method-flexible shared-model orchestration; it does not turn ABC distances into exact biological compatibility certificates.

[sbi reloaded, JOSS 2025](https://joss.theoj.org/papers/10.21105/joss.07754), pp1–3, supplies a multi-method neural SBI workflow with amortized and sequential algorithms, customizable simulation/training/sampling and diagnostics. The [official diagnostic guide](https://sbi.readthedocs.io/en/stable/how_to_guide/14_choose_diagnostic_tool.html) distinguishes prior-predictive average coverage/SBC, observation-specific conditional checks and model-misspecification checks. Training convergence and diagnostic power are limitations, not automatic certificates of uniform correctness. Its “sequential inference” concerns concentrating simulations for inference; it must not be silently equated with choosing fresh biological measurements.

### 3.2 Existing joint evolutionary-model platforms

[BEAST 2.5, Bouckaert et al. 2019](https://journals.plos.org/ploscompbiol/article?id=10.1371/journal.pcbi.1006650), “What is BEAST?”, “Model selection and model adequacy,” and “Validation, testing and quality management,” is an actual modular system of compatible submodels and posterior trees or supported time-network models. It integrates sequence, dates, fossil, phenotype and other data; packages include SNAPP, structured coalescent and AIM. Model comparison, simulation and posterior-predictive adequacy checking are already part of the ecosystem. Its quality-management section explicitly notes that distributed package validation had been largely informal. A platform's ability to host a new model does not prove an existing matching implementation or mathematical guarantee.

[LinguaPhylo, Drummond et al. 2023](https://journals.plos.org/ploscompbiol/article?id=10.1371/journal.pcbi.1011226), abstract/implementation sections, already makes a complete phylogenetic model human/machine readable, supports simulation and extensibility, and translates specifications to BEAST 2 analysis XML. This is direct prior art for a transparent model specification and backend interface.

[RevBayes, Höhna et al. 2016](https://pubmed.ncbi.nlm.nih.gov/27235697/) provides explicit user-composed probabilistic graphical models and inference; [P3, Höhna et al. 2018](https://pubmed.ncbi.nlm.nih.gov/29136211/) implements data- and inference-based posterior-predictive model-fit tests. The [official validation documentation](https://revbayes.github.io/developer/validation/) implements SBC over parameter draws from the generative prior. That average-under-prior property is not a per-source, all-time stopping guarantee. A shared graph prevents accidental independent nuisance fits only if the user encoded the intended dependence and source correctly.

### 3.3 PhyloNet: the biological forward layer is already substantially implemented

[Wen et al. 2018, PhyloNet](https://academic.oup.com/sysbio/article/67/4/735/4921127), “Models and Main Inference Features,” implements parsimony, likelihood/pseudolikelihood and Bayesian species-network inference from unlinked locus data. MCMC_SEQ jointly samples a network, gene trees, mutation-unit divergence/coalescence times, population mutation rates and inheritance parameters from sequence alignments. Cross-validation/bootstrap/information criteria address complexity in specified commands. Searches and posterior sampling are not exhaustive compatibility proofs. The paper itself cautions against treating unpenalized full-network likelihood as a generally consistent model-complexity procedure.

The specific [Zhu et al. 2018 biallelic network likelihood](https://journals.plos.org/ploscompbiol/article?id=10.1371/journal.pcbi.1005932), Methods pp3–7, analytically integrates genealogies on rooted binary temporal networks with an infinite ancestral branch. Each edge has theta=4Ne·mu; mutation-unit duration tau has coalescent duration 2tau/theta. Thus much of the independent-inheritance forward model already exists; known mutation calibration permits calendar conversion. Its hybrid Eq. 9 has binomial splitting weights choose(n,k) gamma^k(1−gamma)^(n−k), permitting mixed parental routes. It is **not** the shared-coin common-inheritance transition. Its topology prior rejects inadmissible directed graphs. Exact likelihood evaluation in this model is not polynomial-time on all networks.

| Contract aspect | Commons G5/G6 | What the inspected PhyloNet sources support |
|---|---|---|
| Genealogical process | Kingman within populations; independent or common hybrid inheritance | Substantial independent-inheritance overlap; common shared coins not found |
| Source graph | All finite binary temporal LSA, outer-labeled planar cut-child galled multigraph partners, parallel arcs allowed | Binary rooted network likelihood; exact cut-child/LSA restriction and parallel-bigon code support not audited |
| Time and rates | Contemporaneous tips; common calendar units; freely varying positive constant edge pair rates | Mutation/coalescent units and population parameters; calendar equivalence conditional on a declared calibration |
| Observations | Exact rooted quartet calendar laws (G5); specified finite genealogy/channel profiles (G6) | Unlinked aligned sequences or biallelic markers; latent genealogies integrated or sampled |
| Output | Displayed quartet-support Q and displayed split-union S; robust target fibers | Network/parameter/gene-tree posterior or heuristic estimates; Q/S projection requires correct displayed-target semantics |
| Guarantee | Accepted source-specific hand theorems at stated contracts | No inspected all-positive, all-size, exhaustive confidence-fiber stopping result |

Therefore **do not propose a new independent-MSC sequence likelihood merely because it is missing from an imagined diagram**. Reuse the existing forward computation where the model matches. If all required classes are implemented, the additional work may be only target-query and guarantee validation. For common inheritance, restricted graph enumeration, multigraph encodings or richer observation regimes, document the mismatch before building anything. “Not audited” is not “unsupported by the code.”

The MCMC_SEQ underlying study, [Wen and Nakhleh 2018](https://pubmed.ncbi.nlm.nih.gov/29088409/), was identity/abstract verified. Its original full text could not be retrieved here; a title-based PDF resolver incorrectly returned SNaQ and that result was rejected. Detailed claims above rely instead on the correctly retrieved PhyloNet software paper and Zhu primary methods.

### 3.4 Population ARG inference and query reuse

[SINGER, Deng, Nielsen and Song 2025](https://www.nature.com/articles/s41588-025-02317-9.pdf), Results/Discussion, takes phased whole-genome haplotypes and samples population ARGs. It uses approximate threading HMMs and SGPR, constant-population HMM assumptions and mutation-density time rescaling. The original reports empirical robustness and rank/credible-interval calibration, and downstream differentiation/introgression/local-tree analyses. It assumes infinite sites and cannot directly analyze genotype arrays; scalability is hundreds rather than arbitrary sample size. This is strong prior art for reusable uncertain genealogies, but an ARG generated by coalescence with recombination is not a reticulate species-demography source or a historical original-ID forcing model.

[tskit official introduction](https://tskit.dev/tskit/docs/stable/introduction.html) provides tree-sequence representation/query infrastructure; [tsdate official introduction](https://tskit.dev/tsdate/docs/latest/introduction.html) describes node-time inference conditional on an input genealogy and optional approximate time posteriors. Representing and querying a tree sequence does not supply full uncertainty over its topology or a universal latent-law estimator.

[Peng et al., 2025 ARG downstream benchmark](https://pubmed.ncbi.nlm.nih.gov/40048614/), Methods/Results/Discussion, compared seven estimators for PGS-history targets and found performance depends on sample size and time horizon, beyond generic ARG accuracy/scalability. It examined bias, coverage and error rates. It assumes known additive effect sizes and excludes environmental effects/interactions in its trait simulation; it does not establish psychological mechanisms or real trait histories from ancestry alone. This is concrete evidence for target-aware method evaluation, not a ready-made certified router.

### 3.5 The guarantee layer also has substantial prior art

[AutoBounds, Duarte et al., JASA 2024; inspected 2021 preprint](https://arxiv.org/abs/2109.13471), §§3–8 and Algorithms 1–2, takes discrete causal graphs, assumptions, observed information and estimands. It reduces admissible latent data-generating processes to polynomial constraints, searches target extrema, and produces sharp bounds when solved. Its anytime primal/dual procedure gives valid outer bounds and an epsilon-sharpness measure before completion; §7 separately handles sampling uncertainty. [Author software](https://github.com/duarteguilherme/autobounds) is an implementation. This closely subsumes the generic compatibility→target-bound→abstention idea. Its lossless discrete reduction does not automatically compile unknown-size continuous coalescent sources; sound numerical outer bounds require correct constraints and solver treatment. A population feasibility problem and a sampling confidence region remain different objects.

[LF2I, Dalmasso et al., EJS 2024, arXiv v10](https://arxiv.org/abs/2107.03920v10), Fig. 1, §§3–4/6 and Appendix F, implements separate statistic, critical-value and conditional-coverage diagnostic modules; [author code](https://github.com/lee-group-cmu/lf2i). Its central validity is finite in **observed sample size**, but approaches nominal coverage as simulation-training budget B′ grows under consistency assumptions for quantile/CDF estimation. Nuisance-uniform inversion needs an infimum over nuisance values; the paper separately evaluates approximate shortcuts. Do not advertise finite simulation diagnostics as an exact uniform calibration certificate.

[Universal inference, Wasserman, Ramdas and Balakrishnan 2020](https://pmc.ncbi.nlm.nih.gov/articles/PMC7382245/), and [inspected expanded arXiv v4](https://arxiv.org/abs/1912.11436v4), Theorem 1/sequential Theorem 11, already provide finite-sample confidence sets and confidence sequences using split/predictable likelihood ratios, with nuisance and null-optimization variants. Arbitrary training-side estimators are allowed; certified upper bounds on null likelihood can replace exact maxima. Correct normalized likelihoods and the stated independence/conditional structure are essential. This offers a potential route to wrap existing fitted biology, rather than inventing a generic guarantee layer. A neural likelihood approximation cannot be substituted without error control.

[Robust universal inference, Park et al.; inspected arXiv:2307.04034v4](https://arxiv.org/abs/2307.04034v4), Introduction and later constructions, extends this direction to confidence sets for divergence projections under misspecification, with exact or approximate guarantees under stated conditions. It does not turn a best-fitting wrong source into the true genealogy. Its projected-distribution target is different from an exact historical target.

### 3.6 Design and routing precedents

- [DAD, Foster et al., ICML 2021](https://proceedings.mlr.press/v139/foster21a), original §§2–3: implemented learned sequential experiment policy, prior/simulator, information-bound objectives and fast deployed actions. [iDAD, NeurIPS 2021](https://proceedings.nips.cc/paper_files/paper/2021/hash/d811406316b669ad3d370d78b51b1d2e-Abstract.html) extends to implicit likelihoods. Learned objective optimization is not a matched minimax genealogy cost theorem or an all-time confidence certificate.
- [PhyDesign, López-Giráldez and Townsend 2011](https://link.springer.com/article/10.1186/1471-2148-11-152), Input/Results: implemented locus prioritization by time epoch using alignments and a supplied reasonably known ultrametric tree or rate vectors. The paper explicitly says its informativeness profiles omit homoplasy noise. This is a useful source-dependent measurement heuristic, not universally optimal locus/copy/control substitution.
- [ModelTeller, Abadi et al. 2020](https://pubmed.ncbi.nlm.nih.gov/32585030/), Methods/Results: implemented machine-learning substitution-model selection optimized for branch-length accuracy, rather than assuming best statistical fit gives best reconstruction. It is task-specific empirical routing, not a general proof-qualified portfolio.
- [SATzilla, Xu et al. 2008](https://doi.org/10.1613/jair.2490), primary article identity/abstract evidence, establishes automated solver portfolios/runtime prediction in SAT. The original PDF fetch failed here; no new theorem audit relies on it. A selector's performance model does not independently certify underlying statistical assumptions. No biological guarantee follows from importing a portfolio pattern.
- [Zhang and Xu, Certified Task-Conditioned Active Observability, arXiv:2609.28520v1](https://arxiv.org/abs/2609.28520), §§2–4, is a very recent **unreviewed preprint**, with selected original pages inspected, not independently proof-audited. It studies a finite candidate bank with known controlled future models and fixed task labels, quotienting, adaptive distinguishing costs, martingale certification and abstention. This is an especially close generic architecture precedent. The bank/known kernels are supplied; obtaining a complete biologically faithful bank is outside that premise. Its reported physical stress audits do not validate coalescent networks, and public reproducible implementation was not established here.

## 4. Recommended reuse route

**Start with an existing domain model and a narrow target, not with a new universal sorter.** The following is a recommendation, not an implemented pipeline:

1. For **unlinked species-network sequence data under independent inheritance**, first assess PhyloNet MCMC_SEQ or its biallelic integrated likelihood. Use SNAPP for the matched tree subcase. Keep a single declared source, mutation/sampling model and calibrated units. For a direct level-1 or tree-of-blobs target with suitable gene-tree input, assess SNaQ/MSCquartets instead of insisting on reconstruction of every latent gene tree.
2. For **linked population haplotypes and ARG targets**, use SINGER plus tskit-compatible queries. Do not transplant these outputs into the species-network calendar theorem without an actual source/channel equivalence argument.
3. For **simulator-only inference or repeated multi-target use**, BayesFlow 2 is the closest general workflow to reuse. ELFI/sbi are alternatives depending on simulator cost, differentiability and desired estimators. Cost comparisons must include simulation/training, fitting, querying and new biological data; amortization is not free.
4. For **a finite discrete compatibility model**, inspect AutoBounds before writing an identified-set optimizer. For reliable simulator-based intervals, inspect LF2I and its calibration limitations. If exact or certified likelihood computations are available, assess universal/e-process inference rather than assuming a wholly new confidence wrapper is required.
5. Add a **small source-qualified interface only where a mismatch is demonstrated**: model/units/target declarations, shared-data provenance, verified input admission, output guarantee type and uncertainty status. This could be worthwhile integration; configuration/provenance alone is not a research novelty result.

## 5. What could still require genuine biological mathematics?

The following are **prospective questions**, not additional G gates or assigned closure requirements:

- Does the selected, calibrated **sequence observation channel** preserve identification of the specific Q/S target on the precise admitted source class, including common inheritance where intended? Existing generic target factorization and neural posterior training do not answer this. Nor does genealogy-level G5 automatically answer it. Prior logDet/network-identifiability results may already solve restricted versions, so specify the regime before posing a new theorem.
- Can existing exact likelihoods or validated simulators be converted into **effective, complete joint source/target outer sets** at the needed class, with certified numerical approximation and nuisance handling? Much independent-MSC forward computation is already available. The unbounded-class, multigraph, shared-coin or finite-read closure aspects require separate checking, not a blanket claim that all inference machinery is absent.
- Can a chosen biological experiment menu attain a **matched target-specific resource optimum** under the same observation error/dependence regime? Learning a good design, theoretical information gain, biological feasibility and minimax cost are separate claims. Historical full hybrid forcing needs an accessible actuator, not just a simulated switch.

Answering one of these could be useful source-specific work. Merely naming all three, building a registry or invoking a generic inference theorem does not settle them.

## 6. Output and composition discipline

An actual sorter should distinguish:

1. **Posterior estimate:** conditional on model/prior and computational approximation.
2. **Confidence/outer target set:** with a declared coverage event, channel, nuisance and dependence contract.
3. **Exact compatibility or impossibility certificate:** a verified witness or exhaustive/certified infeasibility result.
4. **Abstention:** insufficient separation, incomplete computation or failed admission, each identified separately.

Failed model-fit tests, an OOD score, absent MCMC samples and exact source inconsistency are not interchangeable. Local quartet fit and mutually compatible splits need not imply one numerical demographic source. [MSCquartets 3.3 official manual, HolmBonferroni](https://cran.r-project.org/web/packages/MSCquartets/refman/MSCquartets.html#HolmBonferroni) already corrects dependent-quartet multiplicity and explicitly warns that its tests do not enforce cross-quartet edge-length relationships. The current package also implements NANUQ, TINNiK, NANUQ+ and ECToBlob; draft/forthcoming references in its manual must retain their status.

**Reasoned composition consequence:** if one valid joint source confidence set covers the true shared source on a simultaneous event, all target projections of that same set inherit that event. This is a standard pushforward argument, not a new theorem here. Selecting a method after viewing its errors, pooling overlapping quartet pseudo-replicates, taking an uncorrected maximum over favorable tests, or replacing exact likelihoods by uncontrolled neural approximations does not automatically preserve it. Honest splitting, predictable conditional likelihoods or validated simultaneous bounds are existing routes. Whether a concrete model supplies their premises is the substantive check.

## 7. Adversarial value/novelty assessment

| Claim | Assessment after this search |
|---|---|
| “A universal latent-law layer is a new idea” | Demoted: joint generative phylogenetics and reusable ARG posterior inference already exist |
| “Getting the target without reconstructing the whole hidden model is new” | Demoted: integrated latent likelihoods, direct quartet targets and AutoBounds are direct precedents |
| “Adding uncertainty, incompatibility and abstention creates the new architecture” | Demoted: identified-set solvers and finite/anytime inference already supply substantial machinery |
| “Bayesian tools have no relevant rigorous guarantee” | Incorrect: some generic frequentist machinery can wrap arbitrary fitted estimators; the biology/numerics must meet its premises |
| “All forward biology must be implemented from scratch” | Incorrect for the matched independent-MSC sequence/SNP model; verify and reuse |
| “A modular platform automatically implements Commons G5/G6” | Unsupported: source/readout and guarantee equivalence must be checked |
| “A sorter is useful even if its architecture is established” | Plausible engineering value: reproducibility, correct contracts and multi-target reuse; benefit needs a concrete comparison |
| “The sorter is better than direct target inference” | Unestablished: compare matched targets, data, risk, compute and measurement budgets |
| “No one has done the whole system” | Not justified by a bounded search; only exact-contract implementation was not found |

## 8. Evidence, coverage and completion limits

Search protocol and log accompany this note. We used PubMed for biological identities/abstracts, primary publisher/preprint texts, official documentation, a broad ranked alphaXiv pass and targeted query expansion. Twenty bibliography entries were matched by the citation-audit tool; it flagged no retractions in that batch. That is an identity/status check, not proof verification or a comprehensive integrity guarantee.

Full body of the 2025 ARG downstream benchmark was recovered through the rights-eligible native PMC tool in two chunks (54,074 characters). BayesFlow 2 full HTML and selected original PDF pages, PhyloNet software full article, Zhu SNP selected original PDF methods, LF2I/AutoBounds/universal/robust inference selected original pages, DAD and sbi software originals were inspected. RevBayes/P3 claims use primary abstract evidence plus official documentation; native/PubMed or PMC full retrieval was unavailable for some other software papers. Publisher full texts often supplied a permitted alternative. No access denial was bypassed.

Important retrieval errors were caught: the PhyloNet sequence-study title resolver returned a different SNaQ paper and was rejected; one PGS PDF URL and an alphaXiv PMC fetch failed before native recovery; some Rice wiki/RevBayes pages and Oxford redirects failed. Software was neither installed nor executed; no cross-package benchmark, numerical certified solver replay, posterior convergence audit or independent theorem proof was performed. Current documentation demonstrates declared APIs/capabilities, not an executed end-to-end system.

The search is non-exhaustive. Broad PubMed name queries collided with unrelated “Singer”/“Relate” records and were narrowed; top-result samples were not treated as complete databases. Direct code review of all supported graph encodings, every published ARG framework, all robust/partial-ID packages, every formal proof/algorithm-selection system and all field indexes was not undertaken. Exact matching implementations or guarantees could still exist elsewhere. The recommendation is bounded reuse plus contract audit, not a historical-priority conclusion.

## 9. Source-local interpretation of the Commons results

The accepted [G5 review at fefa2deb](https://github.com/Sodelin/Research-Commons/blob/fefa2deb301e8ea34a23113db7d5c3a8ec39f37b/research/2026-10-01-dot-g5-independent-review-2005z/REVIEW.md) and [G6 proof at 883a9315](https://github.com/Sodelin/Research-Commons/blob/883a9315f893e93211c64de344bac3dc365a3e18/research/2026-10-01-g6-effective-certification/PROOF.md) remain source/readout-specific mathematical contributions at their stated contracts. This comparison neither grants them a raw-sequence estimator nor removes their assumptions. Established generic architecture reduces the novelty of packaging the program, while leaving the exact source-specific claims to be assessed against matching biological prior theorems. No new completion prerequisite is introduced.
