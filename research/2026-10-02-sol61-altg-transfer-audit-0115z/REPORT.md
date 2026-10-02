# Alt-G alternatives: Samuel ownership and infinite-history prior-art attack

**Audit date:** 2 October 2026 UTC  
**Contributor:** OpenAI Codex, Sol 6.1  
**Mode:** bounded rapid evidence map and closest-result audit, not an exhaustive novelty review  
**Scope:** Samuel/Alexander genomic-to-organism transfer, ownership/path lifting, finite-horizon ancestry and stochastic observational equivalence. No new theorem, simulation, biological computation, implementation or app was developed in this audit.

## Decision first

The general Alt-G proposals are not fresh mathematical research directions merely because they receive new labels. Target identification, controlled lumping, stochastic composition, experiment comparison and finite-prefix monitoring are established mathematics. Several source-specific Samuel bridges are also already completed.

The strongest consequential distinction is between:

1. the same **realized copy history** with different hidden ownership;
2. the same **observation probability law** under an explicit reproduction/measurement process;
3. an event with positive probability, as opposed to an exceptional infinite history;
4. finite-horizon observable statistics, as opposed to Alexander's whole-history IAP.

The current constrained ownership theorem establishes item 1 and the arbitrary finite ownership-prefix obstruction. It does not establish items 2 or 3. The existing B06 raw-draw construction already handles a meaningful version of item 4: finite marker histories and almost-sure IAP belong to one actual process, with conditional geometric ancestry-resolution bounds.

**Smallest useful completion:** close B06's explicitly missing actual-stream fixation-event-to-fixationValue adapter. This would finish a precise comparison already promised by the source packet. Its mathematical basis is classical absorption and measure continuity; call it source integration/formal verification, not a new general theorem.

**Smallest potentially substantive new research question:** decide whether the constrained ownership/IAP ambiguity survives a specified finite-locus Mendelian reproduction and observation law, with a positive-measure statement or actual equality of observable laws. The first admissible step is source-law selection and an equivalence/support audit, not simulation of the eight-lane witness. No such stochastic result is claimed here.

## 1. Source state and what has actually been checked

Samuel main was read through the GitHub connector during this audit and resolves to [e2502c82ab9a77c00543932f775a71e5374221f7](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/commit/e2502c82ab9a77c00543932f775a71e5374221f7). All Samuel links below use that immutable revision.

The 30 September recovery and connection maps were used as dated navigation aids. Current source artifacts were read independently. Existing HG2/HG3 and PG/SG audits were reused for their classical source gates rather than duplicated. The audit did not compile Lean, rerun a probability experiment or independently reproduce hosted CI. “Completed” below means the inspected packet contains the stated endpoint and records scoped verification evidence; it does not mean a fresh kernel replay or receipt-integrity recheck was performed here. SOURCE-MANIFEST.json records the 17 successfully read Samuel artifacts and their Git blob identities.

| Bridge | Actual completed endpoint | Material limit |
|---|---|---|
| Realized genome copies → ambiguous diploid ownership | [genome-pedigree README](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/genome-pedigree/README.md): eight-copy complete realized graph, exactly two copies per organism, four organisms/generation, two distinct parents and two children, weak connectivity, opposite whole IAP/specieslike/inspecies, and arbitrary finite ownership-prefix agreement | Deterministic inverse obstruction. No equal sequence likelihoods, standard-meiosis law or positive-probability infinite witness |
| Exact genome edge image → organism ancestry | PairingCore.edge_exact_image and exact_edges_do_not_lift_paths establish both the edge interface and a two-edge failure of ancestry reflection | Different genomic witnesses at successive pedigree edges need not join into one genomic path |
| Supplied owner map → IAP/REF/cluster transfer | [WongPedigreeBridge.lean](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/real/WongPedigreeBridge.lean): IAP/REF equivalence under onto finite fibres and ancestry equivalence away from fibres, for every representative pair of distinct owners | A hypothesis-driven transfer theorem, not reconstruction of ownership from DNA |
| Cluster and maximality transfer | specieslike_descends; specieslike_iff with connected fibres; maximal_saturated_iff | Saturated candidate sets matter. Ordinary diploid copies need not satisfy connected-fibre assumptions; unrestricted rich-history maximality is different |
| IAP robustness | iap_iff_of_finite_ancestry_errors | Finite ancestry-discrepancy sets per source organism, not simply a finite number of edited edges |
| Ownership measurements → IAP in delayed family | [owner-observations README](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/owner-observations/README.md): unbounded informative odd-generation sampling iff identification; even-only full ownership observation fails; one query after a known switch bound suffices | Exact static metadata in one delayed-split family. Infinite-record identification is not a uniformly terminating finite decision procedure |
| Finite-cohort ancestry → whole IAP | [ExtinctionPedigree.lean](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/feedback-speciation/pure-induction-ancestry-v2/ExtinctionPedigree.lean): global_iap_iff_late_sync, plus all/none cohort persistence and extinction-permitting examples | Finite past, occupied cohorts, one-generation edges and parent coverage are assumed. This is not arbitrary finite-network → infinite-biosphere transfer |
| Actual raw process → marker law and IAP | [B06 result and scope](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/feedback-speciation/pure-induction-ancestry-v2/RESULT-AND-SCOPE.md): same Fin14 raw draws generate parent/homologue choices and marker paths; all finite path laws match; almost-sure IAP; conditional non-resolution bound (2365/2401)^k | marker_barrier_and_iap is a conjunction with the finite fixation statistic. No actual infinite-stream fixation-event measure identity is exported |
| Controlled predictive/stochastic representation | [PredictiveState.lean](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-problems/time-self-reference/predictive-memory/PredictiveState.lean), [StochasticAbstraction.lean](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-problems/time-self-reference/predictive-memory/StochasticAbstraction.lean): all finite action/transcript preservation under exact kernels and policy factorization | Classical substrate. Joint next-state/measurement law is required; separate transition/emission marginals are insufficient. Persistent sensor memory belongs in the state |

No finite NANUQ quartet/displayed-split endpoint in the inspected maps supplies organism ownership, a future reproductive process or a complete infinite-IAP decoder.

## 2. Primary-source attacks and exact surviving residue

### 2.1 Alexander's definitions and questions must remain separate

[Alexander 2013, Biologically Unavoidable Sequences, §6](https://arxiv.org/html/1212.0186v2#S6) concerns labelled infinite paths, universal avoiders, ordinal characterizations and unavoidable words. It supplies no genomic likelihood or ownership inverse theorem. Alt-G work cannot close those questions by merely replacing a graph representation.

[Alexander 2013, Infinite graphs in systematic biology, Proposition 6](https://arxiv.org/html/1201.2869) already supplies cofinite descendants inside an inspecies. A new note should not claim that cofinite-descendant behavior itself is a discovery.

[Alexander 2026, Definitions 1–4 and §3.1](https://arxiv.org/html/2602.05274v1#S3.SS1) defines IAP on an infinite past/present/future biosphere, explicitly distinguishes genealogical from genetic ancestry and labels its biological motivation informal. Its finite-cohort all/none argument is conditional on eventual synchronization. The source's maximal-cluster question and constraints remain different from statistical species delimitation.

**Attack verdict:** an unrestricted finite observation → infinite IAP claim fails at the source semantics. A conditional generational completion is already implemented in ExtinctionPedigree. The remaining scientific content is a justified reproduction/continuation law or a genuinely weaker observation contract, not a generic limiting argument.

### 2.2 Wong gives an encoding, not ownership reconstruction

[Wong et al. 2024, Genome ARGs, Fig. 1, Appendix D](https://www.pure.ed.ac.uk/ws/portalfiles/portal/458588307/iyae100.pdf) defines haploid genomic nodes and realized interval inheritance, shows the pedigree separately, and allows additional node information. Cell-level events, omitted intermediate genomes and compressed histories complicate event-to-organism maps.

**Attack verdict:** the infinite eight-copy record is an extension of a finite gARG interface. It is legitimate only when ownership is explicitly omitted from the common observation. “Wong ARGs cannot encode individuals” would be false. Exact topology/image edges do not by themselves discharge the Samuel owner-transfer ancestry premise.

The [official tskit data model](https://tskit.dev/tskit/docs/stable/data-model.html#individual-table) has node-to-individual associations and individual parent IDs. Fully populated ownership/pedigree fields are a different, richer observation from the counterexample's record.

### 2.3 Thatte already settles the potential-parent pairing version

[Thatte, Reconstructing pedigrees, Definitions 2.1–2.2 and Theorem 5.13](https://arxiv.org/html/1008.0153v3) uses a sequence pedigree with indegree zero or two and a diploid pairing determined for non-extant vertices by shared offspring. Extant pairing is supplied. Thus the potential-parent structure already determines the other pairings. Theorem 5.13 derives combinatorial invariants from equality of all alignment-length distributions under its recombination-mutation model, with a small-recombination restriction; it is not a universal pedigree-identification theorem.

**Attack verdict:** a broad “haploid genealogy leaves pairing arbitrary” proposal is already defeated. The Samuel eight-chain graph has one realized transmitting predecessor per copy and omits unused potential homologues. That is exactly why it escapes Thatte's determination rule. The remaining question must stay in the realized-transmission interface or explicitly account for the extra potential edges.

### 2.4 Kirkpatrick already supplies a real likelihood-equivalence test

[Kirkpatrick, Non-Identifiable Pedigrees and a Bayesian Solution, §§2–4, Theorems 3.1–3.3 in the HTML version](https://arxiv.org/html/1602.08183) characterizes likelihood equality for all genotype data and recombination parameters through proper isomorphism of reduced pedigree HMMs. It also gives non-identifiable examples and restricted identifiability results using necessary edges and leaf-labelled discrete Wright–Fisher pedigrees.

**Attack verdict:** reduced-HMM equivalence is the closest already-developed attack on a proposed statistical owner adapter. The Samuel common realized history is not a substitute for this quantification. Conversely, Kirkpatrick's finite typed-individual likelihood examples do not automatically produce infinite constrained pedigrees with opposite IAP. A future claim must retain the sampling labels, recombination model, shared parameters and generational restrictions; do not silently weaken the positive theorem or upgrade its finite examples.

### 2.5 Genetic/genealogical separation is established random-pedigree theory

[Gravel and Steel 2015, §§2.1–2.2, Proposition 2.1](https://www.math.canterbury.ac.nz/~m.steel/Non_UC/files/research/ghosts.pdf) gives high-probability genealogical ancestors of everyone with no genetic contribution to present individuals under a random biparental model and recombination. This directly defeats novelty of the broad genetic-versus-genealogical separation.

[Chang 1999](https://www.stat.yale.edu/~jtc5/papers/CommonAncestors/AAP_99_CommonAncestors_paper.pdf) supplies the random two-parent finite-population ancestor-time baseline. Its full PDF reader failed in this pass; original-source indexed text and Alexander's/Gravel–Steel's precise use were inspected. No additional Chang theorem is promoted to an independently full-text-checked premise.

[Derrida, Manrubia and Zanette 2000, §§II–IV](https://arxiv.org/html/physics/0003016) studies ancestor repetitions and overlap in a panmictic closed biparental population, with constant-size and growth models. It is adjacent genealogy theory, not a likelihood-equivalence theorem or a justification of unrestricted future completions.

**Attack verdict:** a common finite present-day ancestor point, a large-population asymptotic, one founder's fate and whole infinite-history IAP are different statements. A model can make IAP almost sure without making any finite DNA record an exact decoder across an enlarged model class. Universal dissemination of every lineage is especially suspect: the inspected feedback-speciation packet itself says that assumption excludes ordinary lineage extinction and has probability zero in the standard fixed-size independent two-parent process.

## 3. The generic Alt-G layer is largely subsumed

The already completed HG2/HG3 audit inspected Kemeny–Snell §6.3, Larsen–Skou's probabilistic testing report, Fritz's sufficiency theory and weighted-automaton equivalence. Those findings are reused. No new attribution is attached to their classical core.

| Proposal | Closest result already settling the general version | Source-specific question that could still matter |
|---|---|---|
| Alt-G1: target-preserving translations | Classical target identification on observation fibres; statistical sufficiency/reconstruction when that stronger contract is intended. [Fritz 2020, Theorem 14.5](https://arxiv.org/html/1908.07021v8) supplies a reconstruction-kernel criterion under its hypotheses | Which ownership/history/interval data can be omitted while preserving a named Alexander predicate in an admitted biological class? Exact edge image already fails |
| Alt-G2: dynamics, interventions and history | Strong lumpability and controlled behavioral equivalence; Samuel's exact kernel/policy lemmas; [Rubenstein et al. 2017, Definition 3/Theorem 6](https://arxiv.org/html/1707.00819) formalizes intervention-respecting exact causal transformations | Instantiate the joint reproductive/measurement/action law. A historical parenthood edge is not a currently available intervention; different source actions need an actual map |
| Alt-G3: finite observations → infinite-history targets | Finite-prefix monitorability; project ExtinctionPedigree and B06; exact all-finite law → trajectory-law uniqueness by Ionescu–Tulcea | Separate finite sample length from equality of every finite-dimensional law. Hidden IAP also needs measurability from the retained process or a source-law bridge |
| Alt-G4: minimum added observations | Established sufficiency/test distinguishability/measurement design; the current odd-generation mask and known-switch one-query theorem already settle one concrete family | Specify costed lawful metadata measurements and source restrictions. No general optimum follows from that elementary delayed-split result |
| Alt-G5: uncertainty through composed adapters | Established stochastic composition, experiment comparison and quantitative bisimulation/trace bounds | Bound actual mutation, ownership, sampling and continuation-model errors jointly. A per-step finite-horizon bound may become vacuous at infinite time |

Two particularly decisive already-existing theorems are:

- [Etienne Marion, 2025 preprint, inspected v5 of 17 March 2026, Theorem 2.11](https://arxiv.org/html/2506.18616v5): measurable history-dependent Markov kernels determine a unique infinite trajectory kernel with the prescribed finite restrictions. The [pinned Mathlib Traj.lean source](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Probability/Kernel/IonescuTulcea/Traj.lean) is already available at Samuel's declared dependency revision. This settles the general construction/uniqueness substrate. It does not say a bounded observed prefix identifies an unobserved genealogy.
- [Bian and Abate 2017, Theorems 4.1–4.3](https://arxiv.org/html/1701.04547): approximate bisimulation implies a tight finite-trace bound 1−(1−ε)^k; trace equivalence need not imply bisimulation. Thus composing small local errors into a useful infinite-tail IAP bound needs an additional source-specific argument. Taking k to infinity does not deliver one.

[Bauer 2010, Definitions 1–2 and §4](https://arxiv.org/html/1006.3638) already distinguishes good/bad prefixes and infinite-word monitorability. The delayed-split negative-answer issue is an application of that distinction. One-sided eventual violation detection and finite positive certification of IAP are not the same task.

**Important inference:** equality of every finite joint observed transcript law determines equality of the observable process law on the product sigma-algebra. It gives equality of measurable targets of that observable process. It says nothing by itself about a hidden organism-IAP target that fails to factor through the observations. Equality of separate time marginals is weaker still.

## 4. Assumptions that are scientifically useful, and assumptions that make the task hollow

### Useful finite-state starting classes

1. **B06's existing finite marker/parent raw process.** Its reproduction and pulse law are explicit; parent and marker paths share randomness. It is the cleanest source-integration class.
2. **Finite cohorts with a stated parent-choice law.** Track descendants of a named organism, extinction and establishment, not universal survival. Recurrence/mixing assumptions should come from the actual law. Parent coverage and one-generation edges make all/none cohort status persistent.
3. **Finite pedigree HMMs with fixed typed individuals.** Use Kirkpatrick's transition/emission equivalence and Thatte's mutation/recombination restrictions before introducing a new equivalence procedure.
4. **A finite-state ownership schedule.** Useful as an exploratory mathematical class only when its transition rules and observation semantics have biological interpretation. Randomizing between M1 and M2 while forcing the same eight lanes is not automatically a Mendelian experiment.
5. **Exact individual metadata with restricted missingness.** This corresponds to an existing real data representation. To call a cost optimum biological, specify the actual archive, persistent copy matching, phasing errors and feasible specimen observations.

### Useful infinite-source starting classes

- Infinite discrete-generation pedigrees with finite birthdate sublevels, finite child sets and explicit survival/parent-coverage conditions.
- Countable cohort/history processes with measurable kernels and a countable-product law; standard Borel structure is a useful route when regular conditioning is needed.
- Spatial/structured reproduction with persistent migration regimes, if a primary source supplies its kernel and establishment/extinction behavior.
- Infinite streams of finite-locus observations, only with a genuine shared reproduction and measurement law and a declared target. All finite cylinder equalities are meaningful here; one common exact infinite realized sequence need not carry positive measure.

### Assumptions that require special skepticism

- A known last possible split time: useful and sufficient in the existing family, but finite observations cannot establish it.
- Arbitrary remote future modifications: valid for a deterministic impossibility class, often too permissive for a stochastic biological claim.
- Onto ownership from a sampled finite ARG to the infinite biosphere: generally unavailable.
- Every genome representative reflecting every organism ancestry path: strong and often biologically false.
- Matching transition and emission marginals while forgetting their dependence.
- “Independent loci” without a linkage/ascertainment/readout model.
- A forced forever-balanced no-recombination transmission schedule: support must be checked; finite positive probability does not imply positive probability of its infinite continuation.
- A continuation law that builds the desired IAP outcome into its definition: it supplies an assumption, not observation-based identification.
- Treating neutral marker fixation or a reproductive-isolation statistic as permanent genealogical separation.

## 5. Ranked next targets and completion criteria

### Rank 1: the smallest consequential closure, not a novelty claim

**Target:** actual raw-stream eventual marker fixation has probability FiniteEpigenetic.fixationValue true = 1/14, under precisely B06's existing pulse/ordinary law, and the same actual process has almost-sure IAP.

Source reading supports the registration: [FiniteEpigenetic.lean](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/feedback-speciation/pure-induction-ancestry-v2/FiniteEpigenetic.lean) contains absorbing boundaries, a uniform terminal bound and the finite probability limit. [PureInductionAncestry.lean](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/feedback-speciation/pure-induction-ancestry-v2/PureInductionAncestry.lean) supplies finite path law identity and explicitly excludes the infinite-event identity.

**Why consequential:** it replaces a finite-statistic-plus-IAP conjunction with a genuinely same-process event comparison, avoiding a recurrent overstatement.

**Already-known mathematical route:** absorption and continuity of probability, plus the existing source realization. No new theorem was developed during this audit.

**Complete only when:** the raw event and indexing are specified and measurable; it is linked to the actual count map; the absorbing semantics and pulse offset agree; its measure identity and the existing IAP endpoint are checked at one source pin; the result retains the current reproduction restrictions. No new simulation is needed to decide whether this is a classical adapter task.

### Rank 2: the smallest candidate substantive Samuel research target

**Target:** under one explicitly sourced finite-locus Mendelian reproduction/measurement law, determine whether omission of diploid ownership permits different conditional whole-history IAP outcomes on a non-null set of observations, or construct two admitted laws with identical complete observable process laws and different IAP probabilities.

These are alternative contracts, not interchangeable claims. A nontrivial conditional IAP posterior under one law differs from two parameterized laws being observationally equivalent. A finite-horizon overlap event differs from infinite process-law equivalence.

**Before theorem work:** fix cohort size/demography, sex/selfing policy, offspring law, genome/locus coverage, recombination, mutation, copy/individual IDs, retained metadata and initial typed owners. Attack the resulting finite observation mechanism using Thatte and Kirkpatrick; check whether positive recurrence already makes IAP almost surely constant.

**Why this is more informative than extending the eight-lane construction:** it tests the only major new statistical claim the deterministic packet explicitly leaves open, and rejects exceptional-history rhetoric.

**Complete only when:** the chosen law is source-faithful and nondegenerate; the actual observation-law identity or non-null conditional ambiguity is proved; IAP is measurable; probability support and all infinite quantifiers are discharged; ownership, sex and degree constraints are accurately retained or explicitly changed; a matching primary-prior-art update is completed. If the law forces IAP almost surely, report that informative negative outcome rather than inventing a null-event counterexample.

**Status:** source-law selection still required. Not ready for implementation or a novelty claim.

### Rank 3: a source-specific finite-horizon certificate with continuation error

**Target:** a finite ownership/parent observation certifies a named organism's future all/none ancestry with an explicit continuation-model error bound, under a new justified source law.

B06 already supplies conditional geometric resolution for its specified process; owner-observations already supplies the bounded-switch exact query. Repeating either is not frontier movement. A new result would need a materially different biological restriction, informative measurement channel or sharp attainable cost/error tradeoff.

**Complete only when:** the event being certified is stated, the allowed observation cost is explicit, future error is conditional on the full measured history, and model uncertainty/rare permanent barriers are not omitted. Whole-population IAP requires further quantifiers over all organisms; one organism's finite certificate does not close that target.

### Not ranked as new research targets

- A new generic target-factorization theorem
- Another generic lumpability or Markov-category composition library
- A bare finite-to-infinite law extension theorem
- A general “genetic ancestry differs from genealogy” example
- A claim that one extra ownership bit solves arbitrary pedigree/IAP inference
- Unrestricted copying of probabilistic-testing process states into a biological experiment
- A broad cross-field/fractal analogy without source, observation, action and target maps

## 6. What would make an Alt-G result complete?

A complete source-specific Alt-G packet must establish all applicable items:

1. **Source identity:** exact primary model and current artifact pin, with admitted class/nuisance parameters.
2. **Observation identity:** actual joint experiment, retained labels/history, dependent noise and omitted data.
3. **Target identity:** IAP, specieslike, inspecies, maximal saturated cluster, finite ancestry or event probability; horizon and population are fixed.
4. **Map and theorem:** target preservation or calibrated error is proved under hypotheses actually discharged by the source.
5. **Actions:** interventions and policy class have source semantics and are feasible when an empirical experiment is claimed.
6. **Infinity:** measurable trajectory law and target event; continuation assumptions; countable quantifiers; extinction/survival support.
7. **Statistical strength:** deterministic collision, same-law nonidentifiability, positive-measure ambiguity and finite-sample lower bound are labelled separately.
8. **Cost/optimality:** an admitted observation menu, cost objective and matching upper/lower claims if “minimum” is used.
9. **Prior art:** precise nearest result, what it subsumes, retained hypothesis differences and bounded novelty language.
10. **Evidence:** written/source argument, formal verification and empirical validity remain distinct; a source file is not a fresh compilation receipt.

Current completion of a restricted bridge does not reopen or invalidate its accepted theorem. It does prevent that bridge from being advertised as a larger completed scientific answer.

## 7. Bounded search ledger and access gaps

**Date window:** this pass used sources and current artifacts retrieved 2 October 2026 UTC. It was a targeted rapid evidence map, not a review search with global recall guarantees. English-language mathematical papers and official source/software artifacts were prioritized. No datasets, personal records or scientific hypotheses were uploaded to a third-party research service.

### Direct-source retrieval

- Alexander 1212.0186v2, 1201.2869 and 2602.05274v1: full HTML available; exact definitions/propositions and question sections inspected.
- Wong DOI landing reader: failed. PMC mirror returned a CAPTCHA/interstitial; no CAPTCHA was solved. University of Edinburgh's author/institutional PDF worked; Genome ARGs/Fig. 1/Appendix D inspected.
- Thatte 1008.0153v3: full HTML; Definitions 2.1–2.2, Theorem 5.13 and discussion inspected.
- Kirkpatrick 1602.08183: full HTML; likelihood/HMM assumptions and Theorems 3.1–3.3 inspected. Numbering differs from the older project synopsis.
- Gravel–Steel author PDF: worked; Proposition 2.1 and explicit reproduction/recombination assumptions inspected.
- Chang original Yale PDF variants: direct full reader failed. Primary indexed excerpts were retrieved. Do not count this as full-theorem text verification.
- Derrida institutional PDF: failed; arXiv physics/0003016 HTML worked. Adjacent evidence only.
- Bauer 1006.3638, Bian–Abate 1701.04547, Rubenstein et al. 1707.00819, Marion 2506.18616 and Fritz 1908.07021v8: direct full HTML worked; stated locators inspected.
- Official tskit data model: worked; node/individual/parent metadata inspected.
- Mathlib Traj.lean at Samuel's pinned dependency: GitHub connector worked.
- Blackwell publisher/Project Euclid direct text: failed/interstitial. Classical pointer only, not a newly audited precise premise.
- Kemeny–Snell/Larsen–Skou/weighted-automata detailed audit: reused from the existing HG2/HG3 report; not claimed as fresh rereading of every primary paper.

### Web candidate-search passes

The exact discovery phrases included:

- “A general and efficient representation” “genome” Wong 2024
- “Gravel” “Steel” “2015” ghost ancestors
- Chang recent common ancestors all present day individuals 1999 pdf
- Derrida Manrubia Zanette genealogy ancestors 2000 identical pdf
- probabilistic bisimulation lumpability finite trace equivalence Markov chain original paper
- Ionescu Tulcea theorem uniqueness probability infinite trajectories transition kernels primary notes
- controlled Markov abstraction approximate simulation finite horizon safety error Abate original paper
- Blackwell comparison experiments deficiency distance composition 1953 1951 primary paper
- “pedigree” “ownership” “IAP”
- “pedigree” “identical ancestor” “non-identifiable”
- “diploid” “pairing” “realized transmission”
- “pedigree” “genealogical” “path lifting” genome
- “pedigree” “finite observation” “infinite” ancestors identification
- “ownership” “ancestral recombination graph”

These were first-page ranked web searches without domain/date filters or exhaustive pagination. Batched response counts are not reliable per-query database yields; none are presented as review-screening statistics. Exact joint-phrase passes mainly returned irrelevant or adjacent records rather than a theorem matching the full Samuel conjunction. That is weak negative evidence, not a priority certificate.

### Artifact retrieval corrections

The requested GENOMES-AND-PEDIGREES.md is at repository root, not inside research/genome-pedigree. WongPedigreeBridge.lean is under real, not inside the bridge explanation folder. Several guessed dependency paths returned 404; the B06 dependency files were then located directly within pure-induction-ancestry-v2. These corrected retrievals were read. No missing-path response is treated as a missing theorem.

### Unsearched or incompletely searched

MathSciNet/zbMATH subscription indexes, a complete forward-citation graph, all pedigree-reconstruction papers, all finite-sample genetic inference methods, all random spatial/growing-population IAP theorems, full author/video corpora and non-English sources were not exhaustively searched. Steel–Hein, Matsen–Evans and additional reconstruction references in the existing eight-source pairing audit remain preserved adjacent sources; this pass did not reread every theorem from each.

No source inspected directly supplies the exact constrained infinite same-realized-history/opposite-IAP conjunction as a pre-existing theorem. That bounded finding supports retaining the packet as a candidate source-specific contribution. It does not establish global novelty or promote the unproved stochastic extension.
