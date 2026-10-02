# Psychology and sociology generalizations: source-based admission audit

Contributor: Codex / Sol6.1. Assessment: 2026-10-02 UTC.
Status: bounded source audit and research proposals, not new proofs, clinical claims, or a priority determination.

## Decision in brief

The existing work supports a useful PG/SG research programme, but the programme should begin with source-specific identification and experiment-design contracts. It does not support a claim that 85 CBT classifications have been proved, that CBT efficacy has been verified, or that the biological G5 recovery theorem already generalizes to people and societies.

The strongest near-term choices are:

1. **PG-L: delayed-response sufficiency in the published latent-cause task.** Most exciting scientific direction. Identify a specified longer-delay or genuinely new-context response without demanding unique recovery of every learning parameter. The cited task already contains a recovery test, model comparison, intervention simulations, and parameter-recovery work; those are baselines, not our proposed discoveries.
2. **SG-E: robust structural-power/bargaining-rank agreement.** Clearest externally posed mathematical comparison. Fix the original index and compare it with the entire set of balanced outcomes, including the quantifier over matchings. Exact index recovery and closest-theorem comparison precede enumeration.
3. **SG-C: censored local contagion observations and decision-relevant uncertainty.** Practical source-code-backed investigation. Local mechanism classification is already published. A potentially defensible extension concerns an explicitly censored observation channel, robust abstention, and a bounded measurement menu, not another first-discriminator claim.
4. **PG-A: source-faithful CBT observation adapter.** Most practical immediate reuse of completed work. Preserve and expose the existing source bridge, then state exactly what a fuller source adapter would have to preserve. This is engineering/formalization value, not a newly open mathematical problem.
5. **SG-S: signed-status/probabilistic ranking with shared path causes.** Most distinctive cross-psychology/sociology direction, but also one of the most model-sensitive. The source's independent noisy-OR baseline is established; free priors or a renamed path strength cannot supply a meaningful theorem.

The most distant defensible extension is **PG-M: longitudinal metacognitive incremental prediction with cognition and biomarkers**, joined to the other disciplines through explicit measurement and population-transport maps. This requires an eligible longitudinal cohort and empirical validation; a Lean-only answer would fail its scientific question.

“Ready for targeted prior-art/proof” below means that the next bounded source/prior-art investigation is well posed. It does not admit novelty or authorize implementation before that gate passes. No new proof project or simulation was started in this audit.

## 1. Verified corpus, provenance, and build state

### Source pins

- Formalizing-Soft-Sciences main: **8e665d2a9f6168e6448b2ca49fccbec87d57d3ad**. Repository tree and actual Lean files were read through the GitHub connector.
- Cross-Scale-Causal-Formalization main: **28bdb75b8d057332e1bb32020d02e5eaea4c0517**. The actual catalog directory is `research/open-problem-catalogs-2026-09-30/`; `PSYCHOLOGICAL.md`, `SOCIAL.md`, `OMNIBUS-MAP.md`, and `INDEX.json` were read.
- Samuel architecture source: **e2502c82ab9a77c00543932f775a71e5374221f7**, with the actual `PredictiveState.lean` and `StochasticAbstraction.lean` files under `research/open-problems/time-self-reference/predictive-memory/` read at that pin.
- Commons source context: **3d755ef391066069d33ff4490da65f00742b7ea7**. The Samuel connection map and current cross-G register were read. This is a read pin, not a claimed publication commit for this note.

### Direct declaration census

The census counts actual source lines introducing named `theorem` declarations, excluding copied historical source files, definitions, and repeated audit commands:

| Source module | Named declarations |
|---|---:|
| Solidarity.lean | 16 |
| SocialScience/Aggregation.lean | 8 |
| SocialScience/Causality.lean | 6 |
| SocialScience/CollectiveAction.lean | 10 |
| SocialScience/Identifiability.lean | 9 |
| SocialScience/Learning.lean | 9 |
| SocialScience/Measurement.lean | 9 |
| clinical/ClinicalModels/PublishedCBT.lean | 14 |
| clinical/ClinicalModels/SourceBridge.lean | 4 |
| **Total** | **85** |

Thus **16 + 51 + 18 = 85**, where 18 means 14 PublishedCBT results plus four source bridges. The main [psychology reconciliation](https://github.com/Sodelin/Formalizing-Soft-Sciences/blob/8e665d2a9f6168e6448b2ca49fccbec87d57d3ad/psychology/README.md), [coverage map](https://github.com/Sodelin/Formalizing-Soft-Sciences/blob/8e665d2a9f6168e6448b2ca49fccbec87d57d3ad/PUBLICATION-COVERAGE-2026-09-29.md), and [handoff](https://github.com/Sodelin/Formalizing-Soft-Sciences/blob/8e665d2a9f6168e6448b2ca49fccbec87d57d3ad/ASTRA-HANDOFF.md) agree with that census. The earlier Mathematics-of-Psychology-Formalized copy contributes no additional 16. A distinct older psychology corpus remains unlocated; this audit neither replaces it nor invents its inventory.

The preserved 67-result books do not silently become revised 85-result clinical editions. The existing declaration-level audit is an interpretive inventory, not 85 independent discoveries: its roles are 21 support, 20 endpoint, 17 consequence, 15 witness, ten integrity, and two reuse entries.

### Build evidence

The [current-main workflow run 36691100776](https://github.com/Sodelin/Formalizing-Soft-Sciences/actions/runs/36691100776) and [check/job 110555566686](https://github.com/Sodelin/Formalizing-Soft-Sciences/actions/runs/36691100776/job/110555566686) report **completed/success** for exactly the source pin above, completed 2026-10-01 around 19:54 UTC. The job's toolchain-install, source/build, research-documentation/provenance, and published-CBT-fragment steps all report success.

The [pinned workflow](https://github.com/Sodelin/Formalizing-Soft-Sciences/blob/8e665d2a9f6168e6448b2ca49fccbec87d57d3ad/.github/workflows/lean.yml) installs Lean **4.19.0**, builds the core and clinical projects, invokes both axiom audits, rejects source occurrences of sorry/admit/axiom/native_decide, and checks the pinned MATLAB transcription. This is positive CI evidence for the actual current commit. This audit did **not** run a fresh local Lean build, reinterpret CI as empirical validation, or claim compilation of all unrelated Samuel/Commons modules. An initial attempt to read a direct Actions job endpoint was unsupported by the connector; the supported workflow-run jobs endpoint and commit check-run collection supplied the successful evidence.

The actual omnibus index contains **five biological, four psychological, and five social entries: 14 total**. Catalog inclusion is a research lead, not proof admission. No catalog source claims all entries are novel solved targets.

## 2. What the existing Lean results actually establish

### Solidarity: separate reach, membership, and incentives

The network is the natural-number path, with adjacency between consecutive integers. Reach is the reflexive/transitive path relation. Connectedness and unbounded reach coexist with at most two neighbors. Membership is an arbitrary predicate and inclusion is implication; nesting and overlap are ordinary set/graph consequences. Trust is a separate arbitrary relation, so a completely false trust relation witnesses connectedness without trust. There is no empirical social network, cognitive capacity model, or inferred trust process.

The donation-game payoff is `benefit from the other's contribution − own contribution cost or defection sanction`. Stability of mutual contribution against unilateral Boolean deviations holds iff **cost ≤ sanction**. The benefit cancels in that comparison. Sanction reliability, integer payoffs, the specified deviation set, and the absence of institutional financing/legitimacy mechanisms matter. Attribute labels and symbols do not enter the payoff, so their inability to determine stability is built into the model. This is not evidence that identity never matters socially.

**Verdict:** useful elementary separation witnesses and incentive implications. No sociology mechanism or cross-scale intervention bridge is established. Reproving these under PG/SG labels would be duplication.

### Identifiability: exact probes and elementary fibres

`Equivalent predict design θ φ` means equality of exact outputs at every permitted probe. `Identified` demands that this forces θ = φ. Reflexivity, restriction, monotonic identification under extra probes, and preservation of indistinguishability under postprocessing follow directly from these definitions. The concrete model observes either an integer component sum or the first component. Sum-only observations confuse (1,0) with (0,1); both exact probes identify the pair.

**Verdict:** established identification/functional-factorization machinery plus a clear witness. No noisy estimation, confidence calibration, latent-clinical construct, or cost-optimal design is encoded.

### Measurement: additive scores, conditional bias interval

The observation is the integer sum latent + intercept. Common-intercept cancellation, the latent/intercept shift ambiguity, and recovery given a known intercept/anchor are algebraic. Unequal intercepts can reverse a latent ordering. The latent-difference interval assumes the differential bias lies in [−δ,δ]. A measured gap larger than the stipulated upper differential bias fixes the latent sign.

**Verdict:** a useful deterministic sensitivity template. Neither the bias bound nor construct/instrument validity is estimated or proved. A direct G6 application must supply those quantities and calibrated finite-data uncertainty externally.

### Causality: observational collision, different intervention effect

`BinaryModel.outcome` maps treatment and binary background to a binary result. Observational assignment sets treatment = background. The treatment-only and background-only models then have the same observation function, but their interventional effects differ. `effectNumerator` represents twice the average effect under a uniform background interpretation. The no-universal-estimator theorem is a consequence of that collision. Complete exact response-table equality identifies the record by function extensionality.

**Verdict:** standard causal nonidentification in a tiny deterministic class. It does not implement homophily/contagion, symptom dynamics, selection, or network interference.

### Learning: exact consistency, not psychological learning dynamics

`Fits` means agreement of a hypothesis with every item in a finite labeled list. Adding correct evidence retains the specified truth; a correctly labeled distinguishing query removes a rival; a wrong label can remove truth; duplicates add no exact constraints. Empty/concatenated-evidence lemmas are definition-level list reasoning.

**Verdict:** version-space learning prior art. There is no reward learning, posterior update, latent-cause inference, policy selection, human learning-rate estimate, or mechanism of therapy. Related public Lean version-space formalization is already recorded in the repository's [prior-work audit](https://github.com/Sodelin/Formalizing-Soft-Sciences/blob/8e665d2a9f6168e6448b2ca49fccbec87d57d3ad/research/publication-audit-2026-09-29/SOURCES.md).

### Collective action: task coverage and participation constraints

Feasibility says every required task has some capable group member. Congestion, time, competing resource demands, and stochastic failure are absent. Acceptance is each member's reward ≥ cost relative to a zero outside option. Larger groups preserve this uncongested task coverage; smaller groups preserve the corresponding acceptance constraint. A two-specialist witness separates aggregate surplus from individual participation. The two-person budget theorem characterizes existence of an unrestricted integer transfer by total costs ≤ budget.

**Verdict:** coverage and allocation feasibility. This is not a bargaining mechanism, balanced exchange outcome, organizational event model, or coalition formation theory. SOC-03 cannot be marked partly solved by the budget theorem.

### Aggregation: a strict Simpson witness and information loss

Four valid positive-denominator cells exhibit within-stratum advantages reversed after pooling. Other declarations reuse component-sum nonidentification and its postprocessing consequence.

**Verdict:** established Simpson behavior and deterministic data-processing loss. This is relevant warning vocabulary for HG2; it neither specifies a new sufficient social summary nor establishes a source-specific recovery boundary.

## 3. CBT fragment versus complete published model

### Exact scope of the formal fragment

The actual [PublishedCBT source](https://github.com/Sodelin/Formalizing-Soft-Sciences/blob/8e665d2a9f6168e6448b2ca49fccbec87d57d3ad/clinical/ClinicalModels/PublishedCBT.lean) fixes:

- Six phase labels: start, stimulus, approach, interact, avoid, safetyCost
- Two preselected deterministic transition functions
- Four recorded time points, starting at start
- A spider-present slice and two Boolean danger candidates
- All four observation modalities: spider observation, arousal, affect, and phase/action
- Exact integer-scaled implicit affective weights, with CABi interpreted as c/(10u) when u > 0

Avoidance records the same trajectory under the two danger candidates, so every classifier using **only that stipulated trajectory** fails on at least one candidate. Approach produces different affective observations and identifies the Boolean state among those two possibilities. The trajectory equalities are definitional; the classifier impossibility is the standard indistinguishability consequence; the scientific grounding lies in the selected published source tables.

Weight-mass, nonnegativity, and equality results concern unnormalized integer triples. Positivity and bounds are essential for the probability interpretation. The approach-column equality theorem itself needs no positivity premise; interpreting it as CABi = 0.1 does need u > 0. This is not verification over every real-valued parameter or the inferred patient's full posterior.

### What the source bridge adds

The pinned upstream is [CBT_model.m at 82a0a3d75b0bdc08d2b78cdf2201d7aa626c27a3](https://github.com/rssmith33/Simulating_Cognitive_Behavioral_Therapy/blob/82a0a3d75b0bdc08d2b78cdf2201d7aa626c27a3/CBT_model.m), with the extractor expecting SHA-256 `faba14894224ccf1a20594d390a5f7e3a74eed665205fa24285ddfa1d36513e5`.

The extractor checks ten selected matrices: the spider-present safe/danger slices of A1, A2, A3; the two B1 action matrices; and the two a3 implicit affective slices. Six literal source guards cover A4's phase-identity assignment, implicit/prior scales, the explicit prior assignment, T=4, and rng('shuffle'). Four Lean source-bridge theorems check sensory, affective, transition, and scaled implicit columns. A4 is guarded text rather than another extracted matrix theorem.

This is the strongest meaningful bridge in the 85 corpus: **published bytes → bounded declarative extraction → exact correspondence → an observation-level information statement**. Its novelty class is reproducible source-fragment verification, not invention of the source's avoidance explanation. The Python extractor and its selected syntax are part of the provenance/trusted pipeline; Lean does not prove the parser, MATLAB semantics, or SPM implementation correct.

### Mechanisms present upstream but absent from Lean

The upstream code additionally specifies initial-state priors D, explicit d concentrations, learned a concentrations, preference matrices C, policy sequences V, policy prior E, beta/alpha policy/action precision, eta learning rate, SPM model checking and variational inference calls, and a 200-trial exposure loop followed by updated-model tests. Its no-spider slices and all cross-trial latent updates are outside the current reconstruction. The source invokes `spm_MDP_check` and `spm_MDP_VB_X`; the Lean code never implements those algorithms.

The [2021 primary paper](https://pmc.ncbi.nlm.nih.gov/articles/PMC8115057/) already explains why avoidance withholds corrective information. Its Discussion separately proposes intolerance-of-uncertainty/partial-approach simulation and notes empirical parameter validation is needed. Those mechanisms cannot be inferred from the existing two-path theorem. Clinical efficacy, construct validity, and therapeutic recommendations do not follow from the formalization.

**PG-A admission:** ready as a source-adapter/audit continuation. Preserve existing results; a future full-model adapter needs declared SPM semantics and joint observation/action-history preservation. Reject a claim that fragment completion alone closes PSY-2 or proves CBT efficacy.

## 4. Primary prior-art attack and bounded search result

This is a **rapid evidence map**, not a systematic review. Actual files were inspected before proposal selection, then primary source pages/PDFs and their named closest work were queried before any new mathematical computation.

Load-bearing tightening beyond the 30 September catalog:

- [Dablander and Hinne (2019)](https://pmc.ncbi.nlm.nih.gov/articles/PMC6497646/) already compare centrality in estimated undirected networks with causal influence in source DAG models. A generic centrality/intervention counterexample is not a new PG result. Use their source assumptions and the newer source-specific intervention methods as baselines.
- [Berwian et al. (2024), pp.159–166](https://escholarship.org/content/qt3mj8q8kx/qt3mj8q8kx.pdf), the actual reference 15 behind PSY-3, already supplies acquisition/extinction, a roughly 15-minute recovery test, relearning, seven model variants, particle-filter inference, parameter recovery, and simulations of cognitive restructuring, retrieval cues and spaced extinction. Its selective-maintenance update is d = γ + (1−γ)ωp(US|cause). It reports ω/γ dependence and the reparameterization ω′=(1−γ)ω. Its Discussion still acknowledges missing mechanisms. These are substantial existing results, not an empty starter task.
- [Berwian et al. (2025), Testing the predictions/Figure 3](https://www.nature.com/articles/s44271-025-00251-4) explains the existing task/model pathway and calls for psychometric and longitudinal clinical validation. A new mathematical task-sufficiency certificate could be useful, but a fitted parameter is not automatically a validated clinical construct.
- [Andres et al. (2025)](https://www.nature.com/articles/s44260-025-00034-2), published 4 March 2025, already addresses coexisting simple, complex and spontaneous adoption from ego/neighbour histories, including unknown parameters and asynchronous setups. It provides a likelihood approach, random forests, a star-network analytical reference, and [public experiment code](https://github.com/ElsaA05/DistinguishSimpleComplex/tree/main/analysis). “Local rather than global observation” alone is not a novelty delta.
- [Contreras, Cencetti and Barrat (2024)](https://journals.plos.org/ploscompbiol/article?id=10.1371/journal.pcbi.1012206) already compare infection patterns across simple and complex processes and give [simulation code](https://github.com/giuliacencetti/Infection_pattern). Together with the catalog's 2023 classifier and 2025 persistent-homology work, this makes another generic contagion discriminator a poor target.
- [Kleinberg and Tardos (2008)](https://www.cs.cornell.edu/home/kleinber/stoc08-exchange.pdf), especially pp.2–3 and the subsequent characterization, already establish balanced-outcome existence iff stability and efficient set computation for weighted networks. Computing one balanced outcome is prior art. [Braun and Gautschi (2006)](https://www.sciencedirect.com/science/article/abs/pii/S0378873304000711) is another structural-embeddedness/bargaining baseline; this pass retrieved its primary abstract and model-context excerpts, not the complete original index derivation.
- [Volchenkov's author preprint, §§3.4–3.5](https://www.preprints.org/manuscript/202608.0726) supplies the ranking-comparison directions. In the status direction it already provides the conditional independent-path noisy-OR baseline and explicitly warns that strengths, probabilities, signed normalization, priors and posterior odds are different objects. Its complete publication-version passage was not freshly retrieved: the direct publisher endpoint failed. The author preprint is the verified passage source for this audit.
- [Cinelli et al. (2025), §3.6.3](https://arxiv.org/html/2508.17099v1) motivates joint causal-bias challenges, but [Smith, Mathur and VanderWeele](https://arxiv.org/abs/2005.02908) already combine multiple biases. Any SG joint-region proposal must map its exposure and sensitivity assumptions to that actual framework before derivation.
- [Cappa et al. (2024)](https://alz-journals.onlinelibrary.wiley.com/doi/10.1002/alz.13905) treats performance-based metacognitive measurement and longitudinal prognostic value as unmet needs. The [2026 awareness review](https://pubmed.ncbi.nlm.nih.gov/42739221/) still emphasizes heterogeneity and longitudinal standardization; its abstract was inspected in this pass. This does not establish that a specific new cohort study has priority.

Targeted web queries included exact source titles, partial approach/uncertainty, latent-cause model recovery and delayed response, network centrality versus causal intervention, local contagion mechanisms, structural power/balanced outcomes, and metacognitive longitudinal prediction. Broad or irrelevant search hits were not used as evidence. PMC challenge pages were not bypassed: publisher, author PDF and repository alternatives supplied usable sources where available. The 2024 latent-cause PDF succeeded through its canonical eScholarship PDF after a decorated download URL failed.

Unsearched or incomplete lanes include APA PsycInfo, a comprehensive citation/citer sweep, all original status-index papers, all organizational-ecology latent-event results, source-code reproduction of the 2024 task, and the publication correction details for the 2025 perspective. No zero-hit search establishes openness, no search-result date substitutes for a publication date, and no result is admitted on absence-of-hit reasoning.

## 5. Candidate contracts and admission decisions

### PG-L / catalog PSY-3: delayed-response sufficiency

- **Source model:** the actual 2024 latent-cause family and recorded trial protocol, rather than the deterministic PublishedCBT fragment. Fix the seven existing alternatives or a justified subset, priors, parameter bounds, selective-maintenance/decay updates, observation-likelihood update, inference approximation, and time representation.
- **Observation:** trial-level reported US expectations over the existing acquisition/extinction/test/relearning schedule. The existing delayed test is part of the baseline evidence, not an added invention.
- **Target:** a prespecified response distribution at a genuinely untested longer delay or new context, or a robust ranking between source-defined task interventions. Parameter uniqueness is not required if every compatible model gives the same target.
- **Assumptions:** a fixed shared parameter/model assignment explains all retained trials; report-error law and censoring are declared; approximation error of particle inference is separated from scientific model uncertainty; simulated breaks are not assumed to equal human elapsed time universally; the permitted extra trials and costs are fixed.
- **Closest prior art:** the 2024 task's own model comparison, reparameterization and recovery analysis; 2025 predictions and classical active design/target identifiability.
- **Actual remaining gap:** no source-specific proof in the current corpus certifies that the existing task determines the new target or which feasible added measurement removes its target-relevant ambiguity. The exact gap is a candidate until code and subsequent work are checked.
- **G parents:** G5 for target recovery; G6 for a calibrated compatible-response region/abstention; G7 for the allowed probe menu. HG2 diagnoses loss caused by aggregating trials; HG3 concerns minimality only under explicitly admitted task testers.
- **Admission:** **ready for targeted prior-art/proof**, first recovering actual code and comparing its design/recovery analyses. Reject “invent latent-cause fitting,” “add a delayed test,” or “discover ω/γ confounding.” Clinical prediction requires a separate empirical bridge.

### PG-N / PSY-1: symptom observations and intervention ranking

- **Source model:** a specified published causal symptom-dynamics model, with its simulation equations/implementation. A cross-sectional partial-correlation graph alone is an observation summary, not that source.
- **Observation:** declared instrument items and time-sampling/filtering channel, including selection and measurement error.
- **Target:** expected burden or intervention ranking at a fixed horizon under a named feasible action.
- **Assumptions:** latent dynamics, intervention semantics, confounding restrictions, measurement comparability, history dependence, costs and stochastic errors are fixed before optimisation.
- **Prior art:** Dablander/Hinne, existing causal graphical identification, and the catalog's in-silico intervention methodology. The elementary binary collision is reusable teaching machinery.
- **Gap:** source-specific partially observed dynamics may or may not permit a robust intervention target despite uncertain mechanisms. Neither this corpus nor this bounded search proves that narrowed result new.
- **G parents:** G5/G6/G7; G1 only if a genuine source-adapter preservation contract is supplied.
- **Admission:** **needs empirical bridge** for clinically interpreted interventions and a source-model bridge before proof. **Reject as duplicate/vague** the generic assertion that centrality can fail to identify causal targets.

### PG-U / PSY-2: uncertainty and partial approach

- **Source model:** a justified extension of the full 2021 active-inference model, adding a partial-approach action and its stochastic observations while retaining or explicitly changing inference, policy selection and learning.
- **Observation:** complete action/outcome histories and specified training/test contexts.
- **Target:** a model-specific region where partial approach improves a specified transfer outcome, versus maintaining avoidance. A single generic utility threshold is insufficient.
- **Assumptions:** preference/information weights, safety costs, prior concentrations, precision, learning equations, context-reset law, and policy menu are explicit. Outcomes must be simulation endpoints rather than unearned treatment claims.
- **Prior art:** the original source's information-seeking proposal, active-inference/POMDP theory, and newer learning models. The current no-perfect-classifier theorem is only its observation baseline.
- **Gap:** full source-consistent missing-mechanism specification and the exact subsequent-work comparison remain unresolved. A new action definition alone supplies no scientific mechanism.
- **G parents:** G1/G4 for full-model substitution, G5/G6 for transfer targets, G7 for controls. Do not conflate psychological generalization with G1 source equivalence.
- **Admission:** **needs empirical bridge** for any psychological claim; source-model and current-status hold for simulation/proof. No implementation admitted here.

### PG-M / PSY-4: longitudinal metacognitive added value

- **Source model:** a prespecified longitudinal prediction model in an eligible SCD population, with baseline cognition/biomarkers and separately measured confidence bias, sensitivity and efficiency.
- **Observation:** repeated task-level confidence/performance, informant reports, biomarkers and follow-up outcomes.
- **Target:** incremental held-out prediction of a fixed endpoint/horizon over the baseline model.
- **Assumptions:** task/instrument versions, population, missing follow-up, informant error, calibration, measurement invariance and transport are defended. Self/informant discrepancy is not automatically a pure awareness measure.
- **Prior art/gap:** existing metacognitive measures and longitudinal models are baselines; the unmet source question is incremental validated value under an adequate design. No eligible dataset was secured or evaluated in this audit.
- **G parents:** G6, with G5 measurement sufficiency and G7 design only as supporting mathematical work; Alt-G needs actual modality/population maps.
- **Admission:** **needs empirical bridge**. Most distant defensible extension, not a Lean proof target or diagnostic recommendation.

### SG-C / SOC-01: censored local contagion evidence

- **Source model:** the Andres et al. SI, deterministic-threshold and spontaneous-adoption families, including the declared synchronous/asynchronous and heterogeneous-parameter regimes. Simple adoption uses node-specific β; complex adoption uses a threshold φ on infected-neighbour fraction; spontaneous adoption uses r.
- **Observation:** ego/neighbour adoption times passed through a specified censoring/missing-edge channel. Local histories themselves are already the published baseline.
- **Target:** a robust mechanism-compatible set or a specified seed/control outcome ranking, with truthful abstention where alternatives remain indistinguishable.
- **Assumptions:** known versus unknown graph/parameters, seed law, coexistence, missingness mechanism, time resolution, and intervention feasibility are separated. The same global source assignment must explain all observations.
- **Prior art:** the 2025 local-view analytical/classification work, 2023 classifier, 2024 infection-pattern work, and 2025 higher-order classifier.
- **Gap:** a carefully chosen censored-law/cost boundary might be uncovered; the exact assertion must first be compared with published theoretical guarantees and supplements. A new classifier or local-view label is not enough.
- **G parents:** G5/G6/G7; HG2 for summaries; Alt-G may share the observation contract with epidemiology while retaining different adoption mechanisms.
- **Admission:** **ready for targeted prior-art/proof** on one explicit observation channel; reject the broad first-discriminator claim. This is the most practical source-code-backed SG investigation.

### SG-B / SOC-02: sharp joint-bias direct/spillover region

- **Source model:** a finite binary network causal model with a fixed exposure map, selection process and outcome misclassification restrictions.
- **Observation:** selected, error-prone treatment/exposure/outcome records.
- **Target:** a sharp identified interval/region for one direct or spillover contrast, including attaining compatible models.
- **Assumptions:** treatment assignment, positivity, cluster dependence, interference/exposure semantics, selection and misclassification dependence, and sensitivity parameters are fixed jointly.
- **Prior art/gap:** multiple-bias bounds and standard response-type enumeration already exist. The remaining candidate is one uncovered interference/error interaction or an actual computational/analytic gain, not additive-bias algebra renamed as causal sensitivity.
- **G parents:** G5/G6, G7 if design is included.
- **Admission:** **needs empirical bridge** for defended sensitivity/exposure restrictions and an exact prior-art mapping. Reject generic “joint bias is new.”

### SG-E / SOC-03: power ranking versus all balanced outcomes

- **Source model:** one exact original structural-power index on a declared weighted exchange-graph class; balanced outcomes use matching, outside options, stability and equal surplus on matched edges.
- **Observation:** the source graph/index or a declared graph measurement, with exchange/action semantics held fixed.
- **Target:** pairwise payoff ordering over the balanced-outcome set. State whether agreement is matching-conditioned, existential, or robust across all maximum-weight matchings and all balanced outcomes; require the outcome set nonempty.
- **Assumptions:** index version/normalization, edge weights, exchange capacity, graph class and matching quantifier are fixed. Do not replace the joint solution set by independent coordinate intervals.
- **Prior art:** Kleinberg/Tardos set characterization/efficient computation and original sociological index/bargaining work. Existing budget feasibility contains none of these objects.
- **Gap:** the author's source question is an exact ranking comparison. A new graph-class theorem, bounded minimal separating example or complexity boundary remains possible, but is unverified until the precise index and nearby class results are read.
- **G parents:** G5 target-directed comparison; HG2 for loss in a structural scalar; HG3 only relative to the admitted comparison/test family. G7 applies to measurement design only if a menu is actually added.
- **Admission:** **ready for targeted prior-art/proof**, beginning with exact index recovery. No enumeration or new proof until that discriminator passes.

### SG-S / SOC-04: shared-path status and probabilistic ranking

- **Source model:** signed relevance-path aggregation with decreasing path strength, together with a fully specified normalized signed probabilistic model, latent path activations, shared causes, priors and evidence.
- **Observation:** status/task evidence under one fixed protocol; path strength is not itself a measured probability.
- **Target:** preservation of actor-pair ordinal conclusions or a sharp dependency-sensitive region permitting honest rank abstention.
- **Assumptions:** factorization and shared causes, evidence semantics, prior restrictions, sign combination and outcome normalization are explicit. Edge-disjointness alone does not exclude shared latent causes. Free actor-specific priors can make an uninteresting reversal.
- **Prior art/gap:** independent noisy-OR is the source's Proposition 1 baseline, not our contribution. A meaningful extension would handle a specified overlap/dependence pattern and retain source-matched ranking semantics; the relevant original status literature and subsequent results remain incompletely screened.
- **G parents:** G1 for a faithful probabilistic reinterpretation under a precise interface; G5/G6 for ordinal target recovery; HG2/HG3 for summary loss and lawful tester-relative minimality.
- **Admission:** **needs empirical bridge** for probabilistic meaning and protocol linkage, with a ready narrow source/prior-art comparison. Reject generic noisy-OR reproof or arbitrary-prior counterexamples as discoveries. Most distinctive conceptual bridge.

### SG-O / SOC-05: recognition separately from congestion

- **Source model:** a specified two-latent-process marked birth/death/event model, not an unrestricted pair of unnamed mechanisms.
- **Observation:** organization density, founding/survival event histories, and a declared recognition/resource measurement or exclusion source.
- **Target:** separate effects or their sharp identified region.
- **Assumptions:** latent-process dynamics, risk sets, positive intensities, time resolution, measurement law, endogenous density and covariate/exclusion restrictions must be supplied.
- **Prior art/gap:** organizational ecology and latent-event identification are substantial baselines. A generic pair with identical counts is standard nonidentification; a source-linked minimal measurement/exclusion result could matter if not covered already.
- **G parents:** G5/G6/G7; G3/G4 only for a fully specified source realization/kernel question.
- **Admission:** **needs empirical bridge** and original-theorem review. Reject as vague until the process/measurement/exclusion contract is fixed.

## 6. G, HG, Bio-1 and Alt-G: what may actually transfer

### G assignment is an obligation, not a disciplinary analogy

- **G1:** a source replacement must preserve the actual contextual action/observation experiment, including history and shared registers. Matching selected CBT tables or observed social marginals does not automatically meet it.
- **G2:** selected-label/live-ancestor routing is a biological source obligation. A PG/SG adapter may have its own projection contract, but actors, causes and trials are not genealogical labels merely because they sit in a graph.
- **G3:** exact recognition asks whether the entire supplied object/law comes from one admitted source. A classifier score or a per-row fit is not a global source witness.
- **G4:** full-kernel equivalence and stopping demand richer semantics than target identification. No all-policy/full-model equivalence is proved by the four-point CBT fragment.
- **G5:** target constancy on observation fibres is reusable classical identification. The biological bounded-hidden-position calendar-panel theorem is a source-specific instance. Its (k+1)-tip conclusion has no automatic meaning for numbers of questionnaire items, therapy sessions, people, or contagion observations.
- **G6:** compatible-model regions become finite-data certificates only after the data law, confidence calibration, model error and abstention rule are supplied. An exact-consistency list is not a confidence set.
- **G7:** cost optimisation is meaningful only under an admitted action/measurement menu and a stated resource objective. Biological actuators and source IDs do not supply lawful psychological interventions.

HG1's bounded local-to-global backbone, HG2's information-loss reasoning and HG3's lawful tester-relative minimality can organise these projects. Their general classical mathematics should be credited and reused. The new contribution, if any, is the actual source integration or a new source-specific sharp boundary. Neither more discipline folders nor another quotient theorem is evidence of frontier movement.

### Explicit Alt-G transfer contract

Each proposed transfer should expose five objects:

1. Source model/state class, including nuisance parameters, shared memory and admitted contexts
2. Observation channel and retained history, including dependent measurement noise
3. Intervention map and policy class, preserving what the action really changes
4. Target map and horizon/population meaning
5. Preservation or calibrated-error claim relating the source's joint experiment law to the proposed representation

Models fitted separately to each panel/context can violate object 1 even when every marginal fit looks good. A transfer preserving only a target need not preserve every latent mechanism; that limitation should be deliberate and explicit. If the transfer changes measurement semantics or context, it needs a separate measurement/transport bridge rather than a notation substitution.

### Samuel Alexander architecture

The current [PredictiveState source](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-problems/time-self-reference/predictive-memory/PredictiveState.lean) explicitly labels its controlled behavioral quotient/machine-minimization construction classical. It covers all finite action words and total actions. Exact refinements require observation and transition commutation; feedback preservation additionally requires the selected action to factor through retained state/history. Finite-depth tests become all-horizon conclusions only with the global stabilization hypothesis.

The [StochasticAbstraction source](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-problems/time-self-reference/predictive-memory/StochasticAbstraction.lean) formalizes exact controlled kernel lumping and complete finite observed action/history-law preservation. It requires the joint next-state/measurement pushforward, not equality of separate transition and emission marginals. Persistent sensor drift or memory must be included in the state. These are useful architecture for future PG/SG adapters; their hypotheses do the substantive work and are not currently discharged for a complete CBT source.

Alexander's infinite pedigree/unavoidability/cluster questions are different scientific sources. A finite psychological state graph or a social influence network does not become an organism pedigree, infinite future completion, or species predicate by analogy. The existing [Alexander connection map](https://github.com/Sodelin/Research-Commons/blob/3d755ef391066069d33ff4490da65f00742b7ea7/notes/2026-09-30-alexander-connection-map-1812z.md) already requires explicit source/observation/target maps. The defensible distant extension is to investigate finite-history versus enduring-response targets under explicit persistence/transport assumptions, without importing an infinite-ancestry theorem as a psychology claim.

**Bio-1 connection:** share interface discipline and target-directed finite-data certification. Keep phylogenetic genealogy, molecular observations, symptom dynamics, human learning and social adoption laws separate until an actual map proves the required relation. Quartet/calendar target recovery is not evidence for real-world psychological or sociological recovery.

## 7. Stopping point and proposed next decision

The requested audit has established the corpus, current CI evidence, formal-model boundaries, primary-prior-art threats, candidate contracts, and transfer limits. No model validity, clinical efficacy, new theorem, experiment, exhaustive literature closure or fresh local build is claimed.

The least costly consequential next research choice is **one** of:

- Recover PG-L's actual code and audit the existing/new probe distinction before deriving target uncertainty
- Recover SG-E's exact index and compare original class results before any graph enumeration
- Inspect SG-C's analytical guarantees/supplements against one explicitly censored observation channel before any new classifier or simulation

PG-A can proceed as source-adapter documentation/engineering independent of novelty; it should preserve the current fragment rather than restart it. PG-U, PG-M, SG-B, SG-S and SG-O retain source/empirical gates. This note supplies an admission map, not a new mandatory proof backlog.
