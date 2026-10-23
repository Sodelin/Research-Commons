# Claim board: what we know, what it is useful for, and what is still open

Updated 2026-10-23. Prepared by dot (OpenAI). Version 1.11-alexander-source-recovery. P5 source publication by the existing owner, Codex (OpenAI).

This is a **claim-by-claim guide**, not a list of everything we have written. Start with the four short answers on each card. The expandable section holds the exact assumptions, attribution, evidence and remaining work.

For completed work that older notes mistakenly leave pending, read the [duplicate-work and supersession report](DUPLICATE-WORK-REPORT.md). It preserves accepted results rather than counting them as new discoveries.

Current status labels were reconciled on 23 October; see the [scope and corrections](STATUS-LABEL-AUDIT.md). Author-complete hand proofs, independent acceptance, formal checking and implementation are separate facts.

## Binding completion labels — human correction, 23 October 2026

A complete hand proof is **PROVED (not Lean formalized)** when no full Lean receipt exists. Independent review is a separate field; an author-complete proof is not an unstarted research task. A historical “candidate” header, unrun build, missing review or broader unsolved extension cannot reopen the completed statement. Unverified source status is labelled unverified, not inferred mathematically open.

The compact index below is a mathematical summary; the exact current completion/formal/review fields are on each card and in [claims.json](claims.json). Completed cards label later work **separate downstream work**, so that it cannot become another request to re-prove the supplier. The [G3 recovered proof catalogue](../research/2026-10-23-g3-proof-recovery/README.md) preserves 58 mathematical notes and 17 Lean source files with original/public hashes and exact successor corrections. These are recovered sources, not 75 new results.

## How to read the board

- **Proved** means the exact stated mathematics has a documented proof and acceptance at the level specified. It does not automatically mean software verified it.
- **Kernel checked** means the linked formal proof passed its stated proof-checking scope. It does not automatically validate an experimental model or a native executable.
- **Source proposal** means the algorithm/proof text exists, but its formal acceptance is unfinished. That is different from an unanswered mathematical question.
- **A counterexample** defeats its named claim, not the whole paper or research programme.
- **A software check** or **an empirical result** is recorded as such, not promoted into a general theorem.
- **Novelty is separate:** a correct result may reuse established mathematics, and most priority claims here remain unresolved.

## Start with a question

- **Can we simplify ancestry models without changing their answers?** [G1](#cb-g1-001), [phylogenetic root region](#cb-phy-001). These share an idea, not an established theorem dependency.
- **Can we know when enough observations have been collected?** [Completed shared-routing method](#cb-g4-002), [completed two-mode theorem](#cb-g4-003), [remaining independent-only question](#cb-g4-008).
- **Can uncertain data support an honest conclusion?** [G6](#cb-g6-001).
- **Can we choose better tests?** [G7](#cb-g7-001), [restricted causal experiments](#cb-causal-001). Here the causal connection is a proved adapter at the hand-proof level.
- **Do cell-development scores reveal the true hidden history?** [Score limits](#cb-lineage-001), [stochastic-model example](#cb-lineage-002), [optimization difficulty](#cb-lineage-003). These are different questions.
- **What has actually been written or checked in software?** [Mathematical verifier source](#cb-lineage-004), [separate formal-hardness gap](#cb-lineage-005). A certificate, checker, proof of checker correctness and native implementation are four different things.
- **What else happened in October?** [Sequence proofs](#cb-seq-001), [RNA source binding](#cb-rna-001), [MSci DNA models](#cb-msci-001), [solver checks](#cb-software-001), [empirical limits](#cb-emp-bpp-001), [sports evaluations](#cb-sport-baseball-001).
- **What about other sciences?** [Reaction models](#cb-rxn-001), [quantum testing](#cb-phys-p1-001), [noisy quantum dynamics](#cb-phys-p5-001), [nanowire measurements](#cb-nano-001).

## Coverage and source discipline

**Revision — 23 October 2026, 09:25 UTC:** nine recovered existing sequence groups are now indexed below, preserving all 75 prior claim objects and their evidence. These are source/navigation groups, not nine new discoveries. Any dated subjective ranking of 75 cards remains that snapshot; the new nine have not been ranked.

**Feedback source recovery — 23 October 2026, 09:52 UTC:** five existing Samuel B01–B06 groups are now indexed, preserving all 84 prior claim objects. The identical-ancestors property (IAP) means that each member has finitely many descendants or finitely many non-descendants in the stated set. The [same-draw completion](#cb-feedback-005) supersedes its finite precursor's pending list; the [ranking-reversal card](#cb-feedback-004) retains the exact historical build and written-only proof boundaries. These are mathematical model results, not empirical speciation claims or five new discoveries. The dated 75-card subjective ranking remains unchanged; the nine sequence and five feedback additions are not ranked.

**Genome/ownership source recovery — 23 October 2026, 10:00 UTC:** four existing groups cover Samuel G01–G05, preserving all 89 earlier claim objects. They separate [finite ancestry versus unrestricted infinite completion](#cb-genome-001), the [classical three-taxon control](#cb-genome-002), [missing diploid ownership and exact informative sampling](#cb-genome-003), and [independent-block family recovery versus matching correlated marginals](#cb-genome-004). These are recovered completed mathematical results with scoped historical formal receipts, not new discoveries or validated biological classifiers. The ownership sampling criterion consumes a whole infinite record unless the stated switch bound is supplied. Existing subjective ranks are unchanged; these four have not been globally ranked.

**Controlled-state and memory source recovery — 23 October 2026, 10:15 UTC:** four existing groups cover Samuel M01–M05, preserving all 93 earlier claim objects. [Exact deterministic reduction and predictive memory](#cb-memory-001) are grouped as predecessor and continuation; the [split obstruction](#cb-memory-002), [exact stochastic experiment theorem](#cb-memory-003) and [sharp written calibration bound](#cb-memory-004) retain separate scopes. The opposite-completion supplier is already [CB-GENOME-001](#cb-genome-001), not another counted result. Historical 37-source/108-report evidence is not a new build or a discovery count; calibration's independent review is source-reported, and its general proof is not Lean. Countably supported PMFs are not general continuous kernels, and the approximate-TV target remains unmechanized. No empirical memory/consciousness claim or subjective-rank change is made.

**Population/stateful-certificate source recovery — 23 October 2026, 10:23 UTC:** four existing groups cover Samuel T04–T06 and T08–T10, preserving all 97 prior claim objects. They separate the [sharp permanent-gender cap-two threshold](#cb-population-001), [critical-tail rigidity and exact port encoding](#cb-population-002), [full-language pruning versus avoidance-only repair](#cb-population-003), and [one synthetic three-state CA certificate separation](#cb-population-004). Full-schedule periodicity is an additional hypothesis, not a consequence of finite ports. Archived formal receipts are not new runs; the canonical-port converse is written-only. These are recovered mathematical results, not four new discoveries, empirical biology or a Life-like speed result. The dated 75-card ranking is unchanged and these additions have not been ranked.

**Alexander source recovery — 23 October 2026, 10:29 UTC:** three existing groups cover Samuel A01–A04, preserving all 101 earlier claim objects: [countable-host nonuniversality with exact parents](#cb-alexander-002), [classical matching-state certificates and rank transport](#cb-alexander-003), and [maximal clusters under one fixed real founder window](#cb-alexander-004). The countable-host result does not preserve the uniform child cap of [CB-ALEXANDER-001](#cb-alexander-001). Terminal cloning and complete blow-up are different constructions. The October 2 novelty correction credits classical rank/pruning methods without undoing their checked mathematics. Founder-window existence includes an actual seed and all same-window competitors. Historical proof/hosted receipts are recovered, not rerun; no new discovery, biological validation or subjective-rank change is claimed.

This register contains **104 cards**. It is deliberately not an exhaustive catalogue of the repository. Original G1–G7 split branches and two scoped G7 optima; Four cross-field programmes; Physics P1/P5; Nanowires; Selected October sequences, RNA/E8, NANUQ, MSci, solver infrastructure, empirical and application outcomes; Reusable positive-moment component are represented. 

Stable IDs keep different scopes apart. Original G1–G7 are one programme. **Physics P1–P5 are not the unrelated P1–P8 priorities in the October 7 external catalogue.** CG/MG/HG labels are retained aliases or views, not automatically extra master theorems. The external 372-family catalogue is a source-discovery index, not 372 new results.

Source status comes from the linked accepted successors, not an old draft's 'pending' header. This board does not repeat every proof review. For the detailed 14-branch audit, see [G3/G4 acceptance audit](G3-G4-ACCEPTANCE-AUDIT.md). The [machine-readable register](claims.json) contains the same cards and typed connection edges.


## Related work outside this repository

Research Commons is a coordination and discovery home, not the entire research archive. The [Cross-Scale question map](https://github.com/Sodelin/Cross-Scale-Causal-Formalization/blob/28bdb75b8d057332e1bb32020d02e5eaea4c0517/research/open-problem-catalogs-2026-09-30/EXPLANATION-AND-PRIORITIES.md) records biological, psychological and social directions; its historical open labels must be compared with later results. In particular, its structural BIO-1 query-policy gap is superseded by the accepted exact-query results indexed here, while noisy biological acquisition remains a different obligation.

[Formalizing Soft Sciences](https://github.com/Sodelin/Formalizing-Soft-Sciences/blob/8e665d2a9f6168e6448b2ca49fccbec87d57d3ad/PUBLICATION-COVERAGE-2026-09-29.md) separately accounts for 85 checked declarations: 16 solidarity, 51 foundations and 18 published-model fragments. The early Mathematics-of-Psychology repository preserves the same 16, not 16 additional results. These are recorded formalization/source-fragment results, not 85 new field-level discoveries or empirical laws; no build was rerun in this reconciliation. The original Samuel Alexander repository retains the all-level structural proof linked on the cards below. Preserve original sources and authorship instead of copying them into a competing registry.

### Compact index

| ID | Programme / claim | Mathematical disposition |
|---|---|---|
| [CB-G1-001](#cb-g1-001) | A smaller ancestry diagram can preserve the answers | Proved; named Lean scope checked |
| [CB-G2-001](#cb-g2-001) | Keeping fewer sampled individuals stays consistent | Proved; named Lean scope checked |
| [CB-G3-001](#cb-g3-001) | Checking one proposed model is easier than ruling out every model | Proved (not Lean formalized) |
| [CB-G3-002](#cb-g3-002) | A supplied observation certificate can bound the search | Proved (not Lean formalized) |
| [CB-G3-003](#cb-g3-003) | Some inputs allow us to acquire the needed certificate | Proved (not Lean formalized) |
| [CB-G3-004](#cb-g3-004) | Can every exact input be decided? | Unresolved mathematical implication |
| [CB-G4-001](#cb-g4-001) | Some hidden information can be recovered by permitted tests | Proved (not Lean formalized) |
| [CB-G4-002](#cb-g4-002) | Shared routing has a genuine stopping method | Proved by hand; named Lean subcomponents checked |
| [CB-G4-003](#cb-g4-003) | Two routing modes together need only finitely many exact tests | Proved by hand; named Lean subcomponents checked |
| [CB-G4-004](#cb-g4-004) | The result extends to qualifying extra tests | Proved (not Lean formalized) |
| [CB-G4-005](#cb-g4-005) | All independent-routing answers determine all shared-routing answers | Proved (not Lean formalized) |
| [CB-G4-006](#cb-g4-006) | The algebraic search reduction is already complete | Proved (not Lean formalized) |
| [CB-G4-007](#cb-g4-007) | The broader automatic certificate finder is still missing | Unresolved mathematical implication |
| [CB-G4-008](#cb-g4-008) | Finite independent-routing tests are the main unresolved branch | Unresolved mathematical implication |
| [CB-G5-001](#cb-g5-001) | Small timed panels recover particular ancestry features | Proved; named Lean scope checked |
| [CB-G5-002](#cb-g5-002) | Bounded hidden branching has a larger-panel hand theorem | Proved (not Lean formalized) |
| [CB-G6-001](#cb-g6-001) | Certify only what every compatible model agrees on | Proved by hand; named Lean subcomponents checked |
| [CB-G7-001](#cb-g7-001) | Choose tests with a proof of what their answers can establish | Proved by hand; named Lean subcomponents checked |
| [CB-CAUSAL-001](#cb-causal-001) | Some causal questions can be answered with limited experiments | Proved (not Lean formalized) |
| [CB-CAUSAL-002](#cb-causal-002) | Some exact causal tasks really require many tests | Proved (not Lean formalized) |
| [CB-CAUSAL-003](#cb-causal-003) | No target means this particular task needs no questions | Proved (not Lean formalized) |
| [CB-LINEAGE-001](#cb-lineage-001) | A best-fit score does not reveal every developmental link | Proved (not Lean formalized) |
| [CB-LINEAGE-002](#cb-lineage-002) | Different hidden graphs can give identical observed trees | Proved (not Lean formalized) |
| [CB-LINEAGE-003](#cb-lineage-003) | The actual tree-refinement problem is computationally hard | Proved (not Lean formalized) |
| [CB-LINEAGE-004](#cb-lineage-004) | An explicit mathematical checking algorithm has been written | Proof source complete; formal validation pending |
| [CB-LINEAGE-005](#cb-lineage-005) | The formal hardness connection is still missing | Formal integration pending; mathematics is a separate claim |
| [CB-PHY-001](#cb-phy-001) | A root region can be replaced without changing the stated output | Proved (not Lean formalized) |
| [CB-RXN-001](#cb-rxn-001) | Finite features identify one scalar reaction-model class | Proved (not Lean formalized) |
| [CB-RXN-002](#cb-rxn-002) | Two tempting identification shortcuts fail | Proved (not Lean formalized) |
| [CB-RXN-003](#cb-rxn-003) | One hidden observation problem reduces to a survival response | Proved (not Lean formalized) |
| [CB-PHYS-P1-001](#cb-phys-p1-001) | We have better upper and lower limits on the testing cost | Proved (not Lean formalized) |
| [CB-PHYS-P1-002](#cb-phys-p1-002) | A specific measurement has a useful error bound | Proved (not Lean formalized) |
| [CB-PHYS-P5-004](#cb-phys-p5-004) | The unrestricted uniform approximation claim has a completed hand counterexample | Proved by author (not Lean formalized) |
| [CB-PHYS-P5-001](#cb-phys-p5-001) | Several parts of a long-time approximation proof are established | Proved (not Lean formalized) |
| [CB-PHYS-P5-003](#cb-phys-p5-003) | One restricted noisy-quantum case is fully proved by hand | Proved (not Lean formalized) |
| [CB-PHYS-P5-002](#cb-phys-p5-002) | One proposed evolution can fail to preserve a physical state | Proved (not Lean formalized) |
| [CB-NANO-001](#cb-nano-001) | Very similar energy curves can hide opposite model labels | Proved (not Lean formalized) |
| [CB-NANO-002](#cb-nano-002) | Conductance can certify a sign in a specified matrix model | Proved (not Lean formalized) |
| [CB-NANO-003](#cb-nano-003) | One known-model thermal calculation keeps a positive margin | Scoped computational certificate |
| [CB-NANO-004](#cb-nano-004) | Even a complete transmission spectrum cannot force a negative label | Proved (not Lean formalized) |
| [CB-NANO-005](#cb-nano-005) | This entire model-changing route cannot reverse the reflection sign | Proved (not Lean formalized) |
| [CB-CM-001](#cb-cm-001) | A classical moment theorem has a checked reusable component | Proved; named Lean scope checked |
| [CB-SEQ-001](#cb-seq-001) | Three exact first-occurrence formulas are formally proved | Proved; named Lean scope checked |
| [CB-SEQ-002](#cb-seq-002) | A proposed simple description is impossible | Proved (not Lean formalized) |
| [CB-SEQ-003](#cb-seq-003) | The allowed lengths are classified in a specific range | Proved (not Lean formalized) |
| [CB-RNA-001](#cb-rna-001) | A small part of the structure-processing chain is formally connected | Proved; named Lean scope checked |
| [CB-NANUQ-001](#cb-nanuq-001) | A formal chain connects a stated source to its geometric formula | Proved; named Lean scope checked |
| [CB-MSCI-001](#cb-msci-001) | Enough sites preserve the specified ancestry-law distinctions | Proved (not Lean formalized) |
| [CB-MSCI-002](#cb-msci-002) | Equivalent histories differ only by a coherent hidden renaming in one class | Proved (not Lean formalized) |
| [CB-MSCI-003](#cb-msci-003) | Two-site population features identify a specific model family | Proved (not Lean formalized) |
| [CB-SOFTWARE-001](#cb-software-001) | The solver distinguishes a sharp fixture from genuinely broad data | Scoped software result |
| [CB-SOFTWARE-002](#cb-software-002) | A tested Rust component is not a universal correctness certificate | Scoped software result |
| [CB-EMP-BPP-001](#cb-emp-bpp-001) | The saved analyses do not yet support a stable history ranking | Empirical negative or inconclusive result |
| [CB-EMP-TSUGA-001](#cb-emp-tsuga-001) | Different markers disagree, but the cause is not established | Empirical negative or inconclusive result |
| [CB-MATERIALS-001](#cb-materials-001) | One descriptor can hide a change in the next-step behaviour | Proved (not Lean formalized) |
| [CB-DIFFRACTION-001](#cb-diffraction-001) | A good fit alone does not certify a molecule's presence | Proved under the stated premises (not Lean formalized) |
| [CB-VIEWSHED-001](#cb-viewshed-001) | Failed runs are now accounted for explicitly | Scoped software result |
| [CB-SPORT-BASEBALL-001](#cb-sport-baseball-001) | The tested models did not pass the stronger improvement test | Empirical negative or inconclusive result |
| [CB-SPORT-BASKETBALL-001](#cb-sport-basketball-001) | An apparent model improvement is not accepted | Empirical negative or inconclusive result |
| [CB-ALEXANDER-001](#cb-alexander-001) | One host cannot contain every member of the stated restricted class | Proved (not Lean formalized) |
| [CB-G7-002](#cb-g7-002) | One labelled programme can be optimal in a specified test menu | Proved (not Lean formalized) |
| [CB-G7-003](#cb-g7-003) | A different menu has a classical covering-array cost | Proved (not Lean formalized) |
| [CB-NANUQ-002](#cb-nanuq-002) | The original distance keeps exactly the displayed splits at every finite level | Proved (not Lean formalized) |
| [CB-EXACTQUERY-001](#cb-exactquery-001) | Recover the split union and an order with optimally growing query cost | Proved (not Lean formalized) |
| [CB-EXACTQUERY-002](#cb-exactquery-002) | The exact minima are one query for four taxa and five for five | Proved (not Lean formalized) |
| [CB-EXACTQUERY-003](#cb-exactquery-003) | The exact optimum has a finite constructive specification for every size | Proved (not Lean formalized) |
| [CB-TOPOCONTROL-001](#cb-topocontrol-001) | Three settings suffice for a probability floor, and four for certainty | Proved (not Lean formalized) |
| [CB-NANUQ-003](#cb-nanuq-003) | Five labels suffice to test the whole anchor-parameter domain, and four do not | Proved (not Lean formalized) |
| [CB-NANUQ-004](#cb-nanuq-004) | Only the two extreme copies are needed for quartet sets and split unions | Proved (not Lean formalized) |
| [CB-NANUQ-005](#cb-nanuq-005) | Rounding tolerates errors below one half, and the uniform limit is sharp | Proved (not Lean formalized) |
| [CB-SOFTSCI-001](#cb-softsci-001) | Extra observations can resolve ambiguity, but their assumptions matter | Proved; archived Lean check recorded |
| [CB-SOFTSCI-002](#cb-softsci-002) | Identical observations can conceal different intervention effects | Proved; archived Lean check recorded |
| [CB-SOFTSCI-003](#cb-softsci-003) | Connectedness, trust and an acceptable deal are different requirements | Proved; archived Lean check recorded |
| [CB-SOFTSCI-004](#cb-softsci-004) | Pooling groups can reverse both within-group comparisons | Proved; archived Lean check recorded |
| [CB-SOFTSCI-005](#cb-softsci-005) | In one published model fragment, the action determines what can be learned | Proved; archived Lean check recorded |

| [CB-SEQ-004](#cb-seq-004) | Every start and phase has an exact matching answer | Proved; archived Lean check recorded |
| [CB-SEQ-005](#cb-seq-005) | Finite prefix changes have an exactly computable global cost | Proved; archived Lean check recorded |
| [CB-SEQ-006](#cb-seq-006) | Huge finite matches need not become an infinite match | Proved; archived Lean check recorded |
| [CB-SEQ-007](#cb-seq-007) | Typical-scale totals differ sharply from exceptional long matches | Proved by hand; acceptance recorded in complete reading edition |
| [CB-SEQ-008](#cb-seq-008) | A precise coding transfers patterns without preserving every property | Proved by hand; acceptance recorded in complete reading edition |
| [CB-SEQ-009](#cb-seq-009) | A finite pattern reveals its grouping and hidden alignment | Proved by hand; acceptance recorded in complete reading edition |
| [CB-SEQ-010](#cb-seq-010) | Grouped patterns can be richer than ordinary Thue–Morse | Proved by hand; acceptance recorded in complete reading edition |
| [CB-SEQ-011](#cb-seq-011) | Selected digit gaps control repetition, branching and distinguishability | Proved by hand; acceptance recorded in complete reading edition |
| [CB-SEQ-012](#cb-seq-012) | Every finite prefix can exist without one positive infinite realization | Proved by hand; named Lean components checked |
| [CB-FEEDBACK-001](#cb-feedback-001) | Recurring reproductive links determine an ancestry property under explicit mixing | Proved by hand; named historical Lean scope checked |
| [CB-FEEDBACK-002](#cb-feedback-002) | Stable cultural differences can coexist with neutral-marker homogenization | Proved by hand; named historical Lean scope checked |
| [CB-FEEDBACK-003](#cb-feedback-003) | Positive selection defeats arbitrary admitted affinity changes in one source recursion | Proved by hand; named historical Lean scope checked |
| [CB-FEEDBACK-004](#cb-feedback-004) | Finite sampling reverses a matched deterministic marker-barrier ranking | Proved by hand; historical Lean components checked with stated receipt limit |
| [CB-FEEDBACK-005](#cb-feedback-005) | One shared random process joins a marker barrier to almost-sure ancestry mixing | Proved by hand; named historical Lean scope checked |

| [CB-GENOME-001](#cb-genome-001) | A finite ancestry graph does not determine its infinite population's specieslike status | Proved; archived Lean check recorded |
| [CB-GENOME-002](#cb-genome-002) | Exact laws identify three-taxon relationships, but finite samples do not give certainty | Proved; archived Lean check recorded |
| [CB-GENOME-003](#cb-genome-003) | Missing diploid ownership can change long-term ancestry; informative samples are characterized exactly | Proved; archived Lean check recorded |
| [CB-GENOME-004](#cb-genome-004) | Independent inheritance blocks have an exact recovery probability; matching marginals do not suffice | Proved; archived Lean check recorded |

| [CB-MEMORY-001](#cb-memory-001) | An exact predictive summary must keep the distinctions that future actions can expose | Proved; archived Lean check recorded |
| [CB-MEMORY-002](#cb-memory-002) | The present group membership does not determine a predecessor-restoring split | Proved; archived Lean check recorded |
| [CB-MEMORY-003](#cb-memory-003) | An exact stochastic summary preserves the full adaptive observation record | Proved; archived Lean check recorded |
| [CB-MEMORY-004](#cb-memory-004) | There is an exact error cost for distinguishing an impossible event from a rare one | Proved (not Lean formalized) |

| [CB-POPULATION-001](#cb-population-001) | Two children suffice for target avoidance, even with permanent genders | Proved; archived Lean check recorded |
| [CB-POPULATION-002](#cb-population-002) | Critical populations have exact tail structure and finite-frontier descriptions | Proved; archived Lean check recorded |
| [CB-POPULATION-003](#cb-population-003) | Pruning preserves every infinite word; boundary repair preserves avoidance | Proved; archived Lean check recorded |
| [CB-POPULATION-004](#cb-population-004) | One synthetic cellular automaton exposes the cost of forgetting state | Proved; archived Lean check recorded |
| [CB-ALEXANDER-002](#cb-alexander-002) | No countable list of hosts contains all the stated avoiding populations | Proved; archived Lean check recorded |
| [CB-ALEXANDER-003](#cb-alexander-003) | Matching states either continue forever or have an exact finite height | Proved; archived Lean check recorded |
| [CB-ALEXANDER-004](#cb-alexander-004) | Every organism belongs to a maximal cluster under a fixed founder window | Proved; archived Lean check recorded |

## Claim cards


<a id="cb-softsci-001"></a>
### Extra observations can resolve ambiguity, but their assumptions matter
**CB-SOFTSCI-001 · Soft Sciences · identification, measurement and evidence**

**Question:** Which additional observations actually distinguish competing explanations?

**What we learned:** A sum alone hides its components, a specified second probe recovers them, and known bias bounds translate into exact uncertainty intervals. Correct discriminating labels remove rivals; incorrect exact labels can remove the truth.

**What it lets someone do:** Inspect precisely what extra measurement or evidence justifies a conclusion before fitting or interpreting a model.

**What we cannot conclude:** These noiseless integer and exact-label results do not establish an empirical bias bound, a sample-complexity guarantee or robustness to noisy labels.

**Kind:** theorem. **Mathematical status:** Proved; archived Lean check recorded.

<details>
<summary>Exact scope, prior work, evidence and separate downstream work</summary>

**Exact statement and assumptions.** The 27 declarations are nine each in Identifiability, Measurement and Learning. For theta in Int x Int, observing only its sum is noninjective, while observing the sum and first component is injective. For arbitrary prediction functions, more probes preserve identification and postprocessing preserves observation equivalence. In the integer response model response(a,bias)=a+bias, a supplied differential-bias interval [-delta,delta] implies latent difference in [observed gap-delta,observed gap+delta]; an upper bias bound below the observed gap fixes the latent ordering. For deterministic hypotheses and finite exact-label lists, adding correct discriminating evidence preserves a fitting truth and excludes a disagreeing rival; a wrong label excludes truth, inconsistent labels admit no fit, and duplicate identical constraints leave the fitting set unchanged.

**Origin.** project posed. Precisely specified project models, formalizing established reasoning rather than solving an author-designated external open problem.

**Prior work.** These are established identification, additive measurement-invariance and version-space principles. The source comparison credits Wilson and Collins (2019), Putnick and Bornstein (2016), Mitchell's version-space work and related Cslib formalization. The integer examples do not resolve those sources' broader scientific agendas.

**Our contribution and attribution.** The original Formalizing Soft Sciences package exposes the assumptions, proof terms and readable interpretation of these elementary results in one inspectable development. This card recovers that completed work; it adds neither a new theorem nor a claim of 27 discoveries.

**Evidence, kept separate:**

- **Hand:** The repository's complete AI-assisted declaration/publication audit and this bounded actual-source reading support the stated model scope. No human peer-review or fresh worldwide novelty review is claimed.
- **Formal:** The archived Lean 4.19.0 foundations receipt covers the exact 67 solidarity/foundations declarations, with pinned source hashes and propext/Classical.choice/Quot.sound dependencies. The count includes support lemmas and examples. This audit did not rerun Lean.
- **Execution:** Successful historical workflow and source/axiom checks are recorded in the linked manifest; no scientific execution or fresh workflow inspection was performed for these cards.
- **Empirical:** Exact consequences of specified mathematical models. No empirical psychological, social or clinical law follows from formal correctness alone.

**Novelty:** Established mathematics or an already described source-model mechanism; the indexed contribution is precise formalization and source binding, not a claim to a new field-level discovery.

**Separate downstream work (does not reopen this result):** Empirical calibration of bias bounds, stochastic observation models, statistical estimation and learning generalization are not established here. The source's broader research questions remain separate from these completed formal examples.

**Proof, review and related source links:**

- [Identification theorem bodies](https://github.com/Sodelin/Formalizing-Soft-Sciences/blob/8e665d2a9f6168e6448b2ca49fccbec87d57d3ad/SocialScience/Identifiability.lean) (proof or status).
- [Measurement theorem bodies](https://github.com/Sodelin/Formalizing-Soft-Sciences/blob/8e665d2a9f6168e6448b2ca49fccbec87d57d3ad/SocialScience/Measurement.lean) (proof or status).
- [Learning theorem bodies](https://github.com/Sodelin/Formalizing-Soft-Sciences/blob/8e665d2a9f6168e6448b2ca49fccbec87d57d3ad/SocialScience/Learning.lean) (proof or status).
- [Complete declaration inventory and role audit](https://github.com/Sodelin/Formalizing-Soft-Sciences/blob/8e665d2a9f6168e6448b2ca49fccbec87d57d3ad/research/publication-audit-2026-09-29/THEOREM-BY-THEOREM.md) (proof or status).
- [Prior-work comparison and reading limits](https://github.com/Sodelin/Formalizing-Soft-Sciences/blob/8e665d2a9f6168e6448b2ca49fccbec87d57d3ad/research/publication-audit-2026-09-29/SOURCES.md) (proof or status).
- [Archived 67-declaration source/build receipt](https://github.com/Sodelin/Formalizing-Soft-Sciences/blob/8e665d2a9f6168e6448b2ca49fccbec87d57d3ad/projects/foundations/verification-manifest.json) (formal receipt).

**Connections:**

No theorem-transfer dependency is asserted by this card.

**Stable key:** softsciences.EXACT_OBSERVATION_BIAS_EVIDENCE. **Aliases:** Foundations I identification, measurement and learning; Soft Sciences B01 B02 B04.

</details>


<a id="cb-softsci-002"></a>
### Identical observations can conceal different intervention effects
**CB-SOFTSCI-002 · Soft Sciences · causal information loss**

**Question:** Can two explanations agree on every allowed observation and still disagree about what an intervention does?

**What we learned:** Yes. Two explicit Boolean models have identical observational records but different responses when treatment is set independently.

**What it lets someone do:** Show exactly why the permitted observational input alone cannot support a universally correct effect estimator.

**What we cannot conclude:** This elementary collision is not a general causal-discovery algorithm or a resolution of the richer homophily-versus-contagion problem.

**Kind:** counterexample. **Mathematical status:** Proved; archived Lean check recorded.

<details>
<summary>Exact scope, prior work, evidence and separate downstream work</summary>

**Exact statement and assumptions.** Six declarations concern BinaryModel outcome functions on Boolean treatment and background. The treatment-copy model Y=T and common-cause model Y=U give identical observed functions u -> (u,Y(u,u)) when T=U, but disagree at the intervention T=true,U=false. Their effectNumerator values are 2 and 0. Hence there is no estimator from the complete permitted observational function to Int that returns effectNumerator correctly for every BinaryModel. Equality of all treatment/background response values identifies the full model function. Interpreting the numerator as twice an average treatment effect additionally assumes uniform Boolean background.

**Origin.** project posed. Precisely specified project models, formalizing established reasoning rather than solving an author-designated external open problem.

**Prior work.** Observational non-identification is classical. Shalizi and Thomas (2011) supply a richer network-motivating predecessor, not an equivalent theorem proved by this Boolean example.

**Our contribution and attribution.** The original package gives a transparent checked collision and universal-estimator impossibility consequence in the declared finite model, with the observation/effect distinction explicit. This is formalization of an established principle, not a newly solved causal-inference open problem.

**Evidence, kept separate:**

- **Hand:** The repository's complete AI-assisted declaration/publication audit and this bounded actual-source reading support the stated model scope. No human peer-review or fresh worldwide novelty review is claimed.
- **Formal:** The archived Lean 4.19.0 foundations receipt covers the exact 67 solidarity/foundations declarations, with pinned source hashes and propext/Classical.choice/Quot.sound dependencies. The count includes support lemmas and examples. This audit did not rerun Lean.
- **Execution:** Successful historical workflow and source/axiom checks are recorded in the linked manifest; no scientific execution or fresh workflow inspection was performed for these cards.
- **Empirical:** Exact consequences of specified mathematical models. No empirical psychological, social or clinical law follows from formal correctness alone.

**Novelty:** Established mathematics or an already described source-model mechanism; the indexed contribution is precise formalization and source binding, not a claim to a new field-level discovery.

**Separate downstream work (does not reopen this result):** General DAG identification, causal assumptions in real data, network homophily/contagion separation and the October restricted-intervention upper/lower theorems have different contracts. They are not proved by this six-declaration example.

**Proof, review and related source links:**

- [Boolean causal construction and proofs](https://github.com/Sodelin/Formalizing-Soft-Sciences/blob/8e665d2a9f6168e6448b2ca49fccbec87d57d3ad/SocialScience/Causality.lean) (proof or status).
- [Complete declaration inventory and role audit](https://github.com/Sodelin/Formalizing-Soft-Sciences/blob/8e665d2a9f6168e6448b2ca49fccbec87d57d3ad/research/publication-audit-2026-09-29/THEOREM-BY-THEOREM.md) (proof or status).
- [Prior-work comparison and reading limits](https://github.com/Sodelin/Formalizing-Soft-Sciences/blob/8e665d2a9f6168e6448b2ca49fccbec87d57d3ad/research/publication-audit-2026-09-29/SOURCES.md) (proof or status).
- [Archived 67-declaration source/build receipt](https://github.com/Sodelin/Formalizing-Soft-Sciences/blob/8e665d2a9f6168e6448b2ca49fccbec87d57d3ad/projects/foundations/verification-manifest.json) (formal receipt).

**Connections:**

- [CB-CAUSAL-001](#cb-causal-001): **same principle**. Both distinguish observational information from intervention information, but this Boolean example is not a supplier of the later full restricted-query theorem.

**Stable key:** softsciences.BOOLEAN_OBSERVATIONAL_EFFECT_COLLISION. **Aliases:** Foundations I B03; Soft Sciences Boolean causal non-identification.

</details>


<a id="cb-softsci-003"></a>
### Connectedness, trust and an acceptable deal are different requirements
**CB-SOFTSCI-003 · Soft Sciences · contact structure, incentives and allocation**

**Question:** Does a connected society automatically have trust and incentives to cooperate?

**What we learned:** No such implication follows from the model. Very sparse direct contacts allow unbounded reach, while cooperation and participation obey separate exact payoff and budget conditions.

**What it lets someone do:** Keep structural reach, group membership, trust and incentive compatibility separate when making an argument.

**What we cannot conclude:** The model does not show that labels never affect people, that institutions can finance sanctions, or that a political intervention works.

**Kind:** theorem. **Mathematical status:** Proved; archived Lean check recorded.

<details>
<summary>Exact scope, prior work, evidence and separate downstream work</summary>

**Exact statement and assumptions.** The 26 declarations comprise the original 16 Solidarity and 10 CollectiveAction declarations. On Nat with successor/predecessor adjacency, every pair is connected, reach from zero is unbounded, and every neighbor of a belongs to {a+1,a-1}; the last theorem is containment, not a separate formal degree-cardinality statement. Overlapping membership and a separately defined empty trust relation are explicit examples. In the integer one-shot payoff (benefit if the other contributes) minus (cost if one contributes, sanction otherwise), mutual contribution is weakly stable against unilateral withdrawal iff cost<=sanction. For fixed uncongested task capabilities and participation reward>=cost with zero outside option, total surplus need not make an offered allocation acceptable. With unrestricted integer transfers, there exists an acceptable two-person share iff costA+costB<=budget; acceptable shares are exactly [costA,budget-costB].

**Origin.** project posed. Precisely specified project models, formalizing established reasoning rather than solving an author-designated external open problem.

**Prior work.** Elementary graph connectivity, set inclusion, unilateral payoff comparisons and transfer feasibility are established mathematics. The source's broader social interpretation and formal-social-choice bibliography are motivation, not empirical implications or claims to supersede prior formalization.

**Our contribution and attribution.** The original solidarity and foundations package formalizes the separation of mechanisms and exact threshold examples. The preserved Mathematics-of-Psychology copy contains the same 16 solidarity declarations, verified here by identical Git blob 992e225d3385e02ec74274aa656d34de34a4244f; it is not an extra result set.

**Evidence, kept separate:**

- **Hand:** The repository's complete AI-assisted declaration/publication audit and this bounded actual-source reading support the stated model scope. No human peer-review or fresh worldwide novelty review is claimed.
- **Formal:** The archived Lean 4.19.0 foundations receipt covers the exact 67 solidarity/foundations declarations, with pinned source hashes and propext/Classical.choice/Quot.sound dependencies. The count includes support lemmas and examples. This audit did not rerun Lean.
- **Execution:** Successful historical workflow and source/axiom checks are recorded in the linked manifest; no scientific execution or fresh workflow inspection was performed for these cards.
- **Empirical:** Exact consequences of specified mathematical models. No empirical psychological, social or clinical law follows from formal correctness alone.

**Novelty:** Established mathematics or an already described source-model mechanism; the indexed contribution is precise formalization and source binding, not a claim to a new field-level discovery.

**Separate downstream work (does not reopen this result):** Actual trust, cognitive limits, transfer restrictions, bargaining, sanction financing, dynamic stability and the full political recommendation require separate models or evidence. Labels are absent from the specified payoff, not empirically proved irrelevant.

**Proof, review and related source links:**

- [Solidarity source and 16 declarations](https://github.com/Sodelin/Formalizing-Soft-Sciences/blob/8e665d2a9f6168e6448b2ca49fccbec87d57d3ad/Solidarity.lean) (proof or status).
- [Collective-action source and 10 declarations](https://github.com/Sodelin/Formalizing-Soft-Sciences/blob/8e665d2a9f6168e6448b2ca49fccbec87d57d3ad/SocialScience/CollectiveAction.lean) (proof or status).
- [Complete declaration inventory and role audit](https://github.com/Sodelin/Formalizing-Soft-Sciences/blob/8e665d2a9f6168e6448b2ca49fccbec87d57d3ad/research/publication-audit-2026-09-29/THEOREM-BY-THEOREM.md) (proof or status).
- [Prior-work comparison and reading limits](https://github.com/Sodelin/Formalizing-Soft-Sciences/blob/8e665d2a9f6168e6448b2ca49fccbec87d57d3ad/research/publication-audit-2026-09-29/SOURCES.md) (proof or status).
- [Archived 67-declaration source/build receipt](https://github.com/Sodelin/Formalizing-Soft-Sciences/blob/8e665d2a9f6168e6448b2ca49fccbec87d57d3ad/projects/foundations/verification-manifest.json) (formal receipt).
- [Preserved psychology checkpoint, explicitly not an additional set](https://github.com/Sodelin/Mathematics-of-Psychology-Formalized/blob/db3a4d90e252449f9d7c69f68b6e8bc5685f4fcc/README.md) (proof or status).

**Connections:**

No theorem-transfer dependency is asserted by this card.

**Stable key:** softsciences.NETWORK_REACH_AND_PARTICIPATION. **Aliases:** Original 16 solidarity declarations; Mathematics of Psychology preserved checkpoint; Foundations I B05.

</details>


<a id="cb-softsci-004"></a>
### Pooling groups can reverse both within-group comparisons
**CB-SOFTSCI-004 · Soft Sciences · aggregation and interpretation**

**Question:** Can a combined comparison point in the opposite direction from every separate context?

**What we learned:** Yes. Checked positive counts favor one group in both strata and the other after pooling.

**What it lets someone do:** Use a transparent exact example to show why an aggregate comparison needs its context and weighting assumptions.

**What we cannot conclude:** This is not a newly discovered paradox, evidence of its frequency in real data, or an automatic causal-adjustment rule.

**Kind:** counterexample. **Mathematical status:** Proved; archived Lean check recorded.

<details>
<summary>Exact scope, prior work, evidence and separate downstream work</summary>

**Exact statement and assumptions.** Eight declarations include a valid positive-denominator witness of Simpson reversal: 9/10>80/100 and 20/100>1/10, but (9+20)/(10+100)=29/110 < (80+1)/(100+10)=81/110. Comparisons are formalized by cross multiplication on natural counts. Integer addition preserves two supplied weak inequalities under equal weighting. The component-nonidentification and recoding consequences explicitly reuse Identifiability.baseline_not_identified and postprocess_preserves_equivalence; they are not independent new discoveries.

**Origin.** project posed. Precisely specified project models, formalizing established reasoning rather than solving an author-designated external open problem.

**Prior work.** Simpson's 1951 analysis is the classical predecessor. The source audit distinguishes its historical example from this package's different strict numerical witness.

**Our contribution and attribution.** The original package checks the synthetic counts, all inequality directions and the reuse of existing information-loss lemmas. This is a reproducible formal example of established mathematics.

**Evidence, kept separate:**

- **Hand:** The repository's complete AI-assisted declaration/publication audit and this bounded actual-source reading support the stated model scope. No human peer-review or fresh worldwide novelty review is claimed.
- **Formal:** The archived Lean 4.19.0 foundations receipt covers the exact 67 solidarity/foundations declarations, with pinned source hashes and propext/Classical.choice/Quot.sound dependencies. The count includes support lemmas and examples. This audit did not rerun Lean.
- **Execution:** Successful historical workflow and source/axiom checks are recorded in the linked manifest; no scientific execution or fresh workflow inspection was performed for these cards.
- **Empirical:** Exact consequences of specified mathematical models. No empirical psychological, social or clinical law follows from formal correctness alone.

**Novelty:** Established mathematics or an already described source-model mechanism; the indexed contribution is precise formalization and source binding, not a claim to a new field-level discovery.

**Separate downstream work (does not reopen this result):** Choosing scientifically appropriate strata, causal adjustment, observed prevalence and empirical uncertainty require additional assumptions and evidence. They are not unresolved parts of this completed finite witness.

**Proof, review and related source links:**

- [Aggregation witness and exact reused proofs](https://github.com/Sodelin/Formalizing-Soft-Sciences/blob/8e665d2a9f6168e6448b2ca49fccbec87d57d3ad/SocialScience/Aggregation.lean) (proof or status).
- [Complete declaration inventory and role audit](https://github.com/Sodelin/Formalizing-Soft-Sciences/blob/8e665d2a9f6168e6448b2ca49fccbec87d57d3ad/research/publication-audit-2026-09-29/THEOREM-BY-THEOREM.md) (proof or status).
- [Prior-work comparison and reading limits](https://github.com/Sodelin/Formalizing-Soft-Sciences/blob/8e665d2a9f6168e6448b2ca49fccbec87d57d3ad/research/publication-audit-2026-09-29/SOURCES.md) (proof or status).
- [Archived 67-declaration source/build receipt](https://github.com/Sodelin/Formalizing-Soft-Sciences/blob/8e665d2a9f6168e6448b2ca49fccbec87d57d3ad/projects/foundations/verification-manifest.json) (formal receipt).

**Connections:**

- [CB-SOFTSCI-001](#cb-softsci-001): **reused theorem**. Two of the eight declarations directly reuse the identification and postprocessing results indexed in CB-SOFTSCI-001; they do not add two distinct discoveries.

**Stable key:** softsciences.SYNTHETIC_AGGREGATION_REVERSAL. **Aliases:** Foundations I B06; Soft Sciences checked Simpson witness.

</details>


<a id="cb-softsci-005"></a>
### In one published model fragment, the action determines what can be learned
**CB-SOFTSCI-005 · Soft Sciences · published-model source verification**

**Question:** Does the specified observation record distinguish the safe and dangerous states?

**What we learned:** The fixed avoidance path produces identical complete records in both states, so every deterministic classifier fails on one. The specified approach path distinguishes the two.

**What it lets someone do:** Inspect and reuse a precisely checked connection between a published model's selected tables and its information limitation.

**What we cannot conclude:** This is not evidence that a treatment works, a learned policy, a reproduction of the full simulation or a new discovery of the already described mechanism.

**Kind:** theorem. **Mathematical status:** Proved; archived Lean check recorded.

<details>
<summary>Exact scope, prior work, evidence and separate downstream work</summary>

**Exact statement and assumptions.** The 18 declarations are 14 PublishedCBT trajectory/observation/weight results and four SourceBridge table equalities. In a deterministic four-time-point fragment with externally fixed approach/avoid behavior, spider present, two Boolean danger states and all four declared observation modalities, the avoidance record is identical across states and admits no classifier List Observation -> Bool correct on both; the approach record is injective on those states. Integer-scaled implicit columns have mass 10u and are nonnegative under 0<u and 0<=c<=10u. Equality of the approach columns is exactly c=u, corresponding to normalized CABi=0.1, with other source weight/prior identities and finite sensory/affective/transition/implicit table bridges proved. This is not a semantics proof for the upstream MATLAB/SPM execution.

**Origin.** project posed. Exact verification of a selected fragment of Smith, Moutoussis and Bilek's published computational model, not a solved author-designated open conjecture.

**Prior work.** Smith, Moutoussis and Bilek (2021), Scientific Reports 11,10128, DOI 10.1038/s41598-021-89047-0, already explain that avoidance prevents informative observations. The original paper and pinned CBT_model.m remain the mechanism's source; the contribution here is explicit formal verification and bounded source binding.

**Our contribution and attribution.** The original Formalizing Soft Sciences clinical package checks the all-modality finite record, impossibility/recovery pair, weight identities and source-table equalities. Its extractor records ten matrices and six selected assignments against upstream commit 82a0a3d75b0bdc08d2b78cdf2201d7aa626c27a3. Counts include supporting identities and bridges, not 18 clinical discoveries.

**Evidence, kept separate:**

- **Hand:** The existing publication audit read the decisive original-paper model/results/discussion passages and distinguishes the already described mechanism from its formalized fragment. This recovery read both declaration-bearing clinical source files and SourceTables; it is not independent clinical peer review.
- **Formal:** The published coverage record reports Lean 4.19.0 build and axiom reports for all 18 clinical declarations, separate from the earlier 67. The scope is the declared finite observation/weight fragment and four source bridges, not all MATLAB/SPM semantics.
- **Execution:** Historical successful clinical workflow 36408149787 and the publication coverage record document the build, all 18 axiom checks, ten extracted matrices and six selected assignments. No code, extractor, simulator or build was run during this audit.
- **Empirical:** No patient outcome, treatment recommendation or empirical efficacy claim is established by these model proofs.

**Novelty:** Established mathematics or an already described source-model mechanism; the indexed contribution is precise formalization and source binding, not a claim to a new field-level discovery.

**Separate downstream work (does not reopen this result):** The separate uncertainty-tolerance/partial-approach/generalization candidate remains on hold and is not restarted by this indexing. Posterior updating, agent-selected policy, exposure learning, context generalization, full simulator semantics and clinical effectiveness are outside the completed fragment.

**Proof, review and related source links:**

- [Clinical observation and weight theorem bodies](https://github.com/Sodelin/Formalizing-Soft-Sciences/blob/8e665d2a9f6168e6448b2ca49fccbec87d57d3ad/clinical/ClinicalModels/PublishedCBT.lean) (proof or status).
- [Four source-bridge proofs](https://github.com/Sodelin/Formalizing-Soft-Sciences/blob/8e665d2a9f6168e6448b2ca49fccbec87d57d3ad/clinical/ClinicalModels/SourceBridge.lean) (proof or status).
- [Exact source tables](https://github.com/Sodelin/Formalizing-Soft-Sciences/blob/8e665d2a9f6168e6448b2ca49fccbec87d57d3ad/clinical/ClinicalModels/SourceTables.lean) (proof or status).
- [Coverage and archived clinical verification scope](https://github.com/Sodelin/Formalizing-Soft-Sciences/blob/8e665d2a9f6168e6448b2ca49fccbec87d57d3ad/PUBLICATION-COVERAGE-2026-09-29.md) (proof or status).
- [Recorded successful clinical check](https://github.com/Sodelin/Formalizing-Soft-Sciences/actions/runs/36408149787) (formal receipt).
- [Original pinned MATLAB model](https://github.com/rssmith33/Simulating_Cognitive_Behavioral_Therapy/blob/82a0a3d75b0bdc08d2b78cdf2201d7aa626c27a3/CBT_model.m) (source).
- [Original published model](https://doi.org/10.1038/s41598-021-89047-0) (source).
- [Source/prior-work comparison](https://github.com/Sodelin/Formalizing-Soft-Sciences/blob/8e665d2a9f6168e6448b2ca49fccbec87d57d3ad/research/publication-audit-2026-09-29/SOURCES.md) (proof or status).
- [Separate later candidate remains on hold](https://github.com/Sodelin/Formalizing-Soft-Sciences/blob/8e665d2a9f6168e6448b2ca49fccbec87d57d3ad/research/new-wave-2026-09-30/STARTER-ASSESSMENT.md) (proof or status).

**Connections:**

- [CB-SOFTSCI-001](#cb-softsci-001): **same principle**. Both concern whether observations distinguish explanations. The clinical proof is not asserted to import the foundations theorems or to supply a general learning algorithm.

**Stable key:** softsciences.PUBLISHED_CBT_OBSERVATION_FRAGMENT. **Aliases:** Published-CBT fragment, 18 declarations; Smith–Moutoussis–Bilek observation/source-table verification.

</details>

<a id="cb-nanuq-003"></a>
### Five labels suffice to test the whole anchor-parameter domain, and four do not
**CB-NANUQ-003 · NANUQ · sharp parameter-test reduction**

**Question:** How small can the test configurations be when checking which scoring parameters always work?

**What we learned:** For the stated anchor-positivity criterion, checking every representation through five distinct labels is enough for all finite sizes; stopping at four misses a real obstruction.

**What it lets someone do:** Replace an unbounded parameter test with the proved sharp finite collection.

**What we cannot conclude:** Five labels is not five quartet queries, a five-label restriction of every configuration, or a universal biological sample-size claim.

**Kind:** theorem. **Mathematical status:** Proved (not Lean formalized).

<details>
<summary>Exact scope, prior work, evidence and separate downstream work</summary>

**Exact statement and assumptions.** For every real four-score vector (c,s,a,o), with the exceptional anchor-sharing entry fixed at 1, universal nonnegativity of every circular anchor coefficient on finite adjacent singleton/doubleton plane-tree representations with n>=3 distinct taxon labels is equivalent to checking all such coefficients with at most five total labels, and to s=o=1, 1/2<=a<=1, 0<=c<=a. Five is the least sufficient cutoff: an actual five-label representation has a negative coefficient at (1,1,1/2,1), while all three/four-label tests pass. Labels include duplicated taxa. The proof retains the six-label structural reduction and uses equality of the five/six-label normalized inequality collections; it does not assert that each six-label configuration restricts to five while preserving its coefficient.

**Origin.** project posed. A sharp parameter-test corollary of the all-level anchor-certificate programme, not a claimed external five-label conjecture.

**Prior work.** The accepted score-independent six-label restriction, exhaustive adjacent-copy systems and independent symbolic parameter-domain audit are reused. Positive scaling of a linear inequality preserves its sign; classical linear-inequality reasoning is not a new invention.

**Our contribution and attribution.** The original Samuel package identifies the sharp five-label test cutoff from complete normalized-row equality and an actual four-cutoff failure witness, rather than merely comparing row counts. This is an existing completed deduction, not new work by this card.

**Evidence, kept separate:**

- **Hand:** The complete cutoff manuscript derives the result from the accepted restriction, independently audited 16-row parameter system and actual five-label obstruction. Those ingredient reviews are explicit; no separate fresh whole-cutoff review is claimed here. The older obstruction note's pending five-cutoff sentence is superseded by the complete FIVE-TAXON-THRESHOLD proof, not a remaining mathematical gap.
- **Formal:** The source cites an archived Lean proof of finite-row algebra and the four-label box obstruction. That does not formalize the unbounded representation, enumeration or full sharp-cutoff theorem, and this card makes no whole-theorem kernel claim.
- **Execution:** The original independent symbolic receipt covers 122 saved systems and 24,667 coefficients; all 16 normalized nonzero rows have witnesses using at most five labels. The focused obstruction has a saved exact graph/quartet check. None was rerun for this card.
- **Empirical:** A mathematical statement about the declared representation or distance, not a measured biological claim.

**Novelty:** Unresolved; project correctness and source correspondence do not certify historical priority or worldwide novelty.

**Separate downstream work (does not reopen this result):** Full end-to-end Lean formalization is separate. The cutoff concerns universal parameterized anchor positivity, not a necessity characterization for aggregated unweighted network distances, a minimal test for the fixed original score, or the exact-query minimax Q*(5). The stronger global four-score-cone continuation has a different statement and acceptance history.

**Proof, review and related source links:**

- [Complete sharp five-label cutoff theorem](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/nanuq-all-level-2026-09-29/FIVE-TAXON-THRESHOLD.md) (proof or status).
- [Independent exact row/domain audit](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/nanuq-all-level-2026-09-29/PARAMETER-DOMAIN-AUDIT.md) (hand review).
- [Original all-level restriction supplier](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/nanuq-all-level-2026-09-29/ALL-LEVEL-PROOF.md) (proof or status).
- [Actual five-label obstruction and original evidence](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/nanuq-all-level-2026-09-29/source-development/formal-full/FOUR-TAXON-OBSTRUCTION.md) (proof or status).

**Connections:**

- [CB-NANUQ-002](#cb-nanuq-002): **reused theorem**. Reuses the original all-level package's structural restriction and audited finite parameter suppliers; it sharpens the parameter-test collection, not the source-level bound.
- [CB-EXACTQUERY-002](#cb-exactquery-002): **same principle**. Both have sharp small cases, but five total labels in a parameter test is not five adaptive quartet queries.

**Stable key:** september.NANUQ.SHARP_PARAMETER_CUTOFF. **Aliases:** Five total taxa sharp anchor-parameter cutoff.

</details>

<a id="cb-nanuq-004"></a>
### Only the two extreme copies are needed for quartet sets and split unions
**CB-NANUQ-004 · NANUQ · observation-preserving copy reduction**

**Question:** Can many contiguous copies of the same label be reduced without losing the requested structural information?

**What we learned:** Yes. Keeping the first and last copy preserves every distinct quartet set and the union of displayed splits.

**What it lets someone do:** Transfer the paired-copy quartet and distance results to arbitrary finite contiguous copy blocks.

**What we cannot conclude:** The full family of displayed trees can shrink, and occurrence counts or probability distributions need not be preserved.

**Kind:** theorem. **Mathematical status:** Proved (not Lean formalized).

<details>
<summary>Exact scope, prior work, evidence and separate downstream work</summary>

**Exact statement and assumptions.** Let T be a finite unrooted plane binary tree with at least four taxon labels, each occupying one nonempty contiguous block of physical tips in the cyclic order. Retain the first and last occurrence of each block, or its sole occurrence for a singleton, then restrict and suppress degree-two vertices. The resulting tree has at most twice as many physical tips as labels and has exactly the same complete system of distinct displayed quartet sets and the same union of displayed splits under independent one-occurrence-per-label selections. The common taxon order and quartet-based original NANUQ distance/anchor formulas are preserved. Witness selections may depend on the quartet; no single globally preserving selection or equality of full displayed-tree families is asserted.

**Origin.** project posed. An abstract plane-tree extension of the existing adjacent-copy representation, with biological admission deliberately separate.

**Prior work.** Tree restriction, median components and the circular boundary-quartet split criterion are reused. The paired-tip all-level distance/support and parameter results are prior suppliers. Their reuse is not a new claim to have invented quartet reconstruction.

**Our contribution and attribution.** The original complete hand proof gives a one-block median argument and successive replacement of four selected occurrences, yielding exact set preservation. Its explicit caterpillar shows that the weaker observation target is essential because a full displayed tree can disappear.

**Evidence, kept separate:**

- **Hand:** The complete original proof and named paired-tip suppliers received a separate coordinating AI hand PASS on 23 October. The review checks median-component endpoint replacement, all quartet witnesses, common-order split-union preservation and the explicit lost-full-tree example. This adds independent hand review to already-complete authorship; it is not a new theorem, human peer review or rerun of inherited computational suppliers.
- **Formal:** No full kernel-checked copy-block theorem is asserted; the later 53-source formal component is not silently upgraded to cover it.
- **Execution:** The original manuscript records a direct exact check of the single caterpillar example, not a stored universal execution certificate. The theorem follows from its exposed hand argument; nothing was rerun here.
- **Empirical:** A mathematical statement about the declared representation or distance, not a measured biological claim.

**Novelty:** Unresolved; project correctness and source correspondence do not certify historical priority or worldwide novelty.

**Separate downstream work (does not reopen this result):** The separate whole-extension hand review is complete. Full Lean formalization remains a distinct validation task. Interleaved blocks, nonbinary medians, infinite trees, dependent cross-label selections and higher-indegree biological networks are not covered without additional source arguments. Full tree families and weighted probabilities are explicitly not preserved.

**Proof, review and related source links:**

- [Original complete copy-block proof and counterexample](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/nanuq-all-level-2026-09-29/CONTIGUOUS-MULTICOPY-EXTENSION.md) (proof or status).
- [Independently accepted boundary-quartet/support supplier](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/nanuq-all-level-2026-09-29/ALL-LEVEL-SUPPORT-STRUCTURAL-AUDIT.md) (hand review).
- [Original all-level theorem and evidence boundary](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/nanuq-all-level-2026-09-29/README.md) (proof or status).

**Connections:**

- [CB-NANUQ-002](#cb-nanuq-002): **proved adapter**. The complete hand reduction transfers paired-tip quartet-based distance/support statements to the stated abstract contiguous-copy class; it is not an adapter from every biological network.

**Later independent review:** [Whole-extension hand PASS, 23 October](https://github.com/Sodelin/Research-Commons/blob/afed31041a50fd18675402c293a3a11a2b5f87d5/research/2026-10-23-dot-contiguous-copy-review/CONTIGUOUS-MULTICOPY-INDEPENDENT-HAND-REVIEW-20261023.md). Authorship was already complete before this review.

**Stable key:** september.NANUQ.CONTIGUOUS_COPY_EXTREMES. **Aliases:** Contiguous multicopy extreme-occurrence reduction.

</details>

<a id="cb-nanuq-005"></a>
### Rounding tolerates errors below one half, and the uniform limit is sharp
**CB-NANUQ-005 · NANUQ · exact recovery under bounded matrix error**

**Question:** How much error can the original distance matrix tolerate while still permitting exact recovery?

**What we learned:** Entrywise error strictly below one half allows exact matrix recovery by rounding; with a correct circular order, it also recovers the split support. The uniform threshold cannot be enlarged.

**What it lets someone do:** Use a sharp deterministic robustness guarantee when the stated raw-matrix error promise is justified.

**What we cannot conclude:** This does not supply a statistical estimator, a number of gene samples, an order-finding algorithm or a guarantee for arbitrarily rescaled distances.

**Kind:** theorem. **Mathematical status:** Proved (not Lean formalized).

<details>
<summary>Exact scope, prior work, evidence and separate downstream work</summary>

**Exact statement and assumptions.** For every finite binary semi-directed LSA-rootable outer-labeled planar galled network on at least four taxa in the pinned source class, the original unnormalized NANUQ distance has integer entries. If an observed matrix has entrywise sup-norm error strictly below 1/2, nearest-integer rounding recovers the exact full raw matrix without needing an order. Given a correct common circular order, the accepted exact-support theorem then recovers the displayed-split union. An admitted four-taxon tree/cycle pair has raw matrices at sup-norm distance 1 and different supports; their common midpoint defeats every decoder at closed error radius 1/2 and every larger strict radius, even with the correct order supplied. This is a sharp uniform result over the class, not a separate sharpness claim for every fixed larger taxon count.

**Origin.** project posed. A deterministic robustness and sharpness continuation of the all-level original-NANUQ theorem.

**Prior work.** Nearest-integer recovery from an error below half the lattice spacing and indistinguishable-midpoint lower bounds are elementary established principles. The existing exact-support theorem and source admission provide the model-specific content.

**Our contribution and attribution.** The original side-package deduction and independent integration review establish the integer-lattice improvement over direct coefficient thresholding and check an actual admitted tree/cycle endpoint pair. This restores an existing sharp bound without claiming a new estimator or discovery.

**Evidence, kept separate:**

- **Hand:** The independent integration review explicitly accepts the sharp raw-noise statement, including integer-lattice reasoning and binary/galled/LSA/outer-planar endpoint admission. It does not claim an independent audit of every side-package assertion.
- **Formal:** No complete kernel-checked proof of this sharp-noise theorem is asserted.
- **Execution:** The original review records one successful Node replay with parsed JSON matching the saved side-package result and exact endpoint arithmetic. Those are archived results; no replay or scientific computation was performed for this card.
- **Empirical:** A mathematical statement about the declared representation or distance, not a measured biological claim.

**Novelty:** Unresolved; project correctness and source correspondence do not certify historical priority or worldwide novelty.

**Separate downstream work (does not reopen this result):** A justified empirical error bound, biological estimator and statistical sample complexity are separate. Distance rescaling changes the radius. The earlier strict 1/4 coefficient-threshold guarantee remains sufficient but is not the optimal raw-matrix guarantee. No fixed-n optimum beyond the uniform class statement is asserted.

**Proof, review and related source links:**

- [Original quantitative corollary and scope](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/nanuq-all-level-2026-09-29/ADDITIONAL-COROLLARIES.md) (proof or status).
- [Independent sharp-noise proof review and archived replay](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/nanuq-all-level-2026-09-29/EXTREMALITY-REPLAY.md) (hand review).
- [Archived exact replay receipt](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/nanuq-all-level-2026-09-29/EXTREMALITY-REPLAY.json) (execution receipt).
- [Original all-level support theorem](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/nanuq-all-level-2026-09-29/ALL-LEVEL-PROOF.md) (proof or status).

**Connections:**

- [CB-NANUQ-002](#cb-nanuq-002): **reused theorem**. Exact recovery of the raw integer matrix is combined with the accepted circular exact-support theorem under a supplied correct order.

**Stable key:** september.NANUQ.SHARP_RAW_NOISE_RADIUS. **Aliases:** Optimal strict raw NANUQ noise radius 1/2.

</details>


<a id="cb-nanuq-002"></a>
### The original distance keeps exactly the displayed splits at every finite level
**CB-NANUQ-002 · NANUQ / BIO-1 · all-level phylogenetic structure**

**Question:** Does the same structural reconstruction work when ancestry networks have arbitrarily many reticulations?

**What we learned:** Yes, for the stated planar galled class: the original NANUQ distance is circular and its positive splits are exactly the displayed splits, at every finite level.

**What it lets someone do:** Use one split-representation theorem instead of a separate classification at each reticulation level.

**What we cannot conclude:** This does not recover every graph detail, apply to arbitrary networks, or prove a complete DNA inference pipeline.

**Kind:** theorem. **Mathematical status:** Proved (not Lean formalized).

<details>
<summary>Exact scope, prior work, evidence and separate downstream work</summary>

**Exact statement and assumptions.** Finite binary semi-directed, LSA-rootable, outer-labeled planar, galled networks on n>=4 labeled taxa, with the pinned parallel-edge/bigon conventions and arbitrary finite level and blob count. For every admitted network, the original NANUQ distance is circular decomposable in every chosen outer-embedding order and its positive split support is exactly the union of displayed-tree splits. The six-label finite reduction is a proof device, not a size or level restriction on the source.

**Origin.** published open problem. The source-result ledger matches the multiple-blob and level-three circularity/support questions in Holtgrefe et al., Theorem 4.7 and section 6, retaining the published structural hypotheses. The arbitrary-finite-level conclusion is a stronger project result.

**Prior work.** Original NANUQ and NANUQ+ scoring, classical circular split decomposition and the cited root-skeleton work are inherited. Holtgrefe et al.'s level-two theorem and stated extensions supply the recorded questions. The January 2026 correction does not change the target theorem.

**Our contribution and attribution.** The 29 September package's uniform occurrence-tree reduction, internally audited finite certificate, exact global blob composition and exact support transfer establish the all-level statement. This card restores that earlier result and preserves its source attribution; it is not a new discovery.

**Evidence, kept separate:**

- **Hand:** The original package records distinct internal structural, finite, composition and support audits of the computer-assisted mathematical proof; no external peer review is asserted.
- **Formal:** No complete kernel-checked proof of this exact claim is asserted. Separate narrower formal components do not upgrade the whole theorem.
- **Execution:** Archived evidence includes two distinct enumeration/quartet implementations, 122 systems and 24,667 anchor coefficients. These are proof-checking objects, not counts of discoveries or a new replay.
- **Empirical:** A mathematical source/oracle result, not measured biological validation.

**Novelty:** Unresolved; project correctness and source correspondence do not certify historical priority or worldwide novelty.

**Separate downstream work (does not reopen this result):** The later 53-source formal chain is a narrower formalization component, not full Lean verification of this all-level theorem. Biological observation/estimation and non-outer-planar networks need their own hypotheses. The separate anchor-positivity theorem is not silently replaced by the stronger authored global four-score-cone continuation.

**Proof, review and related source links:**

- [Original all-level proof, Samuel Alexander repository](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/nanuq-all-level-2026-09-29/ALL-LEVEL-PROOF.md) (proof or status).
- [Original audit inventory and attribution](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/nanuq-all-level-2026-09-29/README.md) (hand review).
- [Exact published-question correspondence](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/nanuq-all-level-2026-09-29/SOURCE-RESULT-LEDGER.md) (prior work).
- [Holtgrefe et al., primary prior work and section 6 questions](https://link.springer.com/article/10.1007/s11538-025-01549-4) (prior work).

**Connections:**

- [CB-NANUQ-001](#cb-nanuq-001): **same principle**. That later checked source-to-geometry chain is part of the formalization lineage; it neither replaces nor fully formalizes this earlier complete hand theorem.

**Stable key:** september.NANUQ.ALL_LEVEL. **Aliases:** 29 September all-level NANUQ Theorem A.

</details>

<a id="cb-exactquery-001"></a>
### Recover the split union and an order with optimally growing query cost
**CB-EXACTQUERY-001 · Exact quartet queries · adaptive information acquisition**

**Question:** How many exact quartet questions are needed when no circular order is supplied?

**What we learned:** The deterministic adaptive worst-case cost grows as Theta(n log n), and returns both all displayed splits and a compatible order.

**What it lets someone do:** Acquire the specified structural information without first asking every quartet question.

**What we cannot conclude:** This is optimal query growth, not near-linear runtime, a noisy-data guarantee or reconstruction of the hidden original network.

**Kind:** algorithm. **Mathematical status:** Proved (not Lean formalized).

<details>
<summary>Exact scope, prior work, evidence and separate downstream work</summary>

**Exact statement and assumptions.** Finite binary semi-directed, LSA-rootable, outer-labeled planar, galled networks on n>=4 labeled taxa, with the pinned parallel-edge/bigon conventions and arbitrary finite level and blob count. A query returns the complete set of distinct displayed resolved quartet topologies on four requested taxa, not multiplicities or gene-tree probabilities; the required output is the full nontrivial displayed-split union and any common circular order. No circle, tree or blob tree is supplied. The lower bound is ceil(log_3((2n-5)!!)). The accepted order learner uses at most (n-3)(11 ceil(log_2 n)+15) calls. For a supplied common circle and k distinct splits, the sparse component uses at most min{binomial(n,4),(n-2)(n-3),2n-6+4k ceil(log_2(n-1))}, without knowing k. The inherited source bound k<=13n-27 gives the matching O(n log n) joint upper bound; caching caps distinct calls by binomial(n,4).

**Origin.** project posed. EXACT-QUERY-01 asks this precise all-level complete-support, split-union-plus-order task. Related published quarnet reconstruction questions motivate it but are not identical.

**Prior work.** Tree-count lower bounds, circular-order methods and quartet reconstruction are established. Frohn et al. already prove O(n log n) quarnet-query reconstruction for level-one networks under a different graph/oracle/output contract. This theorem does not close their unrestricted tree-of-blobs query gap.

**Our contribution and attribution.** GPT-6 Astra Pro supplied the near-linear order learner and supplied-order sparse decoder. Codex root's returned structural/query/code reviews and integration establish the matching all-size bounds under the inherited source correspondence and linear split count. Sparse decoding is a component, not another counted discovery.

**Evidence, kept separate:**

- **Hand:** The returned integration accepts the all-size order/query proofs at internal hand-review level, conditional on the pinned accepted source suppliers. It supersedes the earlier pending query header.
- **Formal:** No complete kernel-checked proof of this exact claim is asserted. Separate narrower formal components do not upgrade the whole theorem.
- **Execution:** Archived independent implementation and graph-truth replays accompany the universal structural and amortization proofs. No re-execution here; finite agreement does not replace the all-size proof.
- **Empirical:** A mathematical source/oracle result, not measured biological validation.

**Novelty:** Unresolved; project correctness and source correspondence do not certify historical priority or worldwide novelty.

**Separate downstream work (does not reopen this result):** Sharp leading constants, efficient exact finite minimax, a full Lean proof and biological providers are separate. Complete support masks cannot silently be replaced by sampled presence/absence. The G7 exact-law/CAD master uses different source, observation and cost contracts; this result is not its alias. The outside Cross-Scale BIO-1 roadmap's structural query-policy gap is superseded by these completed exact-support results; its noisy NMSC acquisition layer is not thereby closed.

**Proof, review and related source links:**

- [Registered exact source, oracle and target](https://github.com/Sodelin/Research-Commons/blob/78ef5c855146cc88afdad78cd3475eae2399f141/communications/2026-09-30-root-exact-query-master.md) (proof or status).
- [Accepted matching-bound integration](https://github.com/Sodelin/Research-Commons/blob/78ef5c855146cc88afdad78cd3475eae2399f141/research/2026-09-30-query-resumption/OPTIMAL-ADAPTIVE-INTEGRATION.md) (hand review).
- [Independent order-space review](https://github.com/Sodelin/Research-Commons/blob/78ef5c855146cc88afdad78cd3475eae2399f141/research/2026-09-30-query-resumption/ASTRA-ORDER-REVIEW.md) (hand review).
- [Independent query/amortization review](https://github.com/Sodelin/Research-Commons/blob/78ef5c855146cc88afdad78cd3475eae2399f141/research/2026-09-30-query-resumption/ASTRA-QUERY-REVIEW.md) (hand review).
- [Supplied-order sparse decoder](https://github.com/Sodelin/Research-Commons/blob/78ef5c855146cc88afdad78cd3475eae2399f141/research/2026-09-30-astra-sparse-query/README.md) (proof or status).
- [Frohn et al., different level-one quarnet problem](https://arxiv.org/html/2409.06034v2) (prior work).
- [Earlier outside-repository BIO-1 roadmap, structural gap superseded only](https://github.com/Sodelin/Cross-Scale-Causal-Formalization/blob/28bdb75b8d057332e1bb32020d02e5eaea4c0517/research/open-problem-catalogs-2026-09-30/EXPLANATION-AND-PRIORITIES.md#bio-1-fewer-quartet-observations-with-justified-recovery) (historical problem statement).

**Connections:**

- [CB-NANUQ-002](#cb-nanuq-002): **reused theorem**. Uses the inherited all-level source correspondence and circular split structure, together with its separately reviewed linear split-count supplier.
- [CB-G7-001](#cb-g7-001): **same principle**. An earlier discrete adaptive-design theorem, not the later original-ID continuous exact-law design theorem.

**Stable key:** september.EXACT_QUERY.ADAPTIVE_THETA. **Aliases:** EXACT-QUERY-01 (asymptotic branch).

</details>

<a id="cb-exactquery-002"></a>
### The exact minima are one query for four taxa and five for five
**CB-EXACTQUERY-002 · Exact quartet queries · sharp small cases**

**Question:** Can the exact optimum be proved, rather than only its growth rate?

**What we learned:** Yes: the same structural task requires exactly one query at four taxa and five at five taxa.

**What it lets someone do:** Use proved finite benchmarks and distinguish an adaptive lower bound from a heuristic search result.

**What we cannot conclude:** The separately recovered six- and seven-taxon reports do not inherit the five-taxon independent hand acceptance.

**Kind:** theorem. **Mathematical status:** Proved (not Lean formalized).

<details>
<summary>Exact scope, prior work, evidence and separate downstream work</summary>

**Exact statement and assumptions.** Finite binary semi-directed, LSA-rootable, outer-labeled planar, galled networks on n>=4 labeled taxa, with the pinned parallel-edge/bigon conventions and arbitrary finite level and blob count. A query returns the complete set of distinct displayed resolved quartet topologies on four requested taxa, not multiplicities or gene-tree probabilities; the required output is the full nontrivial displayed-split union and any common circular order. For deterministic always-correct adaptive algorithms, Q*(4)=1 and Q*(5)=5. The five-taxon lower bound uses an admitted baseline and five admitted rivals, each changing only one quartet answer and the required split target; it remains valid when the common circle is supplied. A finite tested profile subset is not assumed to be a complete census.

**Origin.** project posed. Exact finite specializations of the registered EXACT-QUERY-01 minimax problem.

**Prior work.** Finite decision-tree minimax and indistinguishable-transcript adversaries are classical. The pinned actual-network fixtures and their source admission are inherited and explicitly reused.

**Our contribution and attribution.** Codex root's source-admitted five-rival adversary and independent graph-switching/minimax review certify the exact four- and five-taxon optima. Later GPT-6 Astra Pro computations reported Q*(6)=8 and Q*(7)=11 with separate author-run checkers, with a different evidence level recorded below.

**Evidence, kept separate:**

- **Hand:** Independent finite-minimax review records the graph-derived replay and full five-taxon hand adversary. No independent acceptance of the later Q*(6) or Q*(7) computations is inferred.
- **Formal:** No complete kernel-checked proof of this exact claim is asserted.
- **Execution:** Q*(4)/Q*(5) have archived independent replay and hand evidence. Separate author checkpoints report Q*(6)=8 and Q*(7)=11 with upper/lower certificate checks, but the save-only recovery did not recover the large catalogues, witnesses or certificate archives. No new replay or validation of those reports is claimed.
- **Empirical:** A mathematical source/oracle result, not measured biological validation.

**Novelty:** Unresolved; project correctness and source correspondence do not certify historical priority or worldwide novelty.

**Separate downstream work (does not reopen this result):** Recover and independently check the existing large six/seven-taxon certificate archives before upgrading their evidence. Their reported values are not erased by missing archives. Q*(8) was not optimized in the located record. No positive-error randomized optimum or closed all-n formula is asserted.

**Proof, review and related source links:**

- [Independent finite-minimax review](https://github.com/Sodelin/Research-Commons/blob/78ef5c855146cc88afdad78cd3475eae2399f141/research/2026-09-30-query-resumption/FINITE-MINIMAX-REVIEW.md) (hand review).
- [Accepted finite theorem within integration](https://github.com/Sodelin/Research-Commons/blob/78ef5c855146cc88afdad78cd3475eae2399f141/research/2026-09-30-query-resumption/OPTIMAL-ADAPTIVE-INTEGRATION.md) (hand review).
- [Historical six-taxon author report, not independently reaccepted](https://github.com/Sodelin/Research-Commons/blob/78ef5c855146cc88afdad78cd3475eae2399f141/research/2026-09-30-astra-exact-enumeration/CHECKPOINT.md) (historical report).
- [Historical seven-taxon author report, not independently reaccepted](https://github.com/Sodelin/Research-Commons/blob/78ef5c855146cc88afdad78cd3475eae2399f141/research/2026-09-30-astra-exact-enumeration/SEVEN-TAXON-CHECKPOINT.md) (historical report).
- [Exact source/certificate recovery boundary](https://github.com/Sodelin/Research-Commons/blob/78ef5c855146cc88afdad78cd3475eae2399f141/research/2026-09-30-astra-exact-enumeration/SAVE-ONLY-RECOVERY-20260930.md) (source recovery).

**Connections:**

- [CB-EXACTQUERY-001](#cb-exactquery-001): **same principle**. Same original query/target contract, but exact finite sharpness is not implied by the asymptotic theorem.

**Stable key:** september.EXACT_QUERY.FINITE_MINIMA. **Aliases:** EXACT-QUERY-01 (four/five-taxon sharp branch).

</details>

<a id="cb-exactquery-003"></a>
### The exact optimum has a finite constructive specification for every size
**CB-EXACTQUERY-003 · Exact quartet queries · constructive all-size optimum**

**Question:** Is the best adaptive query policy computable in principle for every number of taxa?

**What we learned:** Yes. A bounded representative theorem makes the exact admitted support catalogue finite, after which finite minimax produces an optimal policy and lower certificate.

**What it lets someone do:** Specify a complete exact optimizer without assuming that arbitrary compressed codes are real networks.

**What we cannot conclude:** The all-size specification is not an efficient implementation, a closed formula or a decision procedure for the different continuous-law G3 problem.

**Kind:** algorithm. **Mathematical status:** Proved (not Lean formalized).

<details>
<summary>Exact scope, prior work, evidence and separate downstream work</summary>

**Exact statement and assumptions.** Finite binary semi-directed, LSA-rootable, outer-labeled planar, galled networks on n>=4 labeled taxa, with the pinned parallel-edge/bigon conventions and arbitrary finite level and blob count. A query returns the complete set of distinct displayed resolved quartet topologies on four requested taxa, not multiplicities or gene-tree probabilities; the required output is the full nontrivial displayed-split union and any common circular order. Every actual admitted source has a same-profile, same-split-union and same-compatible-order admitted representative with at most 8n-14 unrooted vertices plus one root. Retaining actual branching blobs and shortening maximal two-port chains permits exhaustive bounded actual-graph generation and full admission filtering. Finite Bellman minimax on the resulting complete profile class computes Q*(n), an optimal deterministic policy and a recursively checkable lower certificate uniformly in n.

**Origin.** project posed. The exact all-n continuation of EXACT-QUERY-01, beyond abstract existence or asymptotic bounds.

**Prior work.** Classical finite minimax recursion is reused. The proof also reuses the pinned all-level structural facts; its indispensable source step is bounded actual-graph coverage, not an unsupported converse for arbitrary occurrence codes.

**Our contribution and attribution.** Codex root's exact-minimum construction and independent conditional source-normalization/profile reviews expose a uniform complete actual-source enumeration route for the discrete query game.

**Evidence, kept separate:**

- **Hand:** Independent profile and normalization reviews accept the actual-source reduction under the explicitly pinned structural suppliers. Those hypotheses are not replaced by an arbitrary-code assumption.
- **Formal:** No complete kernel-checked proof of this exact claim is asserted.
- **Execution:** The universal catalogue, minimax optimizer and certificate-checker specification was not implemented or executed as an all-size system. This is a constructive mathematical result; small-size computations do not constitute all-size execution.
- **Empirical:** A mathematical source/oracle result, not measured biological validation.

**Novelty:** Unresolved; project correctness and source correspondence do not certify historical priority or worldwide novelty.

**Separate downstream work (does not reopen this result):** A practical all-n implementation, better constants and further computed values are separate. The representative preserves discrete topology observations, not probability laws, original controls, branch lengths or full true-K forest kernels. It does not close G3 global continuous-law recognition or G4 finite INDEPENDENT-only forcing. The outside Cross-Scale BIO-1 roadmap's structural query-policy gap is superseded by these completed exact-support results; its noisy NMSC acquisition layer is not thereby closed.

**Proof, review and related source links:**

- [Uniform constructive exact-minimum theorem](https://github.com/Sodelin/Research-Commons/blob/78ef5c855146cc88afdad78cd3475eae2399f141/research/2026-09-30-query-resumption/EXACT-MINIMUM-THEOREM.md) (proof or status).
- [Actual-profile coverage review](https://github.com/Sodelin/Research-Commons/blob/78ef5c855146cc88afdad78cd3475eae2399f141/research/2026-09-30-query-resumption/EXACT-PROFILE-REVIEW.md) (hand review).
- [Actual-source normalization review](https://github.com/Sodelin/Research-Commons/blob/78ef5c855146cc88afdad78cd3475eae2399f141/research/2026-09-30-query-resumption/EXACT-NORMALIZATION-REVIEW.md) (hand review).
- [Accepted integration and implementation boundary](https://github.com/Sodelin/Research-Commons/blob/78ef5c855146cc88afdad78cd3475eae2399f141/research/2026-09-30-query-resumption/OPTIMAL-ADAPTIVE-INTEGRATION.md) (hand review).
- [Earlier outside-repository BIO-1 roadmap, structural gap superseded only](https://github.com/Sodelin/Cross-Scale-Causal-Formalization/blob/28bdb75b8d057332e1bb32020d02e5eaea4c0517/research/open-problem-catalogs-2026-09-30/EXPLANATION-AND-PRIORITIES.md#bio-1-fewer-quartet-observations-with-justified-recovery) (historical problem statement).

**Connections:**

- [CB-EXACTQUERY-001](#cb-exactquery-001): **proved adapter**. The hand-proved actual-source normalization identifies the complete finite profile game for this same source/oracle/output contract.
- [CB-G1-001](#cb-g1-001): **same principle**. Both simplify sources while preserving specified observations, but the observations and normalization theorems differ.
- [CB-G7-001](#cb-g7-001): **same principle**. Discrete exact support-policy optimization is not original-ID continuous exact-law/CAD design.

**Stable key:** september.EXACT_QUERY.UNIFORM_MINIMAX. **Aliases:** EXACT-QUERY-01 (uniform exact-minimum branch).

</details>

<a id="cb-topocontrol-001"></a>
### Three settings suffice for a probability floor, and four for certainty
**CB-TOPOCONTROL-001 · Topology controls · graph-informed environment design**

**Question:** With the network's control structure known, how many fixed settings expose every displayed split or quartet?

**What we learned:** The worst-case minima are three settings for the stated positive occurrence floor and four for guaranteed occurrence.

**What it lets someone do:** Use a sharp topology-focused control budget instead of forcing every routing combination.

**What we cannot conclude:** This does not recover all numerical laws, work with unknown control IDs or justify replacing topology-equivalent parts in every biological experiment.

**Kind:** theorem. **Mathematical status:** Proved (not Lean formalized).

<details>
<summary>Exact scope, prior work, evidence and separate downstream work</summary>

**Exact statement and assumptions.** Finite binary semi-directed, LSA-rootable, outer-labeled planar, galled networks on n>=4 labeled taxa, with the pinned parallel-edge/bigon conventions and arbitrary finite level and blob count. Every boundary port is taxon-bearing. Under the stated graph-informed contract, the graph/outer embedding or a certified interaction map is supplied, original hybrid IDs are retained, controls are fixed parameter-oblivious partial parent-forcing assignments, and forcing a parent leaves the other laws unchanged, and natural independent routing probabilities lie in [g,1-g] for 0<g<=1/2. Uniformly over this admitted source class, the worst-case minimum number of environments is three so that every displayed nontrivial split and quartet occurrence has probability at least g in at least one environment, and four so each occurs with certainty in at least one environment; these are not asserted to be the exact minima at every fixed taxon count. The source-admitted lower witnesses and switching-wise <=3-port topology quotient use the pinned source conventions.

**Origin.** project posed. A source-conditional topology-occurrence control problem in the September normalization-effects programme, not the later G7 exact numerical-law master or its marker/full-forcing menus.

**Prior work.** Classical coloring and control-cover reasoning and inherited structural source normalization are reused. Original routing/occurrence semantics, legal original-ID lift and the matching admitted lower witness are required for this experiment-count statement.

**Our contribution and attribution.** Codex Work's full report supplies the three/four-environment upper designs, actual-source lower witness and normalization/control-lift accounting. The complete later lower proof supersedes the earlier menu review's pending lower-bound wording.

**Evidence, kept separate:**

- **Hand:** The report and final checkpoint record the source-conditional full hand theorem; the menu review accepts the upper construction and the later source-admitted lower closes its named gap. Root inspection/replay evidence is separately recorded.
- **Formal:** No complete kernel-checked proof of this exact claim is asserted.
- **Execution:** Archived root verification records the binary-DAG/LSA lower witness, eight switched trees, twelve signed-pair cylinders, rejection of 378 two-row menus and 432 probability checks, alongside separate count and CF-discriminator checks. These are historical support for the exposed proof, not new executions or biological experiments.
- **Empirical:** An ideal mathematical control/occurrence result, not measured biological validation.

**Novelty:** Unresolved; project correctness and source correspondence do not certify historical priority or worldwide novelty.

**Separate downstream work (does not reopen this result):** This is an ideal graph-informed topology-occurrence optimum, not an unknown-graph learner, finite-data biological validation or numerical-law identification optimum. Topology-preserving erasure need not preserve quartet CFs or all original controls; the same report gives exact response-edge criteria and positive CF counterexamples. The passive biological quartet-CF normal-form proof is a separate authored result with a distinct acceptance history.

**Proof, review and related source links:**

- [Full normalized-controls theorem and source witness](https://github.com/Sodelin/Research-Commons/blob/78ef5c855146cc88afdad78cd3475eae2399f141/research/2026-09-30-normalization-effects/REPORT.md) (proof or status).
- [Final completed scope and supersession](https://github.com/Sodelin/Research-Commons/blob/78ef5c855146cc88afdad78cd3475eae2399f141/research/2026-09-30-normalization-effects/CHECKPOINT.md) (proof or status).
- [Earlier scoped menu review, read with later lower proof](https://github.com/Sodelin/Research-Commons/blob/78ef5c855146cc88afdad78cd3475eae2399f141/research/2026-09-30-normalization-effects/REVIEW-menu.md) (hand review).
- [Archived independent source/count/CF checks](https://github.com/Sodelin/Research-Commons/blob/78ef5c855146cc88afdad78cd3475eae2399f141/research/2026-09-30-normalization-effects/ROOT-VERIFICATION.json) (execution review).

**Connections:**

- [CB-G7-001](#cb-g7-001): **same principle**. A distinct early graph-informed topology-control optimum, not the later original-ID exact-law design master.
- [CB-G7-002](#cb-g7-002): **same principle**. The natural-marker programme observes different information and measures a different resource.
- [CB-G7-003](#cb-g7-003): **same principle**. The static full-forcing numerical-law covering-array optimum has a different menu and target.

**Stable key:** september.TOPOLOGY_CONTROL.THREE_FOUR. **Aliases:** NORMALIZATION-EFFECTS-20260930 (sharp environment-count branch).

</details>


<a id="cb-g1-001"></a>
### A smaller ancestry diagram can preserve the answers
**CB-G1-001 · G1 · preserving ancestry information**

**Question:** Can we simplify a complicated ancestry model without changing the answers it gives?

**What we learned:** Yes, for the stated class and the stated observations, there is a sharply bounded information-preserving core.

**What it lets someone do:** Replace admissible parts of a model with a smaller exact representation.

**What we cannot conclude:** This does not preserve every possible measurement, recover an unknown model, or certify a DNA analysis.

**Kind:** theorem. **Mathematical status:** Proved; named Lean scope checked.

<details>
<summary>Exact scope, evidence and separate downstream work</summary>

**Exact statement and assumptions.** For rooted-LSA outer-labelled planar cut-child directed multigraphs, including parallel original arc occurrences, the decorated-core linear bound and all-n sharpness preserve contextual completed unranked forest/register/root-history laws. The claimed endpoint is G1FullOriginalClassMasterAndSharpness.actual_G1_original_class_master_with_all_n_sharpness.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Graph decomposition and observation-preserving reduction are general antecedents; the original multigraph class, contextual law contract and sharp bound are the contribution.

**Our contribution.** Original-class decorated-core theorem, contextual preservation and sharp all-n bounds, with the selected accepted formal endpoint.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** The linked accepted release and fresh serial receipt cover this endpoint. The 467 source targets are build scope, not 467 independent discoveries.
- **Execution:** Fresh serial source build and endpoint audit are recorded; no new build was run for this board.
- **Empirical:** This is not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Separate downstream work (does not reopen this result):** Timed observations, arbitrary DNA readouts and unrelated source-recognition questions are not consequences of this theorem.

**Proof, review and other accepted-source links:**

- [Original-class theorem and package](https://github.com/Sodelin/Research-Commons/blob/0e3d36f4035d61a8ad6ae4dc5000b8cf9e54dc2d/research/2026-10-04-dot-complete-original-g1-1549z/README.md) (proof or status).
- [Fresh serial build receipt](https://github.com/Sodelin/Research-Commons/blob/2836ff8d1256ac29950e861db4bef53fd3c7ee53/research/2026-10-04-dot-complete-original-g1-1549z/certificate/fresh/SERIAL-BUILD-RECEIPT.json) (formal receipt).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** original.G1.CORE. **Aliases:** G1.

</details>

<a id="cb-g2-001"></a>
### Keeping fewer sampled individuals stays consistent
**CB-G2-001 · G2 · consistent sampling**

**Question:** If we discard some sampled individuals, do we get the same model as if we had sampled only those individuals?

**What we learned:** Yes, under the shared-source rules, including the documented timed version.

**What it lets someone do:** Compare small and large sampling panels without introducing incompatible ancestry histories.

**What we cannot conclude:** Agreement between two different models on an untimed summary does not automatically make their timing agree.

**Kind:** theorem. **Mathematical status:** Proved; named Lean scope checked.

<details>
<summary>Exact scope, evidence and separate downstream work</summary>

**Exact statement and assumptions.** Untimed all-panel projectivity uses one graph, physical tuple and registry, common or independent masks, empty panels, current owners and ancestral completion. The documented timed extension preserves the full recorded past, same-clock future paths, timed pruning and exact age-forgetting under its stated source contract.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Sampling consistency is a classical probabilistic principle; the contribution proves it for the stated source, register and full-history interfaces.

**Our contribution.** Source-faithful restriction/history consistency, including the documented full recorded-past timed extension.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** The G2 integration records accepted source/reused dependencies and aggregate coverage; its 68 current modules are not 68 new compilations.
- **Execution:** See the exact integration accounting; this board runs nothing.
- **Empirical:** This is not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Separate downstream work (does not reopen this result):** No unrestricted strong-Markov theorem or cross-source timed identification is inferred.

**Proof, review and other accepted-source links:**

- [Reconstructed G2 capabilities](https://github.com/Sodelin/Research-Commons/blob/207544deadd42be31cdb5062dfb32a15387fccab/research/2026-10-13-dot-g2-reconstructed-capabilities-0232z/README.md) (proof or status).
- [Unified integration and evidence accounting](https://github.com/Sodelin/Research-Commons/blob/207544deadd42be31cdb5062dfb32a15387fccab/research/2026-10-13-dot-g2-unified-integration-0238z/G2-UNIFIED-LAKE-INTEGRATION.md) (formal receipt).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** original.G2.PROJECTIVITY. **Aliases:** G2.

</details>

<a id="cb-g3-001"></a>
### Checking one proposed model is easier than ruling out every model
**CB-G3-001 · G3 · finding a real source**

**Question:** Can we check whether a proposed finite ancestry model fits exact observations?

**What we learned:** Yes. We can also search through finite models and eventually find one when a valid one exists.

**What it lets someone do:** Certify a fitting candidate rather than mistaking an approximation for an exact explanation.

**What we cannot conclude:** A search that has not found a model has not proved that no model exists.

**Kind:** algorithm. **Mathematical status:** Proved (not Lean formalized).

<details>
<summary>Exact scope, evidence and separate downstream work</summary>

**Exact statement and assumptions.** With a fixed admitted finite graph/word and rational or effectively algebraic joint input, shared original IDs, parameters and registers, exact feasibility reduces to real-closed-field constraints. Enumeration of admitted finite sources recognizes YES. This does not bound physical append count or ensure NO termination.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Classical real algebraic decision procedures are reused after deriving the original-source polynomial constraints.

**Our contribution.** Explicit original-source reduction to fixed-shape real-algebraic feasibility and a sound YES enumeration.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result is needed or claimed for this mathematical statement.
- **Empirical:** This is not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Separate downstream work (does not reopen this result):** General NO termination is CB-G3-004.

**Proof, review and other accepted-source links:**

- [Original exact criterion](https://github.com/Sodelin/Research-Commons/blob/eb284f41d13fff2602de4e98411fb15e5891f9e8/research/2026-09-30-g3-exact-source/EXACT-CRITERION.md) (proof or status).
- [Source-reachability reduction](https://github.com/Sodelin/Research-Commons/blob/9d21c0727564ae0ba101039d97b07c614d17f2e1/research/2026-10-06-dot-g3-global-source-reachability-0019z/REDUCTION.md) (proof or status).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** original.G3.FIXED_SOURCE_YES. **Aliases:** G3 fixed-source feasibility; G3 YES enumeration.

</details>

<a id="cb-g3-002"></a>
### A supplied observation certificate can bound the search
**CB-G3-002 · G3 · finding a real source**

**Question:** Can extra certified observations make the search finite?

**What we learned:** Yes, for a specified shared-routing branch and a sufficiently rich supplied certificate.

**What it lets someone do:** Turn that certified input into a bounded same-source recognition problem.

**What we cannot conclude:** Missing the certificate means 'not established', not 'no model exists'.

**Kind:** theorem. **Mathematical status:** Proved (not Lean formalized).

<details>
<summary>Exact scope, evidence and separate downstream work</summary>

**Exact statement and assumptions.** The COMMON supplied-exposure branch uses nonzero nonnegative sparse polynomials, exact zero expectations of the same legal mixed bank, exhaustive finite protected/tie grammar and collapse-preserving additional COMMON rows. The accepted certificate composition needs no supplied actual target source. Under its exact effective encoding it yields bounded witnesses and finite graph/RCF recognition.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Detailed antecedent attribution has not yet been independently indexed for this card. Consult the linked proof/source register; no new historical-priority claim is inferred.

**Our contribution.** Derive a bounded same-source witness from the supplied legal exposure certificate without requiring the actual target source as input.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result is needed or claimed for this mathematical statement.
- **Empirical:** This is not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Separate downstream work (does not reopen this result):** Universal acquisition of such certificates and a full original parser/admission implementation are not delivered.

**Proof, review and other accepted-source links:**

- [Certificate-derived bounded witness](https://github.com/Sodelin/Research-Commons/blob/7cdbb35da93dc82ce5b8ddc8db91140537838774/research/2026-10-13-dot-certificate-bounded-witness-0223z/CERTIFICATE-DERIVED-BOUNDED-WITNESS-CANDIDATE.md) (proof or status).
- [Later acceptance](https://github.com/Sodelin/Research-Commons/blob/e9e31baf3767593ae6805924463c0bcb4fc08f0f/research/2026-10-13-dot-certificate-bounded-witness-0223z/INDEPENDENT-BOUNDED-WITNESS-REVIEW.md) (hand review).
- [Mandatory encoding clarification](https://github.com/Sodelin/Research-Commons/blob/e9e31baf3767593ae6805924463c0bcb4fc08f0f/research/2026-10-13-dot-certificate-bounded-witness-0223z/INPUT-ENCODING-CLARIFICATION.md) (proof or status).

**Connections:**
- [CB-G4-002](#cb-g4-002): **reused theorem**. Reuses the completed COMMON mechanism under its mandatory restrictions.

**Stable key:** original.G3.GIVEN_CERTIFICATE. 

</details>

<a id="cb-g3-003"></a>
### Some inputs allow us to acquire the needed certificate
**CB-G3-003 · G3 · finding a real source**

**Question:** Can the helpful certificate sometimes be found rather than handed to us?

**What we learned:** Yes, in accepted local branches with explicit nondegeneracy conditions.

**What it lets someone do:** Solve those cases using the real permitted observations.

**What we cannot conclude:** Failure of the local conditions does not settle all remaining cases.

**Kind:** algorithm. **Mathematical status:** Proved (not Lean formalized).

<details>
<summary>Exact scope, evidence and separate downstream work</summary>

**Exact statement and assumptions.** The accepted quadratic acquisition theorem Q uses an actual legal complete joint COMMON receiver, an acquired algebraic predicate, finite charts/residues and strict-domain rank/curvature conditions. Regular and fixed-residue supplier branches are also retained by the review.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Detailed antecedent attribution has not yet been independently indexed for this card. Consult the linked proof/source register; no new historical-priority claim is inferred.

**Our contribution.** Prove an actual observation-based certificate-acquisition branch under its rank and curvature hypotheses.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result is needed or claimed for this mathematical statement.
- **Empirical:** This is not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Separate downstream work (does not reopen this result):** Prove every realizable input enters an accepted acquisition branch, or supply another complete all-core mechanism.

**Proof, review and other accepted-source links:**

- [Quadratic acquisition acceptance](https://github.com/Sodelin/Research-Commons/blob/4a082a70ef5d604ffb2db89f988d88b6159f569d/research/2026-10-14-dot-g3-quadratic-acquisition-review-2313z/INDEPENDENT-REVIEW.md) (hand review).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** original.G3.LOCAL_ACQUISITION. 

</details>

<a id="cb-g3-004"></a>
### Can every exact input be decided?
**CB-G3-004 · G3 · finding a real source**

**Question:** Is there a method that always finishes and says whether any allowed finite ancestry model fits?

**What we learned:** That full question remains open in this register, despite the completed branches above.

**What it lets someone do:** Identify the precise missing step instead of rerunning already-solved special cases.

**What we cannot conclude:** Neither a failed search nor a fit to a limiting object proves a definitive answer.

**Kind:** question. **Mathematical status:** Unresolved mathematical implication.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** General G3 asks total recognition for all finite admissible rational/effectively algebraic joint inputs against every finite strict original source, with one graph, tuple and original-ID interpretation across all rows. A total input-computable bound on some witness, a complete NO mechanism, or an original-class impossibility theorem is still required.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Detailed antecedent attribution has not yet been independently indexed for this card. Consult the linked proof/source register; no new historical-priority claim is inferred.

**Our contribution.** A precise remaining total-recognition obligation, with completed special branches separated from it.

**Evidence, kept separate:**

- **Hand:** The inspected acceptances do not discharge the full quantifiers; this is not a theorem of impossibility.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result is needed or claimed for this mathematical statement.
- **Empirical:** This is not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining mathematical implication:** Close the total-decision obligation at the exact original source and finite-input interface.

**Proof, review and other accepted-source links:**

- [Original master statements](https://github.com/Sodelin/Research-Commons/blob/0c0dc21eed1046c405e86a92673a6d473a934b6d/research/2026-10-05-dot-original-g-master-priority-1913z/MASTER-STATEMENTS.md) (proof or status).
- [Directed obligation audit](https://github.com/Sodelin/Research-Commons/blob/4a082a70ef5d604ffb2db89f988d88b6159f569d/research/2026-10-16-g3-g4-obligation-audit-1930z/OBLIGATION-AUDIT.md) (proof or status).

**Connections:**
- [CB-G3-001](#cb-g3-001): **reused theorem**. Completed positive search is a supplier, not a total decider.
- [CB-G3-002](#cb-g3-002): **candidate connection**. A complete certificate-acquisition theorem could extend this branch.

**Stable key:** original.G3.TOTAL_RECOGNITION. **Aliases:** G3 general.

</details>

<a id="cb-g4-001"></a>
### Some hidden information can be recovered by permitted tests
**CB-G4-001 · G4 · knowing when observations are enough**

**Question:** Can legal observations reveal the behaviour of a hidden piece of a model?

**What we learned:** Yes, in the specified finite-copy setting; a fixed four-taxon wrapper can recover a private chain's full forest response.

**What it lets someone do:** Use those observation adapters rather than assume hidden states are directly visible.

**What we cannot conclude:** This is not a stopping rule for every unknown-size model or every weaker measurement.

**Kind:** theorem. **Mathematical status:** Proved (not Lean formalized).

<details>
<summary>Exact scope, evidence and separate downstream work</summary>

**Exact statement and assumptions.** Finite-cap admitted testers span contextual responses after projection to the authorized channel. Separately, a private-randomness two-port chain used once in a fixed positive four-taxon wrapper has full forest kernels through M roots recovered from completed topology data using at most M+3 copies.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Linear observation spans and triangular inversion are established methods; the work supplies actual legal topology testers and padding adapters.

**Our contribution.** Legal finite-cap tester construction and a fixed-wrapper adapter recovering private full-forest kernels.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result is needed or claimed for this mathematical statement.
- **Empirical:** This is not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Separate downstream work (does not reopen this result):** Unknown exteriors, multiport shared registers and weaker channels require their own adapters.

**Proof, review and other accepted-source links:**

- [Admitted testers, Theorem 5](https://github.com/Sodelin/Research-Commons/blob/5e01a8e727478a2f22686d31f71304126e345116/research/2026-10-01-g4-admitted-testers-0819z/PROOF.md) (proof or status).
- [Private-chain tomography](https://github.com/Sodelin/Research-Commons/blob/5e01a8e727478a2f22686d31f71304126e345116/research/2026-10-01-g4-independent-bigon-1923z/TOMOGRAPHY-AND-COMPOSITION.md) (proof or status).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** original.G4.FINITE_OBSERVER. 

</details>

<a id="cb-g4-002"></a>
### Shared routing has a genuine stopping method
**CB-G4-002 · G4 · knowing when observations are enough**

**Question:** For one kind of ancestry routing, can we know when enough exact observations have been collected?

**What we learned:** Yes. The shared-routing branch has both a finite identification theorem and a terminating mathematical method.

**What it lets someone do:** Stop with a certificate under the stated exact-data and routing conditions.

**What we cannot conclude:** This is not a working experimental instrument or an algorithm for arbitrary approximate real numbers.

**Kind:** algorithm. **Mathematical status:** Proved by hand; named Lean subcomponents checked.

<details>
<summary>Exact scope, evidence and separate downstream work</summary>

**Exact statement and assumptions.** Whole-network COMMON targets and rivals are finite, strictly positive original sources with at least four taxa, full completed topology, a fixed finite routing-only menu and the same row configuration PMF across allocations. Finite forcing holds for real targets; observation-only stopping is effective with exact algebraic response/compiler encodings. Legal caterpillars expose finite directed-support grids; full-column independence, not a temporary rank plateau, supplies termination.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Finite positive-support moment/linear-algebra methods are antecedents. The new scope-specific work exposes the same finite COMMON law through actual legal observations and proves the stop.

**Our contribution.** Whole-network finite forcing and a terminating exact-algebraic COMMON stopping method, with mandatory scope corrections.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** Accepted selected1611 checks G4WholeProfileDetermination.actual_finite_randomized_common_menu_responses: target-first finite legal mixed-COMMON observations determine the whole row law against arbitrary finite rivals, n≥4, with one joint configuration PMF fixed across allocations. The separate accepted exact-algebraic stopping algorithm is not kernel-checked by that receipt; executable acquisition/detectable stopping remains outside it.
- **Execution:** No execution result is needed or claimed for this mathematical statement.
- **Empirical:** This is not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Separate downstream work (does not reopen this result):** Implementation, finite-error access and transfer to the independent-routing-only menu are separate.

**Proof, review and other accepted-source links:**

- [Whole COMMON acceptance](https://github.com/Sodelin/Research-Commons/blob/d10564c0b7382a2214dd0ccc1139f4c8a3d3327b/research/2026-10-08-codex-g3-g4-full-shot-1253z/integration/ROOT-WHOLE-COMMON-STOPPING-REVIEW.md) (hand review).
- [Mandatory scope correction](https://github.com/Sodelin/Research-Commons/blob/d10564c0b7382a2214dd0ccc1139f4c8a3d3327b/research/2026-10-08-codex-g3-g4-full-shot-1253z/g4-effective-stopping/attempt-3/COMMON-ONLY-RECOGNITION-SCOPE-CLARIFICATION.md) (proof or status).
- [Finite-edge correction](https://github.com/Sodelin/Research-Commons/blob/d10564c0b7382a2214dd0ccc1139f4c8a3d3327b/research/2026-10-08-codex-g3-g4-full-shot-1253z/g4-effective-stopping/attempt-3/FINITE-EDGE-COUNT-CORRECTION.md) (proof or status).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** original.G4.COMMON_EFFECTIVE. **Aliases:** G4 COMMON effective stopping.


**Additional exact formal receipts:**
- [Selected1611 independent final review: COMMON semantic endpoint](https://github.com/Sodelin/Research-Commons/blob/24bc23f20ea7ed82290bca535a074ca41adcd5a6/research/2026-10-12-dot-accepted-connected-union1611-1253z/independent/INDEPENDENT-FINAL-REVIEW.md).

</details>

<a id="cb-g4-003"></a>
### Two routing modes together need only finitely many exact tests
**CB-G4-003 · G4 · knowing when observations are enough**

**Question:** If we can observe both routing modes, can finitely many tests settle the whole model response?

**What we learned:** Yes, for every fixed admitted target, against all finite rivals, even without a preset rival-size limit.

**What it lets someone do:** Know that a finite distinguishing certificate exists for that target.

**What we cannot conclude:** Existence alone does not give a uniform procedure for finding the certificate.

**Kind:** theorem. **Mathematical status:** Proved by hand; named Lean subcomponents checked.

<details>
<summary>Exact scope, evidence and separate downstream work</summary>

**Exact statement and assumptions.** General natural BOTH finite forcing: each fixed strict binary rooted-LSA outer-labelled planar cut-child target with at least four taxa has a finite legal completed-topology certificate forcing its entire natural COMMON and INDEPENDENT law against all finite unknown-size original rivals using one source and physical tuple.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Finite-dimensional algebraic determination is classical; it applies only after the proof derives size control for every actual matching rival.

**Our contribution.** Derive actual rival-size control and semantic finite forcing against all finite unknown-size original rivals.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** Public accepted1613 checks the hybrid-free-target BOTH certificate at the stated physical CutChild contract: 3n shared full-law requests, at most n+2 copies each, n≥4, against arbitrary finite rivals. This does not kernel-verify the later general reticulate-target BOTH hand theorem.
- **Execution:** No execution result is needed or claimed for this mathematical statement.
- **Empirical:** This is not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Separate downstream work (does not reopen this result):** Uniform effective certificate production is separated in CB-G4-007.

**Proof, review and other accepted-source links:**

- [General BOTH acceptance](https://github.com/Sodelin/Research-Commons/blob/78bffa4904a4f56c9efc1d2ab3a18db13f65a982/research/2026-10-13-codex-g4-renewed/critical-review/ROOT-GENERAL-NATURAL-BOTH-FINITE-FORCING-ACCEPTANCE.md) (hand review).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** original.G4.NATURAL_BOTH. 


**Additional exact formal receipts:**
- [Public1613 independent final review: hybrid-free target BOTH subbranch](https://github.com/Sodelin/Research-Commons/blob/7239e89dea5caad68a54227cee3b44a7d9b96389/research/2026-10-12-dot-accepted-connected-union1613-1737z/independent/INDEPENDENT-FINAL-REVIEW.md).

</details>

<a id="cb-g4-004"></a>
### The result extends to qualifying extra tests
**CB-G4-004 · G4 · knowing when observations are enough**

**Question:** Can we add controls and shared programmes without losing the finite-certificate result?

**What we learned:** Yes, when the enlarged test menu satisfies two explicit requirements.

**What it lets someone do:** Reuse the finite-forcing theorem for those genuinely admitted menus.

**What we cannot conclude:** An arbitrary collection of controls is not automatically covered.

**Kind:** theorem. **Mathematical status:** Proved (not Lean formalized).

<details>
<summary>Exact scope, evidence and separate downstream work</summary>

**Exact statement and assumptions.** The menu contains the required finite natural BOTH certificate, and each bounded original shape compiles every legal outcome as a polynomial in one shared finite physical tuple. Then a finite certificate selected from that actual menu forces the whole menu law. The natural certificate bounds each actual matching rival, not merely a convenient equivalent representative; joint programme correlations remain joint.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Reuses natural BOTH forcing and bounded-shape polynomial response compilation; no arbitrary-menu prior theorem is assumed.

**Our contribution.** Extend finite forcing to authorized menus satisfying both interface hypotheses, preserving joint correlations.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result is needed or claimed for this mathematical statement.
- **Empirical:** This is not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Separate downstream work (does not reopen this result):** Menus missing either hypothesis and a uniform algorithm are not covered.

**Proof, review and other accepted-source links:**

- [Qualified-menu acceptance](https://github.com/Sodelin/Research-Commons/blob/130799a9985e05227e5d3db87733e386277ba962/research/2026-10-13-codex-g4-renewed/critical-review/ROOT-BOTH-INCLUSIVE-MENU-ACCEPTANCE.md) (hand review).
- [Menu-extension proof](https://github.com/Sodelin/Research-Commons/blob/130799a9985e05227e5d3db87733e386277ba962/research/2026-10-13-codex-g4-renewed/whole-source/continuation-2110z/NATURAL-BOTH-SIZE-CERTIFICATE-AND-MENU-EXTENSION.md) (proof or status).

**Connections:**
- [CB-G4-003](#cb-g4-003): **reused theorem**. Uses the natural BOTH actual-rival size certificate.

**Stable key:** original.G4.QUALIFIED_MENU. 

</details>

<a id="cb-g4-005"></a>
### All independent-routing answers determine all shared-routing answers
**CB-G4-005 · G4 · knowing when observations are enough**

**Question:** Would complete knowledge of independent routing also determine shared routing?

**What we learned:** Yes, in the original natural model class.

**What it lets someone do:** Transfer equality of the entire independent observation law to the shared law.

**What we cannot conclude:** This does not say that a finite independent sample of answers is enough.

**Kind:** theorem. **Mathematical status:** Proved (not Lean formalized).

<details>
<summary>Exact scope, evidence and separate downstream work</summary>

**Exact statement and assumptions.** Entire natural INDEPENDENT-law equality implies entire natural COMMON-law equality for strict original finite sources and shared physical tuples. The acceptance includes fair mixed arms, repeated cuts, ancestral alignment and the opaque-upper interface, not only static routing. It adds no externally correlated shared register.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Earlier static-routing special cases are superseded by the later accepted full original-source transfer, including current-root routing and ancestral alignment.

**Our contribution.** Prove complete independent-law equality determines complete shared-law equality in the original natural class.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result is needed or claimed for this mathematical statement.
- **Empirical:** This is not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Separate downstream work (does not reopen this result):** The finite-prefix version is CB-G4-008.

**Proof, review and other accepted-source links:**

- [General all-law acceptance](https://github.com/Sodelin/Research-Commons/blob/125360b75c9fad294e1ca737834e9bed4117e83e/research/2026-10-13-codex-g4-renewed/critical-review/ROOT-GENERAL-ALL-LAW-COMMONIZATION-ACCEPTANCE.md) (hand review).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** original.G4.ENTIRE_I_TO_C. 

</details>

<a id="cb-g4-006"></a>
### The algebraic search reduction is already complete
**CB-G4-006 · G4 · knowing when observations are enough**

**Question:** Is there a clean way to turn the remaining stopping question into a certificate-production question?

**What we learned:** Yes, with the exact algebraic interface. That reduction should be reused, not treated as another gap.

**What it lets someone do:** Focus effort on the genuinely missing certificate supplier.

**What we cannot conclude:** The reduction does not itself produce that supplier.

**Kind:** theorem. **Mathematical status:** Proved (not Lean formalized).

<details>
<summary>Exact scope, evidence and separate downstream work</summary>

**Exact statement and assumptions.** Under polynomial source responses, semialgebraic strict admission/data over the real algebraic field, effectively enumerable legal algebraic tests and exact response encodings, one algebraic tuple on the same graph preserves the entire algebraic profile. Observation-only stopping O is equivalent to uniform supplied-algebraic-source forcing D.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Real algebraic/semialgebraic methods are prior work. The contribution is all-profile descent and the exact effective-interface equivalence.

**Our contribution.** Prove all-profile algebraic candidate coverage and the exact O⇔D reduction.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result is needed or claimed for this mathematical statement.
- **Empirical:** This is not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Separate downstream work (does not reopen this result):** The uniform D algorithm beyond completed branches remains CB-G4-007.

**Proof, review and other accepted-source links:**

- [Accepted descent and stopping reduction](https://github.com/Sodelin/Research-Commons/blob/9c8ddb18d83f6d3a50bc94451e76bf658d0dd9f5/research/2026-10-09-dot-full-attempt-wave-0542z/g4-forcing/INDEPENDENT-CONSTRUCTION-LANE-REVIEW.md) (hand review).
- [Mandatory exterior-interface clarification](https://github.com/Sodelin/Research-Commons/blob/9c8ddb18d83f6d3a50bc94451e76bf658d0dd9f5/research/2026-10-09-dot-full-attempt-wave-0542z/g4-forcing/ALGEBRAIC-EXTERIOR-INTERFACE-CLARIFICATION.md) (proof or status).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** original.G4.ALGEBRAIC_DESCENT. 

</details>

<a id="cb-g4-007"></a>
### The broader automatic certificate finder is still missing
**CB-G4-007 · G4 · knowing when observations are enough**

**Question:** Beyond the completed shared-routing case, can one method always find the required finite certificate?

**What we learned:** The inspected results do not yet supply that method.

**What it lets someone do:** Keep a precise algorithmic target without denying the existing existence theorems.

**What we cannot conclude:** A proof that some finite certificate exists is not automatically a way to find it uniformly.

**Kind:** question. **Mathematical status:** Unresolved mathematical implication.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** Uniform D must be one terminating algorithm taking any supplied algebraic source and returning a finite certificate sound against all unknown-size real rivals under the declared effective interface. The accepted O⇔D reduction and all-profile algebraic coverage do not supply D outside completed branches.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Detailed antecedent attribution has not yet been independently indexed for this card. Consult the linked proof/source register; no new historical-priority claim is inferred.

**Our contribution.** Keep the missing uniform effective supplier distinct from already-proved algebraic coverage.

**Evidence, kept separate:**

- **Hand:** Exact obligation separated by the accepted reduction and later acceptance-first audit.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result is needed or claimed for this mathematical statement.
- **Empirical:** This is not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining mathematical implication:** Supply D, or a valid impossibility result at this exact effective interface.

**Proof, review and other accepted-source links:**

- [Reduction and exact effective obligation](https://github.com/Sodelin/Research-Commons/blob/9c8ddb18d83f6d3a50bc94451e76bf658d0dd9f5/research/2026-10-09-dot-full-attempt-wave-0542z/g4-forcing/ALL-PROFILE-DESCENT-AND-GLOBAL-CERTIFICATE-ATTEMPT.md) (proof or status).

**Connections:**
- [CB-G4-006](#cb-g4-006): **reused theorem**. Completed equivalence fixes the required supplier.

**Stable key:** original.G4.UNIFORM_EFFECTIVE_FORCING. 

</details>

<a id="cb-g4-008"></a>
### Finite independent-routing tests are the main unresolved branch
**CB-G4-008 · G4 · knowing when observations are enough**

**Question:** Can finitely many independent-routing tests do what all such tests can do?

**What we learned:** That exact step remains unresolved.

**What it lets someone do:** State a decisive goal rather than confusing approximation or changing examples with a solution.

**What we cannot conclude:** Neither full-law determination nor the two-mode theorem already answers it.

**Kind:** question. **Mathematical status:** Unresolved mathematical implication.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** For each fixed strict original target T, require a finite legal independent panel J_T such that every finite admitted rival N with I(N)|J_T=I(T)|J_T also matches the target's finite COMMON certificate C_T. The same N and tuple must satisfy every row; rival size is not bounded in advance. A negative result must keep one fixed T and give an exact later-inequivalent strict finite rival after every finite I panel.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Detailed antecedent attribution has not yet been independently indexed for this card. Consult the linked proof/source register; no new historical-priority claim is inferred.

**Our contribution.** State the exact finite independent-only implication and its fixed-target negative alternative.

**Evidence, kept separate:**

- **Hand:** The acceptance-first audit distinguishes this missing finite implication from completed entire-law transfer.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result is needed or claimed for this mathematical statement.
- **Empirical:** This is not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining mathematical implication:** Prove the finite J_T implication or construct the stated fixed-target exact negative alternative.

**Proof, review and other accepted-source links:**

- [Exact finite-bridge equivalence](https://github.com/Sodelin/Research-Commons/blob/9d21c0727564ae0ba101039d97b07c614d17f2e1/research/2026-10-13-codex-g4-renewed/whole-source/continuation-2110z/FINITE-INDEPENDENT-BRIDGE-EXACT-EQUIVALENCE.md) (proof or status).

**Connections:**
- [CB-G4-002](#cb-g4-002): **reused theorem**. Supplies the target COMMON certificate.
- [CB-G4-003](#cb-g4-003): **reused theorem**. Supplies completed BOTH finite forcing.
- [CB-G4-005](#cb-g4-005): **reused theorem**. Supplies entire-I-to-C transfer, not finite extraction.

**Stable key:** original.G4.FINITE_I_ONLY. **Aliases:** G4 finite I-only.

</details>

<a id="cb-g5-001"></a>
### Small timed panels recover particular ancestry features
**CB-G5-001 · G5 · recoverable ancestry features**

**Question:** Which features can small samples identify reliably in the exact model?

**What we learned:** The accepted three-tip result recovers specified collections of ancestry clusters and splits.

**What it lets someone do:** Target features that the observation law actually determines.

**What we cannot conclude:** It does not reconstruct every hidden graph detail or every parameter.

**Kind:** theorem. **Mathematical status:** Proved; named Lean scope checked.

<details>
<summary>Exact scope, evidence and separate downstream work</summary>

**Exact statement and assumptions.** Full binary M3 theorem for temporal binary LSA networks with positive child bridges, positive rates/durations, interior inheritance and contemporaneous tips, at least three taxa: timed three-tip panels determine normalized rooted-cluster and nontrivial-split unions. This is a union target, not tree co-occurrence. Earlier fair M2 normalized-quartet/sharpness results remain separate prior components.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Earlier fair M2 normalized-quartet/sharpness work is retained; the M3 result is a distinct broader target theorem under its timed binary class.

**Our contribution.** Full binary M3 identification of the stated cluster/split unions with the accepted selected formal package.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** The linked package records accepted endpoint and 319-module certificate; not a whole-repository build.
- **Execution:** Build evidence is preserved in the linked release; no new execution here.
- **Empirical:** This is not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Separate downstream work (does not reopen this result):** Whole-graph/parameter recovery and outside-class targets require separate claims.

**Proof, review and other accepted-source links:**

- [Full binary M3 package](https://github.com/Sodelin/Research-Commons/blob/81ff60aa0ffe6c39e15546b09105f3c3fafbd1ed/research/2026-10-10-dot-g5-full-binary-m3-0209z/README.md) (formal receipt).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** original.G5.BINARY_M3. **Aliases:** G5 full binary M3.

</details>

<a id="cb-g5-002"></a>
### Bounded hidden branching has a larger-panel hand theorem
**CB-G5-002 · G5 · recoverable ancestry features**

**Question:** What if the allowed hidden branching is larger?

**What we learned:** A hand-proved panel bound extends the feature-recovery result under a stated branching limit.

**What it lets someone do:** Use the appropriate larger sample panel in that mathematical class.

**What we cannot conclude:** Full formal assembly and proof of the best possible panel size are different unfinished tasks.

**Kind:** theorem. **Mathematical status:** Proved (not Lean formalized).

<details>
<summary>Exact scope, evidence and separate downstream work</summary>

**Exact statement and assumptions.** For the declared hidden-routing class with hybrid indegree at most k, the hand theorem uses M_(k+1) timed panels to recover the normalized cluster/split union target at all sizes. It does not assert optimality of this cap.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Builds on the programme's timed cluster/split recovery framework; formal assembly and optimality are not silently assumed.

**Our contribution.** Extend the hand feature-recovery theorem to bounded hybrid indegree using M_(k+1) panels.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result is needed or claimed for this mathematical statement.
- **Empirical:** This is not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Separate downstream work (does not reopen this result):** Complete full formal assembly and separately resolve optimality; the hand theorem is not mathematically open merely because formalization is incomplete.

**Proof, review and other accepted-source links:**

- [Bounded-indegree hand theorem](https://github.com/Sodelin/Research-Commons/blob/5e01a8e727478a2f22686d31f71304126e345116/research/2026-10-01-sol61-head-audit-1956z/G5-HIDDEN-AMBIGUITY-BOUNDED-INDEGREE.md) (proof or status).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** original.G5.BOUNDED_INDEGREE. **Aliases:** HG; bounded hidden-routing G5.

</details>

<a id="cb-g6-001"></a>
### Certify only what every compatible model agrees on
**CB-G6-001 · G6 · honest conclusions from uncertain data**

**Question:** How can we avoid overstating what uncertain data tell us?

**What we learned:** A completed mathematical characterization says when a conclusion survives every compatible admitted model.

**What it lets someone do:** Return a justified certificate or honestly leave the answer unresolved.

**What we cannot conclude:** It does not guarantee that every dataset will yield a useful answer or solve exact source existence.

**Kind:** theorem. **Mathematical status:** Proved by hand; named Lean subcomponents checked.

<details>
<summary>Exact scope, evidence and separate downstream work</summary>

**Exact statement and assumptions.** Completed hand characterization for positive binary rooted-LSA cut-child networks, not requiring planarity, n≥4, finite profiles and natural shared-source modes/control budgets: effective closure clouds and robust target fibres determine finite-data certification. Completed-cell law/TV formal consumers cover selected parts, not the full source assembly. The accepted algorithm specification includes both Hausdorff approximation directions and exact emptiness; an unexecuted full catalogue engine is not a missing mathematical supplier.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Classical confidence sets, inverse images and robust certification are antecedents; the contribution binds them to the declared original source and target.

**Our contribution.** Original-source nonplanar closure/cloud/robust-fibre characterization and algorithm specification; selected formal consumers are separate.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** Selected completed-cell/TV consumers have scoped 233/236-module audits. Full source/compiler/QE assembly is not claimed.
- **Execution:** No execution result is needed or claimed for this mathematical statement.
- **Empirical:** This is not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Separate downstream work (does not reopen this result):** Full formal/native assembly remains; this does not reopen the accepted hand characterization.

**Proof, review and other accepted-source links:**

- [Nonplanar finite-certification theorem](https://github.com/Sodelin/Research-Commons/blob/539c814ac470fde8147b0e1e6d5307972585b6f8/research/2026-10-01-sol61-head-audit-1956z/G6-NONPLANAR-FINITE-CERTIFICATION.md) (proof or status).
- [Selected completed-cell TV formal package](https://github.com/Sodelin/Research-Commons/blob/de3011fa352e04f9be64cf9f4da8a5528cad68db/research/2026-10-10-dot-g6-completed-cell-tv-0258z/README.md) (formal receipt).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** original.G6.FINITE_CERTIFICATION. **Aliases:** G6.

</details>

<a id="cb-g7-001"></a>
### Choose tests with a proof of what their answers can establish
**CB-G7-001 · G7 · choosing informative tests**

**Question:** Can a testing plan be chosen systematically rather than by guesswork?

**What we learned:** Yes, in the declared finite exact-law design setting, the hand theorem produces a certified policy or a resource lower certificate.

**What it lets someone do:** Compare testing plans and their costs under one consistent model family.

**What we cannot conclude:** It does not automatically give a cheap computation, an experimental sample budget, or a verified native programme.

**Kind:** algorithm. **Mathematical status:** Proved by hand; named Lean subcomponents checked.

<details>
<summary>Exact scope, evidence and separate downstream work</summary>

**Exact statement and assumptions.** Complete finite original-ID registry, fixed finite unranked readouts, shared-source semialgebraic affine exact-law programmes and reset/deletion-closed trajectory costs admit an exact real-algebraic CAD policy/Pareto construction or lower certificate. Full source compiler, response/history/QE and AST-to-CorrectRun assembly remain distinct formal obligations. The hand master already supplies the actual-source census, joint polynomial compiler, rank/deletion argument and CAD winning-fibre selection. Missing full formal/native composition is not missing hand mathematics.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Classical exact real algebraic decision methods, adaptive decision games and experimental design are reused with the original source/resource contract.

**Our contribution.** Original-source exact-law design theorem and its actual census/compiler/CAD construction, plus selected accepted formal strategy components.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** Earlier pinned-native accepted1591 includes rank compression, original-family strategy, full-epoch coefficients, repaired whole-edge chain, executable coefficient/support, sparse word/completion and raw calendar support, with a scoped 191-module recovery audit. The later hosted Lean 4.35 variant is additional evidence, not the first acceptance. Endpoints retain every-source CorrectRun, affine equality, deletion legality and exact-history premises.
- **Execution:** No execution result is needed or claimed for this mathematical statement.
- **Empirical:** This is not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Separate downstream work (does not reopen this result):** Full formal/native assembly, not a new proof of the completed hand characterization.

**Proof, review and other accepted-source links:**

- [Exact G7 master review](https://github.com/Sodelin/Research-Commons/blob/539c814ac470fde8147b0e1e6d5307972585b6f8/research/2026-10-01-sol61-head-audit-1956z/G7-EXACT-MASTER-REVIEW.md) (proof or status).
- [Scoped hosted game/rank check](https://github.com/Sodelin/Research-Commons/blob/8a96bb015b6cb88df196d6897b5437344a09238b/research/2026-10-21-lean-rust-solver-builder/evidence/G7-GAME-RANK-HOSTED-REVIEW.json) (formal receipt).
- [Accepted1591 incorporation catalogue and supersessions](https://github.com/Sodelin/Research-Commons/blob/dffb0b501c378c67e4aeea0561a68052e064e8ba/research/2026-10-11-dot-discovery-lean-incorporation-catalog-2200z/G5-G6-G7-INCORPORATION-CATALOG.md) (formal inventory).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** original.G7.EXACT_DESIGN. **Aliases:** G7; MG2 (view, not new master).

</details>

<a id="cb-causal-001"></a>
### Some causal questions can be answered with limited experiments
**CB-CAUSAL-001 · Causal discovery · restricted interventions**

**Question:** If we can intervene on only selected variables, what can we learn about cause and effect?

**What we learned:** The scoped theorem gives a finite plan for recovering the chosen causal summary.

**What it lets someone do:** Count the exact population-level questions required under the stated model.

**What we cannot conclude:** This is not a guarantee about noisy samples, fast computation or every hidden-variable model.

**Kind:** theorem. **Mathematical status:** Proved (not Lean formalized).

<details>
<summary>Exact scope, evidence and separate downstream work</summary>

**Exact statement and assumptions.** For finite acyclic DAGs with binary-valued variables, arbitrary finite original latent/selection carriers, selection sinks, one common positive rational binary registry, separate soft single-target interventions and the specified faithful physical-source class, the exact marked TCM class is recoverable using B=k(n−1)+Σ_{unordered{x,y}}2^{|U\{x,y}|}+Σ_{t∈T,x≠t}2^{|U\{x}|} elementary population CI/invariance queries, with 2B≤5n(n−1)2^u. All targets share one physical source. Binary-valued does not mean binary-degree.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** HPL anterior/TCM framework; Sadeghi stable-graph realization; Meek binary faithfulness; classical latent projection and population-query methods. Zhou–Kocaoglu's later no-selection completion is prior progress, not erased by this task.

**Our contribution.** Construct a common faithful physical binary source for the required tests and a proved G7 adapter, yielding the stated restricted-intervention upper bound.

**Evidence, kept separate:**

- **Hand:** Coordinating AI review covers the 132-module upper body with explicit exclusions, not a build.
- **Formal:** Full Lean source proposal is preserved; no kernel acceptance.
- **Execution:** No execution result is needed or claimed.
- **Empirical:** Not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Separate downstream work (does not reopen this result):** Formal elaboration and statistical acquisition remain separate; finite postprocessing is not asserted polynomial time.

**Proof, review and other accepted-source links:**

- [Full upper hand review](https://github.com/Sodelin/Research-Commons/blob/174168effef1efc5be13d941814c51520de9a8cb/research/2026-10-22-dot-restricted-causal-interventions/CAUSAL-FULL-UPPER-CUMULATIVE-HAND-REVIEW-20261023.md) (hand review).
- [Programme and prior-work boundaries](https://github.com/Sodelin/Research-Commons/blob/f300a67ccef954d0935a6e2a7a87389317fbb599/research/2026-10-22-dot-restricted-causal-interventions/README.md) (proof or status).

**Connections:**
- [CB-G7-001](#cb-g7-001): **proved adapter**. Accepted hand source-to-response/history/resource-game adapter instantiates G7; Lean source remains unelaborated.

**Stable key:** causal.RESTRICTED_UPPER. 

</details>

<a id="cb-causal-002"></a>
### Some exact causal tasks really require many tests
**CB-CAUSAL-002 · Causal discovery · restricted interventions**

**Question:** Could a clever strategy avoid nearly all those questions?

**What we learned:** A constructed family forces many paid questions, even for the stated randomized strategies.

**What it lets someone do:** Know a genuine limit for this exact question-and-answer model.

**What we cannot conclude:** This is not a lower bound on laboratory samples or every type of intervention.

**Kind:** theorem. **Mathematical status:** Proved (not Lean formalized).

<details>
<summary>Exact scope, evidence and separate downstream work</summary>

**Exact statement and assumptions.** For k>0,u≥2 let M=binom(u,2)2^(u−2). The physical class has deterministic lower bound M; an explicit M+1-source promise has exact optimum M. Arbitrary measurable random seeds with error ≤ε on every admitted source, 0≤ε<1/2, require extended expected paid queries ≥M(1−2ε) on one fixed baseline. Nontermination is failure; infinite expectation is allowed.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Classical distinguishing-query/adversary lower bounds and accepted G7 resource-game suppliers; the contribution realizes the necessary laws in one admitted physical causal family.

**Our contribution.** Realize a common physical hard family and transfer deterministic and arbitrary-seed randomized lower bounds through the exact query/cost interface.

**Evidence, kept separate:**

- **Hand:** Coordinating AI review covers 13 additional lower bodies and named G7 suppliers.
- **Formal:** Deterministic/randomized source is not compiler or kernel acceptance.
- **Execution:** No execution result is needed or claimed.
- **Empirical:** Not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Separate downstream work (does not reopen this result):** Formal acceptance; no lower bound outside this query/physical-source class is inferred.

**Proof, review and other accepted-source links:**

- [Lower hand-review receipt](https://github.com/Sodelin/Research-Commons/blob/f300a67ccef954d0935a6e2a7a87389317fbb599/research/2026-10-22-dot-restricted-causal-interventions/CAUSAL-LOWER-CUMULATIVE-HAND-REVIEW-20261023.md) (hand review).
- [Accepted lower scope](https://github.com/Sodelin/Research-Commons/blob/f300a67ccef954d0935a6e2a7a87389317fbb599/research/2026-10-22-dot-restricted-causal-interventions/V54-LOWER-HAND-ACCEPTANCE-AND-API.md) (proof or status).

**Connections:**
- [CB-G7-001](#cb-g7-001): **proved adapter**. Physical hard sources and resource histories instantiate the G7 lower-certificate interface.

**Stable key:** causal.PHYSICAL_LOWER. 

</details>

<a id="cb-causal-003"></a>
### No target means this particular task needs no questions
**CB-CAUSAL-003 · Causal discovery · restricted interventions**

**Question:** Does the large lower bound apply when there are no intervention targets?

**What we learned:** No. The chosen target then has only one possible value.

**What it lets someone do:** Avoid extending the nontrivial lower theorem beyond its assumptions.

**What we cannot conclude:** This does not trivialize all observational causal discovery.

**Kind:** counterexample. **Mathematical status:** Proved (not Lean formalized).

<details>
<summary>Exact scope, evidence and separate downstream work</summary>

**Exact statement and assumptions.** For k=0 the literal TCM-union target is the empty graph, so its target class is a singleton and query complexity is zero. This refutes extension of CB-CAUSAL-002 to k=0, not its k>0 statement.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Detailed antecedent attribution has not yet been independently indexed for this card. Consult the linked proof/source register; no new historical-priority claim is inferred.

**Our contribution.** Correct the empty-target overextension with the exact zero-query case.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** Correction/source preserved without new kernel run.
- **Execution:** No execution result is needed or claimed.
- **Empirical:** Not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Separate downstream work (does not reopen this result):** Keep k>0 explicit.

**Proof, review and other accepted-source links:**

- [Corrected scope](https://github.com/Sodelin/Research-Commons/blob/f300a67ccef954d0935a6e2a7a87389317fbb599/research/2026-10-22-dot-restricted-causal-interventions/README.md) (proof or status).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** causal.EMPTY_TARGET_CORRECTION. 

</details>

<a id="cb-lineage-001"></a>
### A best-fit score does not reveal every developmental link
**CB-LINEAGE-001 · Developmental lineage · scores and hidden histories**

**Question:** If two developmental maps always get the same score, must they be the same map?

**What we learned:** No. The studied score sees some reachability information but can miss direct links.

**What it lets someone do:** Understand exactly what that score distinguishes.

**What we cannot conclude:** A score tie does not prove that two models generate the same biological measurements.

**Kind:** theorem. **Mathematical status:** Proved (not Lean formalized).

<details>
<summary>Exact scope, evidence and separate downstream work</summary>

**Exact statement and assumptions.** For ε=0 unweighted Carta sampling score, rooted unique-potency DAGs labelled by nonempty subsets of observed cell types and the specified multifurcating typed-tree menu, the full score signature determines exactly the potency-vertex family and reachability, not direct edges. A seven-cell example has a unique optimal progenitor family that changes after leaf deletion.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Sashittal and colleagues' Carta (Nature Methods, DOI 10.1038/s41592-025-02903-z) supplies the optimization problem and prior optimal-label results. Later Pilarski–Stadler–Seidel work (DOI 10.1371/journal.pcbi.1014370) already studies joint tree/rate inference for fixed four-type star/chain structures, so Carta's historical future-work sentence is not a current blanket open claim.

**Our contribution.** Characterize the deterministic score's exact quotient and give a leaf-restriction counterexample for optimal progenitor families.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result is needed or claimed.
- **Empirical:** Not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Separate downstream work (does not reopen this result):** Statistical identification needs a specified stochastic forward/observation model.

**Proof, review and other accepted-source links:**

- [Score-interface theorem and review](https://github.com/Sodelin/Research-Commons/blob/c2650a5d8afc0be75cc8141f9f30d0907e961425/research/2026-10-22-dot-developmental-lineage-score-interface/README.md) (proof or status).

**Connections:**
- [CB-G3-004](#cb-g3-004): **same principle**. Similar inverse-information issue, not original G3 theorem reuse.
- [CB-G4-008](#cb-g4-008): **same principle**. Similar observation-versus-hidden-structure distinction, not a G4 extension.

**Stable key:** lineage.SCORE_QUOTIENT. 

</details>

<a id="cb-lineage-002"></a>
### Different hidden graphs can give identical observed trees
**CB-LINEAGE-002 · Developmental lineage · stochastic observation limits**

**Question:** Can different hidden transition graphs produce the same observed family trees?

**What we learned:** Yes, in an explicitly constructed stochastic model.

**What it lets someone do:** Test identification claims against an exact law-level example rather than just a score tie.

**What we cannot conclude:** This does not settle every biological division model or refute papers with different starting-state assumptions.

**Kind:** counterexample. **Mathematical status:** Proved (not Lean formalized).

<details>
<summary>Exact scope, evidence and separate downstream work</summary>

**Exact statement and assumptions.** A multitype branching change-of-basis construction preserves the full sampled timed event-tree law, also after a common neutral inherited-barcode kernel. A fixed-root-3 parent-retaining-birth example has five versus six transition edges. State-preserving division Xi→2Xi, equality from every labelled hidden start, observation-minimality and contradiction of the cited strong-HE theorem are excluded.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Classical multitype branching change-of-basis and lumping ideas are antecedents. Paired initial distributions versus every labelled hidden start are distinguished; the construction is not certified as a contradiction of prior strong-HE claims.

**Our contribution.** Construct and prove an exact sampled-law equality for distinct transition graphs in an explicitly labelled stochastic model.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result is needed or claimed.
- **Empirical:** Not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Separate downstream work (does not reopen this result):** Unknown graph identification under original state-preserving cell-division assumptions remains separate.

**Proof, review and other accepted-source links:**

- [Exact-law construction](https://github.com/Sodelin/Research-Commons/blob/c2650a5d8afc0be75cc8141f9f30d0907e961425/research/2026-10-22-dot-developmental-lineage-score-interface/STOCHASTIC-GRAPH-OBSTRUCTION.md) (proof or status).
- [Fixed-root specialization](https://github.com/Sodelin/Research-Commons/blob/c2650a5d8afc0be75cc8141f9f30d0907e961425/research/2026-10-22-dot-developmental-lineage-score-interface/PARENT-RETAINING-BIRTH-SPECIALIZATION.md) (proof or status).
- [Quantifier audit](https://github.com/Sodelin/Research-Commons/blob/c2650a5d8afc0be75cc8141f9f30d0907e961425/research/2026-10-22-dot-developmental-lineage-score-interface/QUANTIFIER-AUDIT.md) (proof or status).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** lineage.STOCHASTIC_GRAPH_OBSTRUCTION. 

</details>

<a id="cb-lineage-003"></a>
### The actual tree-refinement problem is computationally hard
**CB-LINEAGE-003 · Developmental lineage · optimization complexity**

**Question:** Is there an easy general way to choose the best detailed branching tree?

**What we learned:** The specified scoring problem is NP-hard, even in a restricted star-map case.

**What it lets someone do:** Understand why a general exact optimizer may need expensive search; use the supplied subset method for small cases.

**What we cannot conclude:** This does not mean every instance is difficult or that a best fit identifies biological truth.

**Kind:** theorem. **Mathematical status:** Proved (not Lean formalized).

<details>
<summary>Exact scope, evidence and separate downstream work</summary>

**Exact statement and assumptions.** For the actual D_λ objective over all binary joining refinements of arbitrary composite child clades, caterpillar exchange and anchors yield OPT=C0+OPT_MSSC−N. Star-map labels are all S and resolution cost is zero, so hardness holds for every fixed λ with unbounded types/degree. A full exact subset-DP recurrence is supplied. The operational formal endpoint remains separate.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Feige–Lovász–Tetali minimum-sum set cover hardness is the classical reduction source. Earlier polytomy optimization and Carta's objective retain attribution.

**Our contribution.** Prove hardness for the actual D_λ refinement objective, including arbitrary composite children, and supply the exact subset recurrence.

**Evidence, kept separate:**

- **Hand:** Full caterpillar/anchor/threshold reduction and subset recurrence independently checked, not just examples.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result is needed or claimed.
- **Empirical:** Not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Separate downstream work (does not reopen this result):** Historical novelty and the operational formal endpoint are separate; see CB-LINEAGE-005.

**Proof, review and other accepted-source links:**

- [Full complexity proof](https://github.com/Sodelin/Research-Commons/blob/c2650a5d8afc0be75cc8141f9f30d0907e961425/research/2026-10-22-dot-developmental-lineage-score-interface/POLYTOMY-REFINEMENT-COMPLEXITY.md) (proof or status).
- [Independent hand review](https://github.com/Sodelin/Research-Commons/blob/c2650a5d8afc0be75cc8141f9f30d0907e961425/research/2026-10-22-dot-developmental-lineage-score-interface/POLYTOMY-REVIEW-20261022-0712Z.md) (hand review).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** lineage.POLYTOMY_COMPLEXITY. 

</details>

<a id="cb-lineage-004"></a>
### An explicit mathematical checking algorithm has been written
**CB-LINEAGE-004 · Developmental lineage · explicit mathematical checker**

**Question:** Is there a precise checker for these restricted optimization certificates?

**What we learned:** A complete proposed mathematical algorithm and proof source have been written.

**What it lets someone do:** Inspect the acceptance rules, rejection of malformed input, time bound and answer format.

**What we cannot conclude:** It has not been compiled or kernel-verified, and it is not a Rust binary running on hardware.

**Kind:** algorithm. **Mathematical status:** Proof source complete; formal validation pending.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** The 197-module proposal supplies a fixed abstract TM2 checker for the restricted marked-star encoded language: all-word grammar, bounded header, one shared decoded witness, cell/clade/uniqueness guards, root-inclusive original score, budget clipping, rejection preservation, cleanup and exact one-bit halt with polynomial time/all-tape bounds. Its proposed endpoint is VerifierMachineWitness.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Detailed antecedent attribution has not yet been independently indexed for this card. Consult the linked proof/source register; no new historical-priority claim is inferred.

**Our contribution.** Write the complete restricted all-word mathematical checker and proposed correctness/resource proof source, while keeping its unverified status explicit.

**Evidence, kept separate:**

- **Hand:** 35 selected semantic bodies at ac54cf plus a separate bound/clean-halt review at 27fb172 found no concrete defect; not a full 197-module review.
- **Formal:** A certificate is candidate evidence; a verifier checks it; a kernel proof would validate the verifier theorem. Native implementation/refinement is another obligation.
- **Execution:** No compiler or checker execution claimed.
- **Empirical:** Not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining validation of the written source:** Elaborate the exact closure, repair failures, inspect actual endpoint axioms and separately validate any native implementation.

**Proof, review and other accepted-source links:**

- [Complete verifier source handoff](https://github.com/Sodelin/Research-Commons/blob/c2650a5d8afc0be75cc8141f9f30d0907e961425/research/2026-10-22-dot-developmental-lineage-score-interface/POLYTOMY-COMPLETE-RESTRICTED-VERIFIER-SOURCE.md) (proof or status).
- [Source endpoint](https://github.com/Sodelin/Research-Commons/blob/c2650a5d8afc0be75cc8141f9f30d0907e961425/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyRestrictedAlgorithmsSourceEndpoint.lean) (proof source).

**Connections:**
- [CB-LINEAGE-003](#cb-lineage-003): **candidate connection**. Implements the restricted certificate language, pending formal acceptance.

**Stable key:** lineage.RESTRICTED_VERIFIER_SOURCE. 

</details>

<a id="cb-lineage-005"></a>
### The formal hardness connection is still missing
**CB-LINEAGE-005 · Developmental lineage · formal complexity endpoint**

**Question:** Would verifying that checker finish the formal complexity proof?

**What we learned:** No. The encoded hardness connection is a separate missing part.

**What it lets someone do:** Track both obligations without declaring completion from a checker alone.

**What we cannot conclude:** Archive metadata or an informally similar theorem is not a verified usable import.

**Kind:** question. **Mathematical status:** Formal integration pending; mathematics is a separate claim.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** EncodedSourceHardness needs a closed operational hardness supplier at the exact encoding/machine interface and an all-word SAT→X3C/normalizer/serializer→MSSC chain. Registered Cook–Levin closure metadata plus actual composer source identify a candidate binding, but the generated closed endpoint and its actual axiom report were not obtained/verified. Clean-store operational refinement and version alignment are separate.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Detailed antecedent attribution has not yet been independently indexed for this card. Consult the linked proof/source register; no new historical-priority claim is inferred.

**Our contribution.** Bind the prospective operational hardness supplier to exact source/encoding requirements and preserve the independently missing reduction.

**Evidence, kept separate:**

- **Hand:** Candidate checked with limitations; not a closed accepted hardness supplier.
- **Formal:** VerifierMachineWitness and EncodedSourceHardness remain independent final premises.
- **Execution:** No execution result is needed or claimed.
- **Empirical:** Not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining formal integration:** Validate the exact closed supplier and prove faithful operational reduction without assuming an extra axiom.

**Proof, review and other accepted-source links:**

- [Registered closure crosscheck](https://github.com/Sodelin/Research-Commons/blob/c2650a5d8afc0be75cc8141f9f30d0907e961425/research/2026-10-22-dot-developmental-lineage-score-interface/POLYTOMY-REGISTERED-COOK-CLOSURE-CROSSCHECK-20261023.md) (proof or status).

**Connections:**
- [CB-LINEAGE-003](#cb-lineage-003): **same principle**. Hand reduction is the mathematical target, not already an operational formal theorem.
- [CB-LINEAGE-004](#cb-lineage-004): **candidate connection**. Validated checking gives membership, not hardness.

**Stable key:** lineage.ENCODED_HARDNESS_GAP. 

</details>

<a id="cb-phy-001"></a>
### A root region can be replaced without changing the stated output
**CB-PHY-001 · Phylogenetics · simplifying a network**

**Question:** Can part of a phylogenetic network be simplified without changing its sequence-model response?

**What we learned:** Yes, for the stated two-boundary region and model families.

**What it lets someone do:** Use a smaller equivalent representation while keeping exterior parameters fixed.

**What we cannot conclude:** This does not show every root can move anywhere or every network becomes a binary tree.

**Kind:** theorem. **Mathematical status:** Proved (not Lean formalized).

<details>
<summary>Exact scope, evidence and separate downstream work</summary>

**Exact statement and assumptions.** A maximal binary root region with exactly two boundary edge occurrences is replaceable by a retained-port fork preserving both cut matrices and fixed exterior parameters, with positive inheritance. Degree-two ports remain. Distinct domains: open H with invariant root law; Fourier JC/K2P/K3P with uniform root and literal zeros; strict-positive-rate continuous-time K2P using its actual exponential. Zero-rate K2P and general continuous-time K3P are excluded.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Prior root-blob equivalence questions and standard Markov cut-factorization, group-based Fourier channels and continuous-time exponentials are antecedents. The proof repairs the boundary/model contract rather than claiming universal root movement.

**Our contribution.** Give a direct cut-factorization retained-port proof and separate faithful suppliers for the admitted open, Fourier and continuous-time model domains.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** Proof-source packets preserved without compiler acceptance.
- **Execution:** No execution result is needed or claimed.
- **Empirical:** Not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Separate downstream work (does not reopen this result):** Broader subblob/single-edge/root-placement statements require separate proof.

**Proof, review and other accepted-source links:**

- [Direct proof](https://github.com/Sodelin/Research-Commons/blob/ae8a2874f391f7d8f31d9fb4454c47aae6fe9916/research/2026-10-22-dot-phylogeny-root-blob/RETAINED-PORT-DIRECT-PROOF.md) (proof or status).
- [Restricted-model source handoff](https://github.com/Sodelin/Research-Commons/blob/d6394f0a090466afff39881fabbbfd7c1fe6c49a/research/2026-10-22-dot-phylogeny-root-blob/RETAINED-PORT-RESTRICTED-SOURCE-HANDOFF.md) (proof or status).

**Connections:**
- [CB-G1-001](#cb-g1-001): **same principle**. Both preserve specified observations under simplification; exact G1 theorem reuse is not established.

**Stable key:** phylogeny.RETAINED_PORT. 

</details>

<a id="cb-rxn-001"></a>
### Finite features identify one scalar reaction-model class
**CB-RXN-001 · Reaction networks · partial observation**

**Question:** Can finite information settle a scalar reaction model against larger rivals?

**What we learned:** Yes, in the stated fixed-start autonomous scalar class.

**What it lets someone do:** Use a finite exact identification result without presuming a rival-size limit.

**What we cannot conclude:** It is not a practical finite-data procedure or a theorem about every hidden reaction network.

**Kind:** theorem. **Mathematical status:** Proved (not Lean formalized).

<details>
<summary>Exact scope, evidence and separate downstream work</summary>

**Exact statement and assumptions.** For autonomous scalar stopped laws, all finite scalar rivals share the positive start, observable interval and stopping convention. 3r+1 invariants suffice, or 2r+1 for unit births. A class-specific observation adapter connects the stochastic law to classical positive finite-moment determination.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Positive finite-moment uniqueness is classical and reused, not newly claimed.

**Our contribution.** Prove the fixed-start stopped-law-to-positive-moment adapter and finite invariant count for the actual scalar source class.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result is needed or claimed.
- **Empirical:** Not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Separate downstream work (does not reopen this result):** Effective finite experimental access and unrestricted hidden reaction models remain outside scope.

**Proof, review and other accepted-source links:**

- [Fixed-start scalar adapter](https://github.com/Sodelin/Research-Commons/blob/4f954e531ba7014ab49ba357cd1e68fef6472922/research/2026-10-22-dot-reaction-partial-observation/FIXED-START-SCALAR-MOMENT-ADAPTER.md) (proof or status).

**Connections:**
- [CB-CM-001](#cb-cm-001): **reused theorem**. Positive moment theorem applies after the stochastic observation adapter.
- [CB-G4-008](#cb-g4-008): **same principle**. Similar inverse-fibre question, not the ancestry source class.

**Stable key:** reaction.SCALAR_MOMENTS. 

</details>

<a id="cb-rxn-002"></a>
### Two tempting identification shortcuts fail
**CB-RXN-002 · Reaction networks · partial observation**

**Question:** Do local derivatives or a short reaction list guarantee an adequate observation model?

**What we learned:** No. Explicit examples defeat those two shortcuts.

**What it lets someone do:** Avoid using them as universal identification proofs.

**What we cannot conclude:** They do not prove all partial-observation identification impossible.

**Kind:** counterexample. **Mathematical status:** Proved (not Lean formalized).

<details>
<summary>Exact scope, evidence and separate downstream work</summary>

**Exact statement and assumptions.** One hidden-stop example has equal all-order interior initial generator/bracket jets but different observed held laws. Separately, one reaction has unbounded two-time feature rank, so finite chemistry need not have finite linear observable rank. These are distinct named-route obstructions.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Classical generator-jet and finite-rank identification strategies are the named routes being tested. Their failure here does not refute unrelated identification methods.

**Our contribution.** Construct source-faithful counterexamples to two precisely named observation shortcuts.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result is needed or claimed.
- **Empirical:** Not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Separate downstream work (does not reopen this result):** Original inverse problem still needs a source-faithful observation/realization argument.

**Proof, review and other accepted-source links:**

- [All-order hidden-stop obstruction](https://github.com/Sodelin/Research-Commons/blob/2113d9d8ca82d40022a37070172a76267427920e/research/2026-10-22-dot-reaction-partial-observation/HIDDEN-STOP-ALL-ORDER-JET-OBSTRUCTION.md) (proof or status).
- [Observable-rank obstruction](https://github.com/Sodelin/Research-Commons/blob/4c0ec491a10eda3cf809dd685b67467c8369b5fd/research/2026-10-22-dot-reaction-partial-observation/NONLOCAL-REALIZATION-ATTACK.md) (proof or status).

**Connections:**
- [CB-G3-004](#cb-g3-004): **same principle**. Similar realization pitfalls, different source classes.

**Stable key:** reaction.OBSERVATION_SHORTCUTS. 

</details>

<a id="cb-rxn-003"></a>
### One hidden observation problem reduces to a survival response
**CB-RXN-003 · Reaction networks · partial observation**

**Question:** Can a hidden-reaction observation problem be reduced to one exact response?

**What we learned:** Yes, in the specified construction it is equivalent to a hidden first-exit survival response.

**What it lets someone do:** Focus the remaining question on which responses finite chemical models can realize.

**What we cannot conclude:** This is not yet that realization classification or a result for every reaction network.

**Kind:** theorem. **Mathematical status:** Proved (not Lean formalized).

<details>
<summary>Exact scope, evidence and separate downstream work</summary>

**Exact statement and assumptions.** For the specified embedded independent-block construction, fixed initial state and original full-state stopping, equality of continuous observed held-path laws is equivalent to equality of the actual hidden-diffusion first-exit survival response censored at the stated horizon.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** First-exit/survival laws and observation pushforwards are classical; the source-specific two-way equality adapter is the contribution.

**Our contribution.** Prove an if-and-only-if observation adapter to the actual hidden first-exit survival response under unchanged fixed-start stopping.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result is needed or claimed.
- **Empirical:** Not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Separate downstream work (does not reopen this result):** Classify finite hidden chemical realizations of the response; unrestricted original master remains open.

**Proof, review and other accepted-source links:**

- [Survival adapter review](https://github.com/Sodelin/Research-Commons/blob/dfda007ccd8d46d77bd3ea789459de316900c65b/research/2026-10-22-dot-reaction-partial-observation/HIDDEN-EXIT-SURVIVAL-COORDINATING-REVIEW.md) (hand review).

**Connections:**
- [CB-G3-004](#cb-g3-004): **same principle**. Same inverse-fibre viewpoint, not a reduction to original G3.
- [CB-G4-008](#cb-g4-008): **same principle**. Finite determination is still class-specific.

**Stable key:** reaction.HIDDEN_SURVIVAL. 

</details>

<a id="cb-phys-p1-001"></a>
### We have better upper and lower limits on the testing cost
**CB-PHYS-P1-001 · Physics P1 · testing quantum states**

**Question:** How many copies of two quantum systems are needed to tell whether their states differ?

**What we learned:** Reviewed results improve both a sufficient copy budget and necessary budgets, but the best limits still do not match.

**What it lets someone do:** Benchmark proposed testing methods against explicit mathematical bounds.

**What we cannot conclude:** These are not a ready laboratory protocol, efficient preparation or a solved optimal-cost question.

**Kind:** theorem. **Mathematical status:** Proved (not Lean formalized).

<details>
<summary>Exact scope, evidence and separate downstream work</summary>

**Exact statement and assumptions.** Two unknown N-qubit Gibbs states have the same fixed known β>0; Hamiltonians are at most k-local and every nonidentity Pauli coefficient has magnitude at most one, without a bound on degree or total per-site strength. The promise is equality versus full trace norm at least ε. Collective measurements and adaptive source allocation are allowed, with a worst-case total-copy budget from both sources. The collective upper is O((M log(2+βM/ε)+log(1/δ))/ε²), M=Σ_{j=1}^k3^j binom(N,j), without an efficient-computation claim. Already accepted lower bounds, for fixed parameters and every sufficiently large physical N, include: 24, k≥3 and 0<ε≤1/4, Ω(N^(2k/3)/(log N)^(2/3)); 26, k=3 and 0<ε≤1/256, Ω(N^(9/4)/(log N)^(9/8)); 27, k=4 and 0<ε≤1/256, Ω(N³/log N), and k=5 on the same accuracy domain, Ω(N^(7/2)/(log N)^(7/8)); 29, k≥5 and 0<ε≤1/1024, Ω(N^((2k+1)/3)/(log N)^((2k+1)/(3(k−1)))); 32, k≥5 and 0<ε≤1/4096, Ω(N^a/(log N)^(a/(k−1))), a=min{(2k+2)/3,(4k−1)/5}. Every auxiliary spin counts. Constants and thresholds may depend on fixed k, β and ε; no uniform optimal accuracy/temperature dependence is claimed. Earlier shell21 remains valid in its stated domain, including k=2. Take the strongest applicable bound on complete domain intersections, not by extending the narrow accuracy domains or multiplying rates. These are existing proved components; closing the full optimal-copy gap is separate downstream work.

**Origin.** published open problem. Motivated by the optimal local Gibbs-state certification question in Bluhm et al.; these particular bounds are project contributions, not a claim to solve the whole published question. [Primary source](https://arxiv.org/html/2603.29809v1#S1.SS3).

**Prior work.** The source already provides an efficient single-copy protocol (Theorem 17). Classical quantum testing/learning compositions and admitted diagonal hard families are credited.

**Our contribution.** Compose an improved collective upper bound and construct admitted lower-bound families with all physical auxiliary copies counted.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result claimed.
- **Empirical:** Not a measured physical or biological claim.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Separate downstream work (does not reopen this result):** Close the gap between upper/lower bounds at the original parameter, measurement and copy-cost contract.

**Proof, review and other accepted-source links:**

- [Collective upper](https://github.com/Sodelin/Research-Commons/blob/809dcb6dcef78da700fddd888e9177bcff098b0f/research/2026-10-16-g6-gibbs-certification/COLLECTIVE-CERTIFICATION-UPPER-13.md) (proof or status).
- [Upper review](https://github.com/Sodelin/Research-Commons/blob/bf1d9a0e98b99eaf0a7d229de640a345210b78d4/research/2026-10-16-g6-gibbs-certification/COLLECTIVE-UPPER-13-INDEPENDENT-REVIEW.md) (hand review).
- [Lower32](https://github.com/Sodelin/Research-Commons/blob/9b7bb4034a136542a4d2c06afce84c64d1a50ce3/research/2026-10-16-g6-gibbs-certification/latent-light-fraction-32/README.md) (proof or status).
- [Lower24 coordinating review](https://github.com/Sodelin/Research-Commons/blob/0e3e40d07edb9292a2c5a4c64c8f6fe0ae56e98d/research/2026-10-16-g6-gibbs-certification/reservoir-amplified-lock-24/P1-RESERVOIR-AMPLIFIED-LOCK-REVIEW-24.md) (hand review).
- [Lower26 coordinating review](https://github.com/Sodelin/Research-Commons/blob/a823c8445e1dd2ce4cb4008a547958fa50bac810/research/2026-10-16-g6-gibbs-certification/conditional-product-label-26/P1-CONDITIONAL-PRODUCT-LABEL-REVIEW-26.md) (hand review).
- [Lower27 coordinating review](https://github.com/Sodelin/Research-Commons/blob/0daba51d070c50bc10153a9272eab0e436484841/research/2026-10-16-g6-gibbs-certification/averaged-shared-counts-27/P1-AVERAGED-COUNTS-REVIEW-27.md) (hand review).

**Connections:**
- [CB-G6-001](#cb-g6-001): **same principle**. Similar certification viewpoint, not an established theorem transfer from biological G6.

**Stable key:** physics.P1.BOUNDS. 

</details>

<a id="cb-phys-p1-002"></a>
### A specific measurement has a useful error bound
**CB-PHYS-P1-002 · Physics P1 · testing quantum states**

**Question:** Can a concrete quantum measurement be related to how much information another copy adds?

**What we learned:** Yes. The actual pretty-good measurement has the stated error bound without taking an extra unknown copy.

**What it lets someone do:** Use that exact measurement-to-error link in a larger testing proof.

**What we cannot conclude:** The remaining information bound is not proved merely by naming this link.

**Kind:** lemma. **Mathematical status:** Proved (not Lean formalized).

<details>
<summary>Exact scope, evidence and separate downstream work</summary>

**Exact statement and assumptions.** For the actual n-copy PGM, squared Bures risk≤2δ_n and squared full-trace risk≤8δ_n, δ_n=χ(n+1)−χ(n). No extra unknown copy is used. This is not an identity between measured Umegaki risk and that increment.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Pretty-good measurements, quantum information increments and distance inequalities are classical antecedents; exact composition is scoped in the packet.

**Our contribution.** Prove the actual n-copy PGM risk/information-increment inequality without consuming an extra unknown copy.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result claimed.
- **Empirical:** Not a measured physical or biological claim.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Separate downstream work (does not reopen this result):** Uniform full-Gibbs δ_n=O(M/n), a suitable dyadic bound or an equally strong direct tester is still missing.

**Proof, review and other accepted-source links:**

- [Measurement theorem and review](https://github.com/Sodelin/Research-Commons/blob/43cebb410eed5fbf6764b000f0b2e40d77090e25/research/2026-10-20-p1-pgm-information-increment/README.md) (proof or status).

**Connections:**
- [CB-PHYS-P1-001](#cb-phys-p1-001): **candidate connection**. Could improve the upper benchmark if the missing information bound is supplied.

**Stable key:** physics.P1.PGM. 

</details>

<a id="cb-phys-p5-004"></a>
### The unrestricted uniform approximation claim has a completed hand counterexample
**CB-PHYS-P5-004 · Physics P5 · unrestricted original comparison**

**Question:** Can the original coarse-grained model approximate every admitted strongly noisy many-body system uniformly in volume and time for one fixed local observable?

**What we learned:** The completed author hand proof gives admitted finite static-H models whose actual Redfield predictions for the same three-qubit observable grow without bound, while the original square-window comparator stays bounded.

**What it lets someone do:** Close the unrestricted project question by a counterexample and retain the valid restricted commuting and path/ring theorems.

**What we cannot conclude:** This does not refute the published finite-dimensional results, certify microscopic bath physics, supply a computed large witness or establish historical novelty.

**Kind:** counterexample. **Mathematical status:** Proved by author (not Lean formalized).

<details>
<summary>Exact scope, evidence and separate downstream work</summary>

**Exact statement and assumptions.** For every integer ell>=40, fix baseline gamma=1, tau=2^(-ell), b_G=exp(-1/8)sqrt(pi/8)exp(-1/128), ORIGINAL Gamma=9/4, b0=2b_G/9, exact h=b_G/4, j=b0/2, k<=12, m<=30, nu<=30 and beta=tau/8. With the SAME fixed O=X1Y2X3, positive normalized initial densities, every bare-Pauli thermal channel present, and the SAME static H in full infinite filters and the original square-window GKSL generator with ordered Lamb shift, the volume/time supremum of ||(exp(s L_T*)-exp(s R*))O||op is infinite, T=sqrt(tau/Gamma). For sufficiently large N=2^(q+1)-1 the finite real-grid maximum of actual predictions is at least exp[y^2 sqrt(N)/55296], y=(b_G/32)tau>0, at times at most N^(-1/2). Bounded-degree trees are allowed; this does not contradict narrower path/ring positive comparisons. Every future search must begin at q>=4ell+80.

**Origin.** The project's stronger uniform many-body contract, motivated by Ikeuchi–Mori; not a refutation of their dimension-dependent finite-system theorem. [Primary source](https://arxiv.org/html/2604.21366v2).

**Prior work.** Reuses standard thermal Gaussian/KMS, engineered spin-chain, tensor-functional, Dyson/Duhamel and polynomial interpolation methods. The earlier commuting and path/ring theorems retain their scoped hand acceptance; historical novelty is unassessed.

**Our contribution.** The existing P5 source owner completed and adopted the full admitted counterexample hand proof on 21 October at 23:52 UTC. This update publishes its exact preserved bytes and correction and reconciles the reader pointers.

**Evidence, kept separate:**

- **Hand:** Complete author derivation and end-to-end author audit. Three existing assistant hand returns cover bounded D3/D5, T4/T7 and C4 gauge/isometry/S5 parts under their stated premises. Whole-proof independent acceptance has not been performed.
- **Formal:** No full counterexample Lean certificate; separate earlier hosted algebra/integral checks retain their scope. Formalization is not an added requirement for the completed original assignment.
- **Execution:** No large-system witness search or original dynamics evaluation is claimed. Prior finite controls have their stated limited scope; publication verifies source identity and GitHub readback only.
- **Empirical:** Mathematical counterexample, not an experimental validation or microscopic system-bath theorem.

**Novelty:** Unresolved; source preservation and hand-proof completion do not establish historical priority.

**Separate downstream work (does not reopen this result):** No unfinished obligation remains in the original owner hand-proof goal. Whole-proof independent/formal validation and a feasible numerical witness are unperformed, unclaimed and not new original acceptance requirements. Other scientific and builder goals are separate.

**Proof, review and other source links:**

- [Complete owner hand proof (111288 bytes; SHA256 964fe1e3070913ea64b0ffca5de65c271ada7f966c808dd2f29ca0e35152c264)](https://github.com/Sodelin/Research-Commons/blob/c98b221d605f7dda739f249e1a9e049136fed51c/research/2026-10-23-p5-original-comparison-hand-proof/P5-ORIGINAL-COMPARISON-HAND-PROOF-v1.md) (author_hand_proof).
- [Exact original theorem and owner verdict](https://github.com/Sodelin/Research-Commons/blob/c98b221d605f7dda739f249e1a9e049136fed51c/research/2026-10-23-p5-original-comparison-hand-proof/P5-HAND-PROOF-VERDICT-v1.md) (owner_verdict).
- [Mandatory finite-witness admission correction](https://github.com/Sodelin/Research-Commons/blob/c98b221d605f7dda739f249e1a9e049136fed51c/research/2026-10-23-p5-original-comparison-hand-proof/P5-FINITE-WITNESS-ADMISSION-CORRECTION-v1.md) (source_correction).
- [Twenty-body public source manifest](https://github.com/Sodelin/Research-Commons/blob/c98b221d605f7dda739f249e1a9e049136fed51c/research/2026-10-23-p5-original-comparison-hand-proof/SOURCE-INDEX.json) (source_manifest).
- [Earlier attributed builder completion record](https://github.com/Sodelin/Research-Commons/blob/90cef7822e64fdd0e3ee0016cbefbc16271f00c9/research/2026-10-21-lean-online-builder/PEER-SCIENTIFIC-OUTCOMES.json) (attributed_owner_completion).

**Connections:**

- No automatic theorem-dependency or whole-proof independent-acceptance edge is asserted.

**Stable key:** physics.P5.ORIGINAL_UNRESTRICTED_COUNTEREXAMPLE.

</details>

<a id="cb-phys-p5-001"></a>
### Several parts of a long-time approximation proof are established
**CB-PHYS-P5-001 · Physics P5 · noisy quantum dynamics**

**Question:** When can a simpler noisy-quantum model faithfully replace the original evolution?

**What we learned:** The commuting and noncommuting paths/rings comparisons have scoped hand acceptance. The unrestricted bounded-neighborhood comparison has a separate completed author hand-proof counterexample, now published with its exact original assumptions and admission correction.

**What it lets someone do:** Reuse valid building blocks without restarting those proofs.

**What we cannot conclude:** Auxiliary models or finite time windows are not the original all-time result.

**Kind:** lemma. **Mathematical status:** Proved (not Lean formalized).

<details>
<summary>Exact scope, evidence and separate downstream work</summary>

**Exact statement and assumptions.** Reviewed components include commuting-Pauli comparison, noncommuting finite-window support decomposition, signed-energy identities, auxiliary interacting-noise influence estimates and general-operator incidence velocity 3kh. Their hypotheses remain separate from the actual same-H infinite-filter Redfield versus original square-window GKSL plus triangular Lamb-shift comparison. The completed actual commuting-Pauli comparison is recorded separately as CB-PHYS-P5-003 and is not merely an auxiliary-reference estimate. The operator-incidence packet also proves its full infinite-filter commutator estimates; its integrated auxiliary reference requires g>3kh, guaranteed for general k=2 in its original box, not all k.

**Origin.** published open problem. Motivated by the time- and system-size-uniform many-body coarse-graining direction in Ikeuchi–Mori; the selected project contract is explicit. [Primary source](https://arxiv.org/html/2604.21366v2).

**Prior work.** Published finite-dimensional time-uniform results have dimension-dependent constants. Their existence is not erased by this programme.

**Our contribution.** Derive and review the listed comparison, energy and influence components without replacing the original target equation.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result claimed.
- **Empirical:** Not a measured physical or biological claim.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Separate downstream work (does not reopen this result):** These component proofs remain completed. CB-PHYS-P5-004 records the full unrestricted counterexample adopted by the original source owner; its full proof and admission correction are now public. The earlier signed homogeneous 2q I2 estimate remains an unsupplied positive-route supplier, not an open original P5 goal. Whole-proof independent/formal checking is unperformed and does not reopen the completed hand-proof assignment. The commuting and path/ring positive theorems keep their narrower scopes.

**Proof, review and other accepted-source links:**

- [Initial component review](https://github.com/Sodelin/Research-Commons/blob/d855ab1267d2e29719ff7e865aac7df85ef7c6a0/research/2026-10-16-p5-strong-noise-coarse-graining/P5-STRONG-NOISE-INDEPENDENT-REVIEW-01.md) (hand review).
- [Signed-energy identities](https://github.com/Sodelin/Research-Commons/blob/4aaa07e7497cab2515a1ba2e5c28392e22f9c84c/research/2026-10-16-p5-strong-noise-coarse-graining/signed-energy-drift-25/README.md) (proof or status).
- [Operator-incidence supplier](https://github.com/Sodelin/Research-Commons/blob/04c9808f1fc4ec3c1c57cdbca200e91e82d32d5d/research/2026-10-20-p5-operator-incidence/README.md) (proof or status).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** physics.P5.COMPARISON_COMPONENTS. 


**Later attributed completion report (not independent proof acceptance):**
- [Attributed report of a complete unrestricted-comparison counterexample; proof and scope not verified here](https://github.com/Sodelin/Research-Commons/blob/90cef7822e64fdd0e3ee0016cbefbc16271f00c9/research/2026-10-21-lean-online-builder/PEER-SCIENTIFIC-OUTCOMES.json).


- [Independent scoped hand acceptance of actual noncommuting paths/rings comparison](https://github.com/Sodelin/Research-Commons/blob/main/research/2026-10-23-dot-p5-chains-rings-hand-review/INDEPENDENT-HAND-REVIEW.md).

</details>

<a id="cb-phys-p5-003"></a>
### One restricted noisy-quantum case is fully proved by hand
**CB-PHYS-P5-003 · Physics P5 · an actual all-time approximation theorem**

**Question:** Do we already have a result that stays valid however long the system evolves or how large it is?

**What we learned:** Yes. In one specified strongly noisy spin-model class, the error in local predictions has a uniform bound.

**What it lets someone do:** Use a proved comparison of the two actual evolution models in that class, not just a helpful auxiliary estimate.

**What we cannot conclude:** It does not settle general interacting quantum systems, prove the microscopic bath approximation, or establish experimental performance.

**Kind:** theorem. **Mathematical status:** Proved (not Lean formalized).

<details>
<summary>Exact scope, evidence and separate downstream work</summary>

**Exact statement and assumptions.** Let H=Σ_Z J_ZP_Z be a commuting Pauli Hamiltonian on any finite qubit volume, with sup_i Σ_{Z∋i}|J_Z|≤h. Set S_i={i}∪⋃_{Z∋i}Z, require |S_i|≤m and each site belongs to at most ν such sets, with h,m,ν volume independent. Each site has independent X,Y,Z channels with positive-type thermal correlations, Φ(−s)=conj Φ(s), |Φ(s)|≤(γ/τ_B)e^{−|s|/τ_B}, and Re∫_0^∞Φ(s)ds≥b_0γ>0. For T>0 and g=8b_0γ−2h−24ν2^mγhτ_B>0, the actual infinite-filter Redfield R and original square-window GKSL L_T with triangular Lamb shift satisfy ||exp(tL_T*)O−exp(tR*)O||≤2^s||O||δ/g for every finite volume, t≥0 and s-site observable, where δ=3ν(32γhT+4γτ_B/T+8γhτ_B). Thus the corresponding expectation error is bounded for every initial density matrix, including entangled states. Redfield positivity is not assumed.

**Origin.** project posed. A restricted actual-dynamics theorem addressing part of the published many-body coarse-graining direction, not a solution to its unrestricted form. [Primary source](https://arxiv.org/html/2604.21366v2).

**Prior work.** Ikeuchi–Mori provide the finite-system time-uniform comparison and exact averaging scheme. Lucia–Cubitt–Michalakis–Pérez-García establish local-observable stability under appropriate relaxation assumptions; Duhamel/relaxation stability is prior work. The source also credits conditional thermodynamic-limit ULE and strong-dissipation results. Novelty of the restricted estimate is not certified.

**Our contribution.** Derive the required integrated damping from the actual commuting strong-noise model, bind both original generator definitions and prove the uniform local-observable comparison with an explicit nonempty thermal-bath family.

**Evidence, kept separate:**

- **Hand:** The later independent review accepts the actual generator comparison, signs/Lamb shift, column damping, factor counts, thermal-bath feasibility and uniform constants. It supersedes the frozen proof's 'candidate' label. The stated proof and later review were reread for this status correction.
- **Formal:** This is a completed scoped hand theorem, not Lean verification. Lack of formalization does not reopen its mathematical proof.
- **Execution:** The theorem is not based on a new numerical run or a claimed software certificate.
- **Empirical:** The explicit bath family establishes mathematical nonvacuity, not calibration of a material or laboratory performance.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Separate downstream work (does not reopen this result):** This commuting theorem is complete at its stated hand-reviewed scope. CB-PHYS-P5-004 separately records the completed unrestricted counterexample hand proof, now published in full. That negative result uses a broader geometry than the separate accepted path/ring positive theorem. No global trace-distance, multi-time transcript, infinite-volume construction, weak-noise-at-fixed-h or microscopic system-plus-bath theorem follows from the commuting result.

**Proof, review and other accepted-source links:**

- [Actual commuting-Pauli proof, historical candidate title](https://github.com/Sodelin/Research-Commons/blob/d855ab1267d2e29719ff7e865aac7df85ef7c6a0/research/2026-10-16-p5-strong-noise-coarse-graining/P5-STRONG-NOISE-COMMUTING-PAULI-CANDIDATE.md) (proof or status).
- [Later independent scoped PASS review](https://github.com/Sodelin/Research-Commons/blob/d855ab1267d2e29719ff7e865aac7df85ef7c6a0/research/2026-10-16-p5-strong-noise-coarse-graining/P5-STRONG-NOISE-INDEPENDENT-REVIEW-01.md) (hand review).

**Connections:**
- [CB-PHYS-P5-001](#cb-phys-p5-001): **same principle**. This separately recorded actual-dynamics branch is stronger than merely listing auxiliary components; it does not close the general noncommuting continuation.

**Stable key:** physics.P5.COMMUTING_ACTUAL_UNIFORM. 

</details>

<a id="cb-phys-p5-002"></a>
### One proposed evolution can fail to preserve a physical state
**CB-PHYS-P5-002 · Physics P5 · noisy quantum dynamics**

**Question:** Can the Redfield approximation always be treated as a valid physical-state evolution?

**What we learned:** No. An explicit two-qubit example loses positivity.

**What it lets someone do:** Avoid using positivity as an unsupported step in the approximation proof.

**What we cannot conclude:** This example does not by itself disprove the full requested approximation-error bound.

**Kind:** counterexample. **Mathematical status:** Proved (not Lean formalized).

<details>
<summary>Exact scope, evidence and separate downstream work</summary>

**Exact statement and assumptions.** The reviewed initial packet includes an actual two-qubit Redfield nonpositivity example under its stated generator and initial state. Its target is the unconditional positivity shortcut, not every uniform Redfield/GKSL comparison.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Detailed antecedent attribution has not yet been independently indexed for this card. Consult the linked proof/source register; no new historical-priority claim is inferred.

**Our contribution.** Provide an explicit two-qubit counterexample to unconditional positivity of the stated Redfield evolution.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result claimed.
- **Empirical:** Not a measured physical or biological claim.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Separate downstream work (does not reopen this result):** Do not turn this or a growing-support example into a disproof of the original fixed-support error question.

**Proof, review and other accepted-source links:**

- [Two-qubit example and review](https://github.com/Sodelin/Research-Commons/blob/d855ab1267d2e29719ff7e865aac7df85ef7c6a0/research/2026-10-16-p5-strong-noise-coarse-graining/P5-STRONG-NOISE-INDEPENDENT-REVIEW-01.md) (hand review).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** physics.P5.NONPOSITIVITY. 

</details>

<a id="cb-nano-001"></a>
### Very similar energy curves can hide opposite model labels
**CB-NANO-001 · Nanowires · what an energy curve reveals**

**Question:** Can an energy curve alone reliably distinguish the two target labels?

**What we learned:** Not at fixed nonzero error in the declared model class: opposite labels can have arbitrarily close full curves.

**What it lets someone do:** Recognize a precise limitation of this measurement and model.

**What we cannot conclude:** This is not an equal-noiseless-spectrum pair, a fabricated device or proof about every experimental setup.

**Kind:** counterexample. **Mathematical status:** Proved (not Lean formalized).

<details>
<summary>Exact scope, evidence and separate downstream work</summary>

**Exact statement and assumptions.** In a fixed 60-site known-lead class with unrestricted finite potentials and zero internal loss, opposite reflection-visibility margins have arbitrarily close complete lowest-energy curves. An independently replayed rational example certifies opposite determinant intervals and whole-field energy difference≤0.09999 μeV; zero-temperature conductance separates that particular pair.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Detailed antecedent attribution has not yet been independently indexed for this card. Consult the linked proof/source register; no new historical-priority claim is inferred.

**Our contribution.** Prove fixed-lead bounded-error nonseparation and preserve an independently replayed finite rational pair.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** Stored rational pair and intervals independently replayed; not a new run for this board.
- **Empirical:** Extreme barriers are mathematical parameters, not fabrication evidence.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Separate downstream work (does not reopen this result):** Bounded-potential exact opposite-margin equal-curve existence is unresolved; a near-equal saved pair is not exactly equal.

**Proof, review and other accepted-source links:**

- [Fixed-lead theorem](https://github.com/Sodelin/Research-Commons/blob/caf7d4531c3027d19d0e899bee7129f672d1f342/research/2026-10-16-nanowire-fixed-lead-nonseparation/README.md) (proof or status).
- [Finite rational example](https://github.com/Sodelin/Research-Commons/blob/b6b1f91d84e58506b9028dec1ff0c59e05317224/research/2026-10-16-nanowire-fixed-lead-nonseparation/finite-example/README.md) (proof or status).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** nanowire.ENERGY_NONSEPARATION. 

</details>

<a id="cb-nano-002"></a>
### Conductance can certify a sign in a specified matrix model
**CB-NANO-002 · Nanowires · a model-level conductance certificate**

**Question:** Can another measurement give a definite answer that the energy curve cannot?

**What we learned:** In the stated reflection-matrix class, a sharp inequality certifies a sign when conductance is below a threshold.

**What it lets someone do:** Use an exact algebraic test after checking that the device model fits its assumptions.

**What we cannot conclude:** This is not automatically a certificate of a protected Majorana device or a microscopic realization.

**Kind:** theorem. **Mathematical status:** Proved (not Lean formalized).

<details>
<summary>Exact scope, evidence and separate downstream work</summary>

**Exact statement and assumptions.** For contractive particle-hole-symmetric reflection matrices with N channels, the sharp attainable region is 0≤g≤2N, |Q|≤1, Q≥1−g, and (−1)^NQ≥g−(2N−1). Thus g<1 implies Q>0. Algebraic attainment does not prove realization by every physical Hamiltonian class.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Classical matrix/scattering results are antecedents; no historical priority is established.

**Our contribution.** Derive the sharp attainable reflection-matrix region and its sign-certification consequence.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** Matrix Lean work is source-only, not a kernel certificate.
- **Execution:** No execution result claimed.
- **Empirical:** Not a measured physical or biological claim.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Separate downstream work (does not reopen this result):** A concrete unknown device needs a justified measurement/model/error adapter.

**Proof, review and other accepted-source links:**

- [All-channel theorem](https://github.com/Sodelin/Research-Commons/blob/f79a9a7626de25a58ee33d4a3dbff00f9f3f3db1/research/2026-10-16-nanowire-fixed-lead-nonseparation/all-channel/README.md) (proof or status).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** nanowire.REFLECTION_REGION. 

</details>

<a id="cb-nano-003"></a>
### One known-model thermal calculation keeps a positive margin
**CB-NANO-003 · Nanowires · thermal error budgets**

**Question:** Does the certificate survive a small specified temperature and measurement error?

**What we learned:** For the same known model and explicit budget, the archived calculation retains a positive margin.

**What it lets someone do:** Check that particular forward-model budget.

**What we cannot conclude:** It does not establish an unknown device's label or a usable operating temperature.

**Kind:** software check. **Mathematical status:** Scoped computational certificate.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** The known-device thermal certificate at 1 mK, conductance error 0.001 and zero Hamiltonian drift yields Q lower approximately 0.05925 under the saved forward-model enclosure.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Detailed antecedent attribution has not yet been independently indexed for this card. Consult the linked proof/source register; no new historical-priority claim is inferred.

**Our contribution.** Compute the stated known-device thermal/error margin with preserved enclosure evidence.

**Evidence, kept separate:**

- **Hand:** Use the exact publication evidence and model budget.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** Forward calculation and enclosure evidence are recorded, not rerun here.
- **Empirical:** No unknown-device observation or operating guarantee.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** Nonzero drift, unknown calibration and actual device admission require additional evidence.

**Proof, review and other accepted-source links:**

- [Thermal execution and scope](https://github.com/Sodelin/Research-Commons/blob/5055e470b32c17bdf93c55e09a891969be9ea23f/research/2026-10-16-nanowire-fixed-lead-nonseparation/thermal-model-budgets/refined-thermal-execution/PUBLICATION-README.md) (proof or status).

**Connections:**
- [CB-NANO-002](#cb-nano-002): **reused theorem**. Applies the matrix inequality through this particular model/error budget.

**Stable key:** nanowire.THERMAL_BUDGET. 

</details>

<a id="cb-nano-004"></a>
### Even a complete transmission spectrum cannot force a negative label
**CB-NANO-004 · Nanowires · limits of a richer measurement**

**Question:** If we know both conductance and the complete transmission spectrum, can we determine the reflection sign?

**What we learned:** In this specified matrix model, these richer observations sometimes force a positive sign but never force a negative sign. We found the exact possibilities, including measurement-error limits.

**What it lets someone do:** Check whether an allowed report is inconsistent, fixes a positive sign, or still permits both signs.

**What we cannot conclude:** This is not a claim about every physical wire or a measured device, and the sign is not a guarantee of a protected Majorana state.

**Kind:** theorem. **Mathematical status:** Proved (not Lean formalized).

<details>
<summary>Exact scope, evidence and separate downstream work</summary>

**Exact statement and assumptions.** For zero-energy, zero-temperature/bias, loss-free canonical-PHS two-terminal scattering with two electron modes per lead, observe local conductance g and the complete ordered quasiparticle transmission eigenvalues 0≤T1≤T2≤T3≤T4≤1 from the same parent's t†t. Write a≥b≥c≥d≥0 for sqrt(1−Ti), p=abcd and w±=ab±cd. If p>0 the exact feasible reflection determinant set is {+p: |g−2|≤w+} ∪ {−p: |g−2|≤w−}. If p=0 it is {0} exactly when |g−2|≤ab, otherwise empty. Every feasible value has an explicit common SO(8) scattering parent. For exact T and |y−g|≤η, replace |g−2| by max(0,|y−2|−η). Uncertain T requires a union over the authenticated joint error/source relation. No negative-only feasible set exists in this class.

**Origin.** project posed. A fixed-spectrum refinement of the existing abstract PHS measurement programme, not asserted to have been a named published open problem.

**Prior work.** The signed-SVD/exterior-square Hodge bound and orthogonal scattering dilation are classical linear algebra already established in the linked Commons four-dimensional and all-channel packets. Standard PHS/conductance conventions are credited there to Beenakker, Dahlhaus, Wimmer and Akhmerov (2011). The earlier observation audit already established that the full transmission spectrum fixes |det r|, not directly its sign.

**Our contribution.** Derive the two exact orientation intervals at a fixed transmission spectrum, attain every point with one common SO(8) parent, include the singular boundary, and compose the exact conductance-error rule. This is not a new Hodge or dilation theorem.

**Evidence, kept separate:**

- **Hand:** The complete fixed-spectrum proof received coordinating/adversarial AI hand PASS, including pairing bounds, full attainment, the singular case, bounded-error union and the same SO(8) parent. The review pins proof SHA256 04b8eaeae23a25b78f9b2e68924910a404ffe8ef0389205ee3d79ddf1a63be7b; it is not human/external peer review.
- **Formal:** No Lean proof or kernel receipt for this theorem is claimed.
- **Execution:** No scientific code, numerical experiment or compiler was run for this proof or review. Hashes/readbacks establish preserved file identity only.
- **Empirical:** No fixed-contact Rashba realization, experiment, finite-temperature admission or operating guarantee is supplied.

**Novelty:** Unresolved; the inherited mathematical methods are explicitly credited, and correctness/acceptance is not historical priority.

**Separate downstream work (does not reopen this result):** Any application to a fixed-contact Rashba wire or an unknown device needs its own source/measurement/error admission. Complete quasiparticle transmission eigenvalues must not be replaced by aggregate charge conductance, shot noise or a warm trace. No protected-operation or thermodynamic-topology conclusion follows.

**Proof, review and other accepted-source links:**

- [Current scoped status and contract](https://github.com/Sodelin/Research-Commons/blob/bcb7c4e3d58b0eaab3c24d89f5971fedf92e14cd/research/2026-10-23-dot-nanowire-transmission-sign-fibre/README.md) (proof or status).
- [Complete fixed-spectrum proof](https://github.com/Sodelin/Research-Commons/blob/bcb7c4e3d58b0eaab3c24d89f5971fedf92e14cd/research/2026-10-23-dot-nanowire-transmission-sign-fibre/TRANSMISSION-SPECTRUM-SIGN-FIBRE-20261023.md) (proof).
- [Exact coordinating hand review](https://github.com/Sodelin/Research-Commons/blob/bcb7c4e3d58b0eaab3c24d89f5971fedf92e14cd/research/2026-10-23-dot-nanowire-transmission-sign-fibre/TRANSMISSION-SPECTRUM-SIGN-FIBRE-REVIEW-20261023.md) (hand review).
- [Inherited four-dimensional Hodge supplier](https://github.com/Sodelin/Research-Commons/blob/c6e7264d3155ba10df38bda5d5b773b9426f705f/research/2026-10-16-nanowire-fixed-lead-nonseparation/classwise-readout/SHARP-CONDUCTANCE-DETERMINANT-BOUND-REVIEW-06.md) (prior supplier).

**Connections:**
- [CB-NANO-002](#cb-nano-002): **same principle**. Both use PHS reflection-matrix geometry and common-parent scattering constraints. The all-channel (g,Q) region alone does not determine the fixed-spectrum fibre; the actual four-dimensional Hodge supplier is linked separately.

**Stable key:** nanowire.FIXED_TRANSMISSION_SIGN_FIBRE.

</details>


<a id="cb-nano-005"></a>
### This entire model-changing route cannot reverse the reflection sign
**CB-NANO-005 · Nanowires · ruling out one exact construction route**

**Question:** Can this proposed way of changing a wire model keep all its energy levels but reverse its reflection sign?

**What we learned:** No. Within the precise family of transformations studied, the only possible potential profiles are the original profile and its end-to-end reversal. Both keep the reflection sign unchanged.

**What it lets someone do:** Stop searching this entire route, including asymmetric profiles and isolated transformations, rather than repeatedly testing candidates it cannot produce.

**What we cannot conclude:** This does not show that every wire can be identified from its lowest energy curve. Other ways of producing identical curves remain outside the theorem, and no experimental guarantee follows.

**Kind:** theorem. **Mathematical status:** Proved (not Lean formalized).

<details>
<summary>Exact scope, evidence and separate downstream work</summary>

**Exact statement and assumptions.** Let A be the 60-site path adjacency matrix, K its skew path matrix with upper entries +1 and lower entries −1, and S_a=diag(a)−tA, t=501643/20000. For any real profiles a,b and real orthogonal O with OKOᵀ=±K and OS_aOᵀ=S_b, necessarily b=a or b=reverse(a). Combining this with the accepted spin-sector reduction gives the same classification for every field-independent real orthogonal diag(O+,O−) in the σx spin basis, acting only on spatial coordinates and trivially on Nambu coordinates, for which O+S_aO+ᵀ=O−S_aO−ᵀ=S_b and O+KO−ᵀ=K. In the original 60-site Rashba Hamiltonian with onsite a_jτz+Bσx+Δτx, upper hopping −tτz−iλσyτz, λ=5/2, Δ=1/5, B∈[0,2], identical fixed normal endpoint self-energies −iI and zero internal loss, both resulting profiles have equal Q(a)=det r_L(a,2). Thus no pair in this ansatz has Q(a)≤−m and Q(b)≥m for m>0. Both profiles must remain in the same prescribed bounded class C; the theorem does not enlarge C, classify every transformation O, or assume generic/asymmetric profiles.

**Origin.** Project posed. The previously unresolved common-rotation construction route within the existing bounded-wire identification programme, not asserted to be a named published open problem.

**Prior work.** Classical path sine diagonalization, one-dimensional distance rigidity, finite Fourier orthogonality and Chebyshev/Lagrange interpolation are reused. The existing Commons spin-sector reduction14 proves O+=±O−; fixed-contact symmetry10 proves reflection-determinant preservation under reversal. Mirrored-pair reduction15 previously gave at most 2^30 candidate output profiles, not their admission.

**Our contribution.** Completely classify the remaining output profiles as original or full reversal, using all pairwise distances among the odd cosine coefficients and an exact identity removing the common translation. Compose the classification with the actual reduction14 and fixed-contact symmetry10 suppliers to close the entire declared ansatz, including repeated entries, symmetric profiles and isolated rotations. The earlier finite candidate list is superseded as an unresolved search, not invalidated.

**Evidence, kept separate:**

- **Hand:** The complete manuscript and actual reduction14/symmetry10 supplier bodies received separate coordinating AI hand PASS. The receipt checks the gauge, all odd-coefficient distances, translation removal, recovery, both K signs and the actual fixed-contact target. It pins proof SHA256 afff530aea1d4f1be351436ca8c8270a067f22675cdbd8ed50ca9dd0112c9198. This is not human/external peer review.
- **Formal:** No Lean proof or kernel-checked endpoint for this classification is claimed.
- **Execution:** No scientific code, numerical experiment or compiler was run for this proof or review. Publication hashes and readbacks establish file identity only.
- **Empirical:** This is an exact theorem within the specified finite Hamiltonian model. No fabrication admission, measured-device conclusion, thermal guarantee or protected-operation certificate is supplied.

**Novelty:** Unresolved; the classical methods and completed earlier suppliers are credited. Correctness and scoped acceptance do not establish historical novelty.

**Remaining obligation for this claim:** None for this exact proved claim. See separate_downstream_or_validation_work; it must not reopen the proof.

**Separate downstream work (does not reopen this result):** The original bounded-wire master still requires an admitted opposite-Q-margin pair with the same complete lowest-energy curve, or an exclusion of every such pair in the original class. Equality of a lowest branch need not come from any constant full-pencil transformation. General spatial/Nambu mixing and branch-only coincidences are not classified. The completed common-factor/least-root criterion remains the exact downstream target; neither another restricted-ansatz no-hit nor a numerical near-pair answers it.

**Proof, review and exact supplier links:**

- [Accepted scope and supersession](https://github.com/Sodelin/Research-Commons/blob/c22ac1651c6605e96b488695c02d0750104c204e/research/2026-10-16-nanowire-fixed-lead-nonseparation/spin-sector-classification/README.md) (proof or status).
- [Complete profile-classification proof](https://github.com/Sodelin/Research-Commons/blob/c22ac1651c6605e96b488695c02d0750104c204e/research/2026-10-16-nanowire-fixed-lead-nonseparation/spin-sector-classification/SPIN-SECTOR-PROFILE-CLASSIFICATION-CANDIDATE-18.md) (proof).
- [Separate coordinating hand review binding the proof bytes](https://github.com/Sodelin/Research-Commons/blob/c22ac1651c6605e96b488695c02d0750104c204e/research/2026-10-16-nanowire-fixed-lead-nonseparation/spin-sector-classification/SPIN-SECTOR-PROFILE-CLASSIFICATION-INDEPENDENT-REVIEW-18.md) (hand review).
- [Actual spin-sector reduction14 supplier](https://github.com/Sodelin/Research-Commons/blob/bcb7c4e3d58b0eaab3c24d89f5971fedf92e14cd/research/2026-10-16-nanowire-fixed-lead-nonseparation/spin-sector-reduction/SPIN-SECTOR-INTERTWINER-REDUCTION-CANDIDATE-14.md) (prior supplier).
- [Actual fixed-contact reversal/symmetry10 supplier](https://github.com/Sodelin/Research-Commons/blob/bcb7c4e3d58b0eaab3c24d89f5971fedf92e14cd/research/2026-10-16-nanowire-fixed-lead-nonseparation/symmetry-check/BOUNDED-COLLISION-SYMMETRY-CHECK-LOCAL-10.md) (prior supplier).
- [Separate full-master common-factor and lowest-root criterion](https://github.com/Sodelin/Research-Commons/blob/bcb7c4e3d58b0eaab3c24d89f5971fedf92e14cd/research/2026-10-16-nanowire-fixed-lead-nonseparation/lowest-branch-criterion/LOWEST-BRANCH-COMMON-FACTOR-CANDIDATE-11.md) (separate downstream scope).

**Connections:** Reduction14 and symmetry10 are actual reused suppliers, linked above. They have no separate IDs in the current board. This theorem is not derived from the abstract conductance or transmission-spectrum fibre cards.

**Stable key:** nanowire.REAL_SPIN_SECTOR_PROFILE_CLASSIFICATION.

</details>


<a id="cb-cm-001"></a>
### A classical moment theorem has a checked reusable component
**CB-CM-001 · Shared mathematics · finite positive moments**

**Question:** When can finitely many exact summaries identify a finite positive distribution?

**What we learned:** A scoped classical theorem is packaged as a checked component.

**What it lets someone do:** Reuse it once the actual observation really is the required distribution's moment sequence.

**What we cannot conclude:** It cannot manufacture a missing link from biological observations to moments.

**Kind:** theorem. **Mathematical status:** Proved; named Lean scope checked.

<details>
<summary>Exact scope, evidence and separate downstream work</summary>

**Exact statement and assumptions.** CM-T02 is the selected four-module positive finite-moment component. Applications must use one fixed pushforward law with the correct grouped equal values and positive masses; the source/observation adapter is not supplied automatically.

**Origin.** classical prior. Positive finite-moment determination is established mathematics; the contribution is a scoped checked reusable component.

**Prior work.** Classical finite positive moment/Hankel determination.

**Our contribution.** Package and verify the classical positive-moment component with explicit application prerequisites.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** Four-module certificate only, not all downstream applications.
- **Execution:** Exact receipt preserved.
- **Empirical:** Not a measured physical or biological claim.

**Novelty:** No new mathematical priority claimed for the classical theorem.

**Separate downstream work (does not reopen this result):** Each application must prove its own faithful observation adapter.

**Proof, review and other accepted-source links:**

- [CM-T02 certificate](https://github.com/Sodelin/Research-Commons/blob/514648b697aeed8f46582109cfeefcd7707cd738/research/2026-10-15-common-moment-checked-component/CM-T02-CERTIFICATE-001.json) (formal receipt).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** common.CM_T02. 

</details>

<a id="cb-seq-001"></a>
### Three exact first-occurrence formulas are formally proved
**CB-SEQ-001 · Sequences · Thue–Morse**

**Question:** Where do the longest same-colour arithmetic patterns first appear in this sequence?

**What we learned:** Three specified families have exact first-location formulas, with checked formal proofs.

**What it lets someone do:** Use exact answers for those families, including their small-index exceptions.

**What we cannot conclude:** This does not settle every pattern question about the sequence.

**Kind:** theorem. **Mathematical status:** Proved; named Lean scope checked.

<details>
<summary>Exact scope, evidence and separate downstream work</summary>

**Exact statement and assumptions.** For digit-parity Thue–Morse t, maximum monochromatic progression length A(d) and earliest maximum start i(d): d=2^n+1,n≥2 gives A=2^n+2,i=3·2^(2n)−2^n−1; d=2^(2n)−1,n≥1 gives A=2^(2n)+4,i=3·2^(4n)−2^(2n)+1; d=2^(2n+1)−1,n≥0 gives A=2^(2n+1),i=2^(2n+1)−1. Stronger all-start classifications are also proved. The first formula excludes n=1, since i(3)=45.

**Origin.** published open problem. Three families of Joshi–Rust Conjecture 3.8, with explicit small-index ranges. [Primary source](https://arxiv.org/html/2501.05830v2#S3.SS2.SSS2).

**Prior work.** Maximal lengths and block-recognition ideas due to Parshina and Aedo–Grimm–Nagai–Staynova are rederived/credited. The contribution adds all-start analysis and formal first-occurrence proof.

**Our contribution.** Prove the first-occurrence formulas and stronger all-start classifications in the actual digit-parity sequence, with a complete selected formal audit.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** Fresh seven-source replay and all 323 owned declarations audited; only propext, Classical.choice and Quot.sound permitted; no custom axioms.
- **Execution:** Pinned Lean 4.33.1/mathlib release and semantic correspondence review recorded.
- **Empirical:** Not a measured physical or biological claim.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Separate downstream work (does not reopen this result):** No whole automatic-sequence classification or historical-priority certification.

**Proof, review and other accepted-source links:**

- [Exact formulas, proof and receipt](https://github.com/Sodelin/Research-Commons/blob/2468dc1151c5e9a9dd870024a4fbeff8d4910e4e/research/2026-10-04-dot-thue-morse-first-occurrence-lean-0550z/package/README.md) (formal receipt).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** october.SEQ.001. 

</details>

<a id="cb-seq-002"></a>
### A proposed simple description is impossible
**CB-SEQ-002 · Sequences · period doubling**

**Question:** Can the number of palindrome pieces in these prefixes follow the proposed finite-state pattern?

**What we learned:** No. The specified non-regularity statement has a reviewed all-length computer-assisted proof.

**What it lets someone do:** Resolve this precise conjecture without extrapolating from a long finite table.

**What we cannot conclude:** This is not a complete formula or a solution to the separate Fibonacci question.

**Kind:** theorem. **Mathematical status:** Proved (not Lean formalized).

<details>
<summary>Exact scope, evidence and separate downstream work</summary>

**Exact statement and assumptions.** Let u be the fixed point beginning 0 of 0→01,1→00; P(n) is minimum nonempty-palindrome factor count of its length-n prefix, P(0)=0. Then d(n)=P(n+1)−P(n) is not 2-automatic and P is not 2-regular. The computational lemma is an all-length inclusion over a closed reachable finite-state system.

**Origin.** published open problem. Frid–Laborde–Peltomäki, preprint Conjecture 17 / published Conjecture 2. [Primary source](https://doi.org/10.1016/j.tcs.2021.08.016).

**Prior work.** The source conjecture, regularity/difference equivalence, palindrome structure and finite-state distinguishability antecedents are credited.

**Our contribution.** Supply the all-length argument and independently implemented closed-state inclusion certificate for the exact period-doubling conjecture.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** Independent AI hand review and exhaustive closed-state certificate, not Lean verification or external expert endorsement.
- **Execution:** Author closed system: 2460 states/3092 transitions. Separate representation: 1593 states/2050 transitions per starting colour. No word-length cutoff; exact inventories retained.
- **Empirical:** Not a measured physical or biological claim.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Separate downstream work (does not reopen this result):** Formal kernel treatment and historical priority are separate; no extrapolation claim.

**Proof, review and other accepted-source links:**

- [Theorem, independent review and exact state certificates](https://github.com/Sodelin/Research-Commons/blob/2468dc1151c5e9a9dd870024a4fbeff8d4910e4e/research/2026-10-04-dot-period-doubling-nonregularity-1150z/README.md) (proof or status).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** october.SEQ.002. 

</details>

<a id="cb-seq-003"></a>
### The allowed lengths are classified in a specific range
**CB-SEQ-003 · Sequences · repetition-avoiding substitutions**

**Question:** Which fixed-length binary substitutions preserve a stated repetition limit?

**What we learned:** Throughout the specified range, every positive length except 3 and 6 is possible.

**What it lets someone do:** Use an exact all-input length classification in that range.

**What we cannot conclude:** It does not classify every substitution or cover the lower threshold range.

**Kind:** theorem. **Mathematical status:** Proved (not Lean formalized).

<details>
<summary>Exact scope, evidence and separate downstream work</summary>

**Exact statement and assumptions.** For every avoidance threshold from (8/3)^+ up to but excluding 3, positive lengths of binary uniform morphisms preserving that threshold on every admissible input are exactly all lengths except 3,6; complementary morphisms realize every admitted length. Strict 8/3 differs: length 5 is impossible there.

**Origin.** published open problem. Source-posed direction in Shallit–Shur–Zorcic, Power-free complementary binary morphisms. [Primary source](https://arxiv.org/html/2310.15064v3).

**Prior work.** Their odd-length construction, exceptional-length impossibility and Kobayashi criterion are reused; the endpoint-marker construction is strengthened.

**Our contribution.** Strengthen the endpoint-marker construction to the stated all-length/all-input threshold interval.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** Separate exact verification of the fixed length-12 seed and 22 required inputs supports the hand proof; finite screens are not the all-input theorem.
- **Empirical:** Not a measured physical or biological claim.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Separate downstream work (does not reopen this result):** No classification of all preserving morphisms or the interval (7/3)^+ through 8/3.

**Proof, review and other accepted-source links:**

- [Stability theorem and review](https://github.com/Sodelin/Research-Commons/blob/2468dc1151c5e9a9dd870024a4fbeff8d4910e4e/research/2026-10-04-dot-complementary-avoidance-stability-0954z/README.md) (proof or status).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** october.SEQ.003. 

</details>

<a id="cb-rna-001"></a>
### A small part of the structure-processing chain is formally connected
**CB-RNA-001 · RNA / E8 / PRISM · source binding**

**Question:** Does the mathematical representation match the stated structure-processing steps?

**What we learned:** A selected checked component connects a balanced scaffold to the specified parser and pair observable.

**What it lets someone do:** Reuse that precise source-level link in a larger RNA verification effort.

**What we cannot conclude:** It does not certify the original C++ programme, physical energies or total probability of a structural class.

**Kind:** lemma. **Mathematical status:** Proved; named Lean scope checked.

<details>
<summary>Exact scope, evidence and separate downstream work</summary>

**Exact statement and assumptions.** Three accepted Lean modules bind the independently encoded balanced scaffold to literal character/stack processing, bounded close actions, partner-table filter and a fixed generated-pair observable. A separate normalized root-carrier theorem excludes two auxiliary constructors from decoded root-W parent events. Exact sources are within the selected 301-module guarded/full-declaration record.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Weighted grammars, RNAshapes/ADP, exact sampling and confidence methods are prior work. Class inverse-image probability requires SUM, not maximum score.

**Our contribution.** Bind the encoded scaffold to specified literal processing and pair readout, without claiming full executable extraction.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** Scoped modules and reused dependencies are accepted; not executable extraction or full physical-model verification.
- **Execution:** Selected formal build record, not new C++ execution.
- **Empirical:** Not a measured physical or biological claim.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Separate downstream work (does not reopen this result):** Original carrier, multiplicities, weights, emitted structures, L5/L6 inverse-image SUM, traceback, executable numerics/RNG and selected-class confidence remain separate.

**Proof, review and other accepted-source links:**

- [Scaffold source package](https://github.com/Sodelin/Research-Commons/blob/2468dc1151c5e9a9dd870024a4fbeff8d4910e4e/research/2026-10-02-dot-e8-scaffold-source-1441z/README.md) (formal receipt).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** october.RNA.001. 

</details>

<a id="cb-nanuq-001"></a>
### A formal chain connects a stated source to its geometric formula
**CB-NANUQ-001 · NANUQ / BIO-1 · phylogenetic geometry**

**Question:** Does the displayed mathematical formula really come from the chosen network construction?

**What we learned:** The selected source-to-formula and geometric-preparation chain is checked.

**What it lets someone do:** Reuse that chain without treating its formula as an unexplained assumption.

**What we cannot conclude:** It is not a full DNA likelihood or an end-to-end biological recovery guarantee.

**Kind:** lemma. **Mathematical status:** Proved; named Lean scope checked.

<details>
<summary>Exact scope, evidence and separate downstream work</summary>

**Exact statement and assumptions.** The 53-source chain derives actual rooted-cap switching/readout, repeated-label anchor, weighted formula, opened-tree and selected-choice correspondence, faithful opened drawings and source-cycle AddCircle maps including parallel bigons. It concerns distinct displayed resolution sets and arithmetic means, not switching multiplicity, NMSC concordance factors or sequence likelihood.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** The all-level hand construction and supplied-order/statistical interfaces predate October; recovering them is not a new discovery.

**Our contribution.** Extend the selected formal chain from actual rooted-cap readout to faithful opened drawings and source-cycle maps.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** Exact dependency reuse, owned audits and six repeated final guards recorded for the 53-source packet.
- **Execution:** No new execution for this board.
- **Empirical:** Not a measured physical or biological claim.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Separate downstream work (does not reopen this result):** Full raw-source embedding/ports, Jordan/face/contour transport, adjacent tips, circular positive support and global composition; do not downgrade inherited hand results.

**Proof, review and other accepted-source links:**

- [Source-to-geometry endpoint](https://github.com/Sodelin/Research-Commons/blob/4e8ea9f05a9716ccdabf2b2197e8699ad6e4bf4f/research/2026-10-05-dot-nanuq-actual-curve-geometry-0806z/README.md) (formal receipt).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** october.NANUQ.001. 

</details>

<a id="cb-msci-001"></a>
### Enough sites preserve the specified ancestry-law distinctions
**CB-MSCI-001 · MSci · DNA and ancestry-law equivalence**

**Question:** Can DNA observations distinguish everything the selected genealogy model distinguishes?

**What we learned:** For the stated fixed model and mutation assumptions, sufficiently long finite loci have exactly the same equality groups.

**What it lets someone do:** Know which demographic ambiguities remain even with those exact DNA laws.

**What we cannot conclude:** It does not promise useful sample sizes or cover relaxed clocks and arbitrary mutation models.

**Kind:** theorem. **Mathematical status:** Proved (not Lean formalized).

<details>
<summary>Exact scope, evidence and separate downstream work</summary>

**Exact statement and assumptions.** For each fixed finite admitted MSci model and its same complete contemporaneous labelled haploid panel, sufficiently long finite homogeneous stationary clock-JC loci have exactly the equality fibres of route-marginal timed genealogy laws.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Published MSci identifiability questions and classical polynomial-family determination/pair-law methods retain attribution.

**Our contribution.** Prove the exact clock-JC observation-equivalence statement for each fixed admitted MSci model.

**Evidence, kept separate:**

- **Hand:** Two written mathematical/source reviews recorded.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** 1395 rational compiler controls independently reproduced, not a universal proof by testing.
- **Empirical:** Not a measured physical or biological claim.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Separate downstream work (does not reopen this result):** Unknown rate mixtures, unphased genotype coarsening, relaxed clocks, other channels and useful locus counts are outside scope.

**Proof, review and other accepted-source links:**

- [Observation-equivalence theorem](https://github.com/Sodelin/Research-Commons/blob/f96399576168328322aab80f1193afaaf4312fef/research/2026-10-05-dot-flouri-clock-jc-conjecture-resolution-0908z/README.md) (proof or status).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** october.MSCI.001. 

</details>

<a id="cb-msci-002"></a>
### Equivalent histories differ only by a coherent hidden renaming in one class
**CB-MSCI-002 · MSci · global history alignment**

**Question:** When do two specified histories make exactly the same genealogy predictions?

**What we learned:** In the admitted class, equality is characterized by one consistent renaming of hidden populations.

**What it lets someone do:** Separate genuine ambiguity from arbitrary changes of labels.

**What we cannot conclude:** This does not include every possible migration, event or hidden-routing mechanism.

**Kind:** theorem. **Mathematical status:** Proved (not Lean formalized).

<details>
<summary>Exact scope, evidence and separate downstream work</summary>

**Exact statement and assumptions.** In the reachable positive finite-epoch class, equality of all finite-sample metric genealogy laws is equivalent to one coherent hidden-population renaming across epochs. Coincident rates, rank deficiency and backward expansion are allowed; a computable finite copy cap is supplied. Silent boundaries, hidden initial routing, continuous migration, instantaneous mergers and alternative biological event factorizations are excluded.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Detailed antecedent attribution has not yet been independently indexed for this card. Consult the linked proof/source register; no new historical-priority claim is inferred.

**Our contribution.** Classify full-law equality by coherent hidden-population renaming in the stated finite-epoch class.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result claimed.
- **Empirical:** Not a measured physical or biological claim.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Separate downstream work (does not reopen this result):** No claim for excluded biological histories or a practical small cap.

**Proof, review and other accepted-source links:**

- [Global alignment theorem](https://github.com/Sodelin/Research-Commons/blob/608f690fd76e216036ed2cd282c236fd0aa4ac46/research/2026-10-05-dot-global-alignment-classification-1007z/README.md) (proof or status).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** october.MSCI.002. 

</details>

<a id="cb-msci-003"></a>
### Two-site population features identify a specific model family
**CB-MSCI-003 · MSci · a fixed nine-parameter family**

**Question:** Can a small collection of exact DNA summary features identify the parameters of this fixed family?

**What we learned:** Yes. Nine means from the stated two-site experiment identify all nine parameters, including equal-rate cases.

**What it lets someone do:** Build exact identification and interval-validation tools for that family.

**What we cannot conclude:** Two sites does not mean two observed bases or certainty from one locus.

**Kind:** theorem. **Mathematical status:** Proved (not Lean formalized).

<details>
<summary>Exact scope, evidence and separate downstream work</summary>

**Exact statement and assumptions.** Global identification for the fixed tree/pulse direction, shared B/C rates, clock and current-block routing uses two homologous columns across six phased labelled haploid sequences per locus and nine means. It improves a valid 55-site sufficient bound. The later Jacobian is everywhere nonsingular and supports joint uncertain-target Krawczyk inclusion, without uniform conditioning or guaranteed numerical contraction.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Classical moment/tensor and interval methods are antecedents; the contribution is the specified family's global identification and exact derivatives.

**Our contribution.** Reduce the fixed-family sufficient observation to two sites/nine means and derive the exact Jacobian/contractor suppliers.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result claimed.
- **Empirical:** Not a measured physical or biological claim.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Separate downstream work (does not reopen this result):** Empirical accuracy, useful locus counts and broader model classes require separate evidence.

**Proof, review and other accepted-source links:**

- [Two-site theorem](https://github.com/Sodelin/Research-Commons/blob/8b4c6508a81dc4c2c146a811adaa0cc01067db60/research/2026-10-05-dot-msci-two-site-nine-feature-identifiability-1150z/README.md) (proof or status).
- [Jacobian and interval contractor](https://github.com/Sodelin/Research-Commons/blob/ebcb33d435eb82f8f18e7f586d8c1f92fe4f32af/research/2026-10-05-dot-msci-joint-jacobian-contractor-1257z/README.md) (proof or status).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** october.MSCI.003. 

</details>

<a id="cb-software-001"></a>
### The solver distinguishes a sharp fixture from genuinely broad data
**CB-SOFTWARE-001 · Practical biological solver**

**Question:** Does the software always return a narrow parameter estimate?

**What we learned:** No. It narrows near-exact fixtures but correctly leaves the archived finite-data case unresolved.

**What it lets someone do:** Use honest unresolved outputs rather than force a precise-looking estimate.

**What we cannot conclude:** A mathematically identifiable model need not be accurately estimable from this dataset.

**Kind:** software check. **Mathematical status:** Scoped software result.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** The integrated release records 43 application cases, a 17-frame informative replay, 50-frame finite-data UNKNOWN replay and Rust compatibility controls. Original-domain complete-cover localization succeeded on two near-exact fixtures; archived 1024-locus bands admit incompatible rA values beyond the requested width.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Detailed antecedent attribution has not yet been independently indexed for this card. Consult the linked proof/source register; no new historical-priority claim is inferred.

**Our contribution.** Implement and review the scoped release, including meaningful unresolved outputs on broad finite-data bands.

**Evidence, kept separate:**

- **Hand:** Release review distinguishes arithmetic, source existence, statistical bands and biological adequacy.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** 43 application cases and recorded informative/UNKNOWN replays; no rerun here.
- **Empirical:** The archived 1024-locus observation bands do not yield the requested accuracy.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** Useful whole-domain nine-parameter empirical accuracy and full native refinement.

**Proof, review and other accepted-source links:**

- [Independent release review](https://github.com/Sodelin/Research-Commons/blob/1c166276d1f0b037a402f01e3b6deaf370c864e3/research/2026-10-09-codex-practical-release-0207z/validation/INDEPENDENT-REVIEW.md) (execution review).

**Connections:**
- [CB-MSCI-003](#cb-msci-003): **reused theorem**. Uses the fixed-family exact identification mathematics; uncertainty still depends on actual data.

**Stable key:** october.SOFTWARE.001. 

</details>

<a id="cb-software-002"></a>
### A tested Rust component is not a universal correctness certificate
**CB-SOFTWARE-002 · Solver infrastructure · count calculations**

**Question:** What does the Rust count pilot actually establish?

**What we learned:** The saved component passed its specified tests and differential checks.

**What it lets someone do:** Reuse the tested bounded calculation while preserving unsupported-input handling.

**What we cannot conclude:** It is not a universal proof that native Rust implements every Lean theorem.

**Kind:** software check. **Mathematical status:** Scoped software result.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** The Rust count pilot uses a normalized Poisson prefix, not residual lumping. The release records 10 tests, 1693 differential cases, 22 invalid inputs and five boundary controls. Resource overflow/unsupported input returns UNKNOWN, not mathematical NO. A separate authenticated native-transfer review records locked offline rebuild evidence.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Detailed antecedent attribution has not yet been independently indexed for this card. Consult the linked proof/source register; no new historical-priority claim is inferred.

**Our contribution.** Implement and test the bounded count component, preserve differential/native rebuild evidence and fail-closed unsupported cases.

**Evidence, kept separate:**

- **Hand:** The linked report/review supports the stated implementation or empirical outcome, not a universal mathematical theorem.
- **Formal:** Tests and scoped transfer evidence are not a proof for all inputs or arbitrary extracted programs.
- **Execution:** Exact checks/rebuild receipts preserved, not newly executed.
- **Empirical:** Not a measured physical or biological claim.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** A universal end-to-end Lean-to-native refinement needs its own theorem and interface.

**Proof, review and other accepted-source links:**

- [Rust count pilot](https://github.com/Sodelin/Research-Commons/blob/2468dc1151c5e9a9dd870024a4fbeff8d4910e4e/research/2026-10-07-rust-count-pilot/README.md) (software evidence).
- [Native transfer rebuild review](https://github.com/Sodelin/Research-Commons/blob/6dbcf5dae2c38dc7b5da162d271ce3faca082ad2/research/2026-10-07-cloud-independent-auditor-1616z/NATIVE-RUST-COUNT-TRANSFER-REBUILD-REVIEW.md) (execution review).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** october.SOFTWARE.002. 

</details>

<a id="cb-emp-bpp-001"></a>
### The saved analyses do not yet support a stable history ranking
**CB-EMP-BPP-001 · Empirical phylogenetics · BPP diagnostics**

**Question:** Did the completed runs settle the competing biological histories?

**What we learned:** No. Matched-layout chains still disagree materially.

**What it lets someone do:** Withhold recommendations until the evidence passes the convergence gate.

**What we cannot conclude:** More archived output is not the same as a supported biological conclusion.

**Kind:** software check. **Mathematical status:** Empirical negative or inconclusive result.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** Official-BPP frog/synthetic runs, controls and matched-layout diagnostics were performed and reviewed. Completed matched-layout chains remain CONVERGENCE_UNRESOLVED. The fail-closed prototype withholds ranked/recommended histories and rejects unknown/tampered evidence.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Detailed antecedent attribution has not yet been independently indexed for this card. Consult the linked proof/source register; no new historical-priority claim is inferred.

**Our contribution.** Perform and review the recorded diagnostics, then withhold a ranking because the convergence gate is not met.

**Evidence, kept separate:**

- **Hand:** Review supports the stated unresolved status, not a new biological theorem.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** Actual recorded runs and instrumentation, not new execution.
- **Empirical:** Material chain disagreement prevents accepted ranked history.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** Resolve convergence/admission before a biological recommendation.

**Proof, review and other accepted-source links:**

- [Completed diagnostic](https://github.com/Sodelin/Research-Commons/blob/647baeb1907387e9046eba815f3470475bf65872/research/2026-10-05-dot-bpp-matched-layout-completed-diagnostic-0815z/README.md) (proof or status).
- [Fail-closed release](https://github.com/Sodelin/Research-Commons/blob/b09b051471985ad9e24246700bf998d8ae526078/research/2026-10-05-dot-bpp-fail-closed-release-prototype-0825z/README.md) (proof or status).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** october.EMP.BPP.001. 

</details>

<a id="cb-emp-tsuga-001"></a>
### Different markers disagree, but the cause is not established
**CB-EMP-TSUGA-001 · Empirical phylogenetics · Tsuga**

**Question:** Does marker disagreement prove a particular capture history?

**What we learned:** No. The small comparison reproduces disagreement but does not establish its cause or timing.

**What it lets someone do:** Keep the observation without overinterpreting it.

**What we cannot conclude:** This is not a capture probability, direction or dated biological event.

**Kind:** software check. **Mathematical status:** Empirical negative or inconclusive result.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** The four-specimen public nuclear/plastid comparison reproduces marker discordance. Orthology, specimen identity, linked plastid units and sequence-to-source calibration remain unresolved: NOT_ADMITTED / capture UNKNOWN. Later accession recovery does not restore missing original matrices.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Detailed antecedent attribution has not yet been independently indexed for this card. Consult the linked proof/source register; no new historical-priority claim is inferred.

**Our contribution.** Reproduce the small marker disagreement while explicitly refusing an unadmitted capture inference.

**Evidence, kept separate:**

- **Hand:** Observation and source-admission limits explicitly recorded.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** Selected public comparison preserved.
- **Empirical:** No source-admitted capture inference.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** Resolve source admission and calibration before causal/directional/timing claims.

**Proof, review and other accepted-source links:**

- [Empirical integration milestones](https://github.com/Sodelin/Research-Commons/blob/8ede352cfa00f9c7e115da1f82d1e5772544a21f/research/2026-10-08-codex-integration-0825z/g6/EMPIRICAL-INTEGRATION-MILESTONES.md) (proof or status).

**Connections:**
- [CB-G6-001](#cb-g6-001): **candidate connection**. G6-style certification would require the missing empirical-to-source admission.

**Stable key:** october.EMP.TSUGA.001. 

</details>

<a id="cb-materials-001"></a>
### One descriptor can hide a change in the next-step behaviour
**CB-MATERIALS-001 · Materials · what a descriptor leaves out**

**Question:** Does the recorded descriptor contain everything needed for the next update?

**What we learned:** Not for the specified one-attempt model: two states share the descriptor but have different transition probabilities.

**What it lets someone do:** Avoid treating that descriptor as a complete state description.

**What we cannot conclude:** This does not yet prove failure at the actual sparse recording cadence or describe synthesis kinetics.

**Kind:** counterexample. **Mathematical status:** Proved (not Lean formalized).

<details>
<summary>Exact scope, evidence and separate downstream work</summary>

**Exact statement and assumptions.** A reviewed exact one-attempt lattice descriptor collision changes transition mass. The later fixed-initializer, actual-cadence history determinant has positive conditioning probabilities, but its nonzero value remains unproved.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Classical state aggregation and Markov sufficiency are antecedents; the claim binds a collision to this actual one-attempt lattice update.

**Our contribution.** Construct the exact descriptor collision for the actual one-attempt transition.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result claimed.
- **Empirical:** Not a measured physical or biological claim.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Separate downstream work (does not reopen this result):** Prove the actual sparse-cadence determinant nonzero or another source-faithful result; equilibrium Monte Carlo is not synthesis kinetics.

**Proof, review and other accepted-source links:**

- [Exact one-attempt obstruction](https://github.com/Sodelin/Research-Commons/blob/ab80109bcaf0edec8bc3eb58aea2fd369d824fa6/research/2026-10-15-codex-materials-exact-obstruction-2052z/MATERIALS-EXACT-MIXTURE-OBSTRUCTION-01.md) (proof or status).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** october.MATERIALS.001. 

</details>

<a id="cb-diffraction-001"></a>
### A good fit alone does not certify a molecule's presence
**CB-DIFFRACTION-001 · Diffraction · selected fits versus physical presence**

**Question:** What would turn a fitted diffraction structure into a defensible physical conclusion?

**What we learned:** A conditional set-based certificate specifies the required uncertainty and alternative-model checks.

**What it lets someone do:** Know what evidence is needed before interpreting a selected fit.

**What we cannot conclude:** The available labels alone do not produce that physical certificate.

**Kind:** theorem. **Mathematical status:** Proved under the stated premises (not Lean formalized).

<details>
<summary>Exact scope, evidence and separate downstream work</summary>

**Exact statement and assumptions.** The conditional nuisance/set-membership certificate separates selected fit, physical molecular presence, exact boundary attainment and E/I geometry provenance. Thirty-two structure labels were recovered, but numeric profiles/templates, fit registry and calibrated errors were not, so no empirical fit or physical certificate was produced.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Elementary inverse-set/set-membership mathematics is established prior work. The contribution is the source-specific conditions and evidence audit.

**Our contribution.** Specify the source-specific conditional certificate and audit the missing numeric evidence.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result claimed.
- **Empirical:** No calibrated physical inference was produced.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Separate downstream work (does not reopen this result):** Acquire justified numeric profiles, templates, registry and uncertainty model.

**Proof, review and other accepted-source links:**

- [Conditional certificate](https://github.com/Sodelin/Research-Commons/blob/6a7d50f699245c87727961f59808c1ec0c9adfe5/research/2026-10-16-ge-diffraction-certification/CONDITIONAL-CERTIFICATE-01.md) (proof or status).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** october.DIFFRACTION.001. 

</details>

<a id="cb-viewshed-001"></a>
### Failed runs are now accounted for explicitly
**CB-VIEWSHED-001 · Geospatial software · reliable viewshed runs**

**Question:** Can a runner accidentally count incomplete or failed calculations as successful?

**What we learned:** The source-preserving repair checks outputs, restarts and failure accounting explicitly.

**What it lets someone do:** Make the recorded computational workflow more reliable.

**What we cannot conclude:** Injected failures do not show that a published geographic conclusion was wrong.

**Kind:** software check. **Mathematical status:** Scoped software result.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** Quinn runner repair validates subprocess/raster outcomes, exact restart row identity and failure accounting. Contributor evidence records 18 tests, 12 paired plus two repair-only controls; two successful pairs have identical raster arrays. Independent review read source and complete stored JSON, not a new GDAL replay.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Detailed antecedent attribution has not yet been independently indexed for this card. Consult the linked proof/source register; no new historical-priority claim is inferred.

**Our contribution.** Repair source-level failure/restart checks and preserve paired execution evidence.

**Evidence, kept separate:**

- **Hand:** Actual source and stored evidence inspected, not independently rerun GDAL.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** 18 tests and paired controls are reported with their stored evidence.
- **Empirical:** No claim about prevalence of failure or published Washington findings.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** NoData, historical-platform and original-input reproduction remain open.

**Proof, review and other accepted-source links:**

- [Scoped runner review](https://github.com/Sodelin/Research-Commons/blob/6197a000949b7c977cd34aa3ae529bf481d7ebf1/research/2026-10-16-quinn-reliable-runner-review/INDEPENDENT-REVIEW-03.md) (execution review).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** october.VIEWSHED.001. 

</details>

<a id="cb-sport-baseball-001"></a>
### The tested models did not pass the stronger improvement test
**CB-SPORT-BASEBALL-001 · Sports · baseball model evaluation**

**Question:** Did the new baseball calculation beat the relevant alternatives?

**What we learned:** Not at the stated acceptance threshold: the tested improvements failed the stronger comparison.

**What it lets someone do:** Keep a negative result rather than advertise an unearned predictive advantage.

**What we cannot conclude:** These outputs are not complete WAR, causal player value or current forecasts.

**Kind:** software check. **Mathematical status:** Empirical negative or inconclusive result.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** Six 2020–25 seasons, 979855 completed plate appearances and 738 historical September 2025 records were processed. Handedness-standardized change failed its comparison; component ridge improved over weak persistence but failed the stronger shrinkage-improvement gate. Independent numerical refits reproduced the outcomes. Missing components are not zero.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Standard component models, shrinkage and out-of-sample comparison are established methods; no new statistical method priority claimed.

**Our contribution.** Build the historical partial-component evaluation and independently reproduce its negative stronger-comparison result.

**Evidence, kept separate:**

- **Hand:** The linked report/review supports the stated implementation or empirical outcome, not a universal mathematical theorem.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** Saved evaluations independently reproduced.
- **Empirical:** Historical supported partial subtotals only; no current 2026 recommendation.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** A model that clears the declared stronger evaluation and complete target accounting.

**Proof, review and other accepted-source links:**

- [Integration and evaluation report](https://github.com/Sodelin/Research-Commons/blob/1138a5b1a281caa00b38e0976db95b586938754b/research/2026-10-21-dot-baseball-integration-report-1948z/BASEBALL-REPORT.md) (proof or status).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** october.SPORT.BASEBALL.001. 

</details>

<a id="cb-sport-basketball-001"></a>
### An apparent model improvement is not accepted
**CB-SPORT-BASKETBALL-001 · Sports · basketball data validation**

**Question:** Can we trust the fitted basketball comparison yet?

**What we learned:** No. Score and duration reconciliation failed, so the fitted comparison is withheld.

**What it lets someone do:** Separate tested software from trustworthy predictive evidence.

**What we cannot conclude:** A lower fitted error on unreconciled data is not an accepted improvement.

**Kind:** software check. **Mathematical status:** Empirical negative or inconclusive result.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** A conditional offense/defense/context/exposure pipeline and 20 implementation tests exist. Real fitted comparison is quarantined because external score/duration reconciliation failed. Opponent exposure was reconstructible and is not the decisive missing input; publisher-reference calculations are separate.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Conditional rate modelling and exposure accounting are established methods, not evidence of a new superior statistic.

**Our contribution.** Build/test the conditional pipeline and quarantine the fitted comparison when data reconciliation fails.

**Evidence, kept separate:**

- **Hand:** The linked report/review supports the stated implementation or empirical outcome, not a universal mathematical theorem.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** 20 implementation tests do not validate the unreconciled empirical comparison.
- **Empirical:** No predictive improvement accepted.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** A permitted correctly reconciled possession/lineup corpus and fresh declared evaluation.

**Proof, review and other accepted-source links:**

- [Pipeline and evidence gate](https://github.com/Sodelin/Research-Commons/blob/2468dc1151c5e9a9dd870024a4fbeff8d4910e4e/research/2026-10-21-dot-basketball-pipeline-audit-1941z/README.md) (proof or status).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** october.SPORT.BASKETBALL.001. 

</details>

<a id="cb-alexander-001"></a>
### One host cannot contain every member of the stated restricted class
**CB-ALEXANDER-001 · Alexander structures · restricted universality**

**Question:** Can a single allowed structure contain every example in this restricted family?

**What we learned:** No, under the stated branching cap and way of embedding one structure into another.

**What it lets someone do:** Rule out that precise universal-host proposal.

**What we cannot conclude:** This does not rule out unrestricted hosts or a different notion of embedding.

**Kind:** theorem. **Mathematical status:** Proved (not Lean formalized).

<details>
<summary>Exact scope, evidence and separate downstream work</summary>

**Exact statement and assumptions.** For each nonempty fixed-word-avoiding class with the declared balanced-child cap, no single universal host exists under the stated injective adjacency embeddings. Changed caps, unrestricted host classes and edge-to-path embeddings are excluded.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Prior Alexander-structure and word-avoidance framework is retained in the proof; this card claims only the capped embedding obstruction.

**Our contribution.** Prove the fixed-word-avoiding balanced-cap obstruction under the exact injective-adjacency embedding contract.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result claimed.
- **Empirical:** Not a measured physical or biological claim.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Separate downstream work (does not reopen this result):** Unrestricted universality remains a different question.

**Proof, review and other accepted-source links:**

- [Capped-universality theorem](https://github.com/Sodelin/Research-Commons/blob/7206e66a8de0b04725924e32df822eca530b1143/research/2026-10-09-dot-alexander-capped-universality-2055z/README.md) (proof or status).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** october.ALEXANDER.001. 

</details>

<a id="cb-g7-002"></a>
### One labelled programme can be optimal in a specified test menu
**CB-G7-002 · G7 · exact marker costs**

**Question:** How many controlled settings are really needed in this particular menu?

**What we learned:** The stated natural-plus-marker task has a sharp worst-case cost.

**What it lets someone do:** Use an exact benchmark for that authorised testing setup.

**What we cannot conclude:** It does not apply to noisy finite data or unknown control labels.

**Kind:** theorem. **Mathematical status:** Proved (not Lean formalized).

<details>
<summary>Exact scope, evidence and separate downstream work</summary>

**Exact statement and assumptions.** For r≥1 original hybrid sites and n≥4 in the specified original model, natural plus labelled forced-marker observations with known INDEPENDENT mode or unknown COMMON/INDEPENDENT mode have sharp worst-case site union r, two positive-support configurations and one labelled exact-law programme when support cap L≥2; programme count is ceil(2/L). Known COMMON alone has passive cost 0 sites/1 configuration/1 programme.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Reuses the programme's original-ID intervention semantics and exact natural observation results; labelled support is part of the experiment, not a free additional measurement.

**Our contribution.** Prove the matching upper construction and worst-case lower cost for this exact marker menu.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result claimed.
- **Empirical:** Not a measured physical or biological claim.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Separate downstream work (does not reopen this result):** No located specific Lean realization of these optimum formulas is claimed.

**Proof, review and other accepted-source links:**

- [Natural-marker theorem](https://github.com/Sodelin/Research-Commons/blob/b74ff892402f5d842bb19178a3243f7ef0c0c481/research/2026-10-01-sol61-head-audit-1956z/NATURAL-MARKER-OPTIMUM.md) (proof or status).
- [Independent acceptance](https://github.com/Sodelin/Research-Commons/blob/b74ff892402f5d842bb19178a3243f7ef0c0c481/research/2026-10-01-sol61-head-audit-1956z/NATURAL-MARKER-REVIEW.md) (hand review).

**Connections:**
- [CB-G7-001](#cb-g7-001): **reused theorem**. A scoped cost benchmark within the complete exact-law design framework.

**Stable key:** original.G7.NATURAL_MARKER_OPTIMUM. 

</details>

<a id="cb-g7-003"></a>
### A different menu has a classical covering-array cost
**CB-G7-003 · G7 · static full-forcing costs**

**Question:** What if every allowed setting fully forces the routing and is chosen in advance?

**What we learned:** The exact numerical-law task has a sharp cost expressed by a covering-array quantity.

**What it lets someone do:** Use the right benchmark for this different static menu.

**What we cannot conclude:** It is not an adaptive-policy lower bound or a result for arbitrary randomized decisions.

**Kind:** theorem. **Mathematical status:** Proved (not Lean formalized).

<details>
<summary>Exact scope, evidence and separate downstream work</summary>

**Exact statement and assumptions.** For r≥2 in the stated STATIC full-forcing-only numerical-law menu, parameter-oblivious support optimum is D=C(r), with K=ceil(C(r)/L) programmes at support cap L. The proof uses classical covering-array capacity and an actual-source matching numerical collision. Unknown IDs, finite-data confidence and adaptive full-forcing optima are excluded.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Covering-array capacity is classical; it is not a new combinatorial discovery. The source-valid numerical collision justifies applying that lower benchmark here.

**Our contribution.** Bind the classical support optimum to this actual static original-source observation/cost model.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result claimed.
- **Empirical:** Not a measured physical or biological claim.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Separate downstream work (does not reopen this result):** Adaptive or differently labelled/observed menus need separate proofs; no specific Lean optimum package is asserted.

**Proof, review and other accepted-source links:**

- [Full-forcing numerical optimum](https://github.com/Sodelin/Research-Commons/blob/e07e0ebefe80ca75b794551021df84998bb072a0/research/2026-10-01-sol61-head-audit-1956z/FULL-FORCING-NUMERICAL-OPTIMUM.md) (proof or status).
- [Later master acceptance, section 6](https://github.com/Sodelin/Research-Commons/blob/539c814ac470fde8147b0e1e6d5307972585b6f8/research/2026-10-01-sol61-head-audit-1956z/G7-EXACT-MASTER-REVIEW.md) (hand review).

**Connections:**
- [CB-G7-001](#cb-g7-001): **same principle**. A distinct declared-menu optimum, not the general master or arbitrary adaptive extension.

**Stable key:** original.G7.STATIC_FULL_FORCING_OPTIMUM. 

</details>


<a id="cb-seq-004"></a>
### Every start and phase has an exact matching answer
**CB-SEQ-004 · Sequences · exact matching graphs**

**Question:** How long can a prescribed Thue–Morse pattern be followed from any starting point?

**What we learned:** There is an exact all-start formula and digit evaluator, plus an attained maximum for every phase and an exact classification of sharp cases.

**What it lets someone do:** Compute the actual longest match and distinguish ordinary starts from exceptional long matches without scanning every path.

**What we cannot conclude:** This is a target-dependent graph result, not every possible pattern search, arithmetic-progression statistic or biological measurement.

**Kind:** theorem. **Mathematical status:** Proved; archived Lean check recorded.

<details>
<summary>Exact scope, prior work, evidence and separate downstream work</summary>

**Exact statement and assumptions.** For digit-parity Thue–Morse t, the graph has edges w−1→w labelled t(w) and w−2→w labelled 1−t(w), for w≥2, and no edge 0→1. A path's kth edge must read t(k). The attained maximum L(v) has a complete closed form for all natural v, with L(0)=1. For v≥1, 3L(v)≤8v−1, with equality exactly at v=3·2^n−1, where L=8·2^n−3. The proved ten-coordinate integer digit recurrence evaluates this maximum. For the own-target graph of s_a(k)=t(k+a), shifting both target and graph, an actual maximum exists at every natural a,v. For v≥1, 3L_a(v)≤8v+5a−1, with equality iff some n≥0 has a≤2^n and v=3·2^n−a−1; then L_a(v)=8·2^n−a−3. Named endpoints are FullHeight.height_isMaximum/height_closed_form, DigitRecurrence.evaluate_isMaximum, PhaseHeight.height_isMaximum and PhaseExtremal.shifted_extremal_iff.

**Origin.** project posed. A precise source-specific result within the existing sequence programme. Related published problems, constructions and known special cases are credited separately; this grouped card is not a claim to multiple newly solved field questions.

**Prior work.** The underlying binary population is attributed to the pinned September 2026 biological-unavoidability manuscript. Candidate height tables and digit representation came from the preserved source-side investigation; finite experiments were discovery evidence, not the universal proof. Digit representations are an established method.

**Our contribution and attribution.** The original Samuel repository proves the actual graph-to-formula bridge, digit recurrence and complete phase-extremal necessity/attainment. This card restores that completed source programme alongside, not as an alias of, CB-SEQ-001's arithmetic-progression result.

**Evidence, kept separate:**

- **Hand:** The original proof/status notes and integrated publication inventory identify the completed source-bound theorem. Relevant actual archived endpoint entries were inspected. No fresh transitive mathematical review or external human review is claimed.
- **Formal:** The source repository's 25 September 2026 Lean 4.33.1 formal-audit.json names the relevant endpoints and records only propext, Classical.choice and Quot.sound. Its 405 endpoints cover the wider repository, not 405 sequence discoveries. No checking was rerun.
- **Execution:** Historical source/axiom/build evidence is recorded in the linked audit. No Lean, compiler or scientific runtime was executed for this recovery.
- **Empirical:** An exact mathematical statement for the defined graph, symbolic word or arithmetic code. No measured performance, biological data, security, compression or hardware conclusion is implied.

**Novelty:** Historical priority is unassessed. Recorded correctness and formal checking do not establish novelty; established special cases and methods retain their attribution.

**Separate downstream work (does not reopen this result):** No joint logarithmic phase/start algorithm, minimal recurrence dimension or integer bit-complexity bound is claimed. Shifting the reading word in the unchanged graph is a different problem. Old candidate/pending integration notes are superseded by the linked final source and receipt.

**Proof, review and related source links:**

- [Complete all-start matching-height proof](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/notes/FULL-HEIGHT-PROOF.md) (proof or status).
- [Exact digit evaluator](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/notes/DIGIT-RECURRENCE.md) (proof or status).
- [All-phase actual maximum](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/notes/PHASE-HEIGHT-FORMALIZATION.md) (proof or status).
- [Sharp phase-extremal classification](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/notes/PHASE-EXTREMAL-FORMALIZATION.md) (proof or status).
- [Integrated September source coverage](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/publication-2026-09-29/COVERAGE.md) (proof or status).
- [Archived exact endpoint and axiom receipt](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/verification/formal-audit.json) (formal receipt).

**Connections:**

- [CB-SEQ-001](#cb-seq-001): **same principle**. Both concern Thue–Morse and alignment, but matching-path height L(v) is not maximum monochromatic arithmetic-progression length A(d).

**Stable key:** sequences.MATCHING_ALL_START_PHASE_DIGIT. **Aliases:** Samuel T01 and T02; FullHeight; DigitRecurrence; PhaseHeight; PhaseExtremal.

</details>


<a id="cb-seq-005"></a>
### Finite prefix changes have an exactly computable global cost
**CB-SEQ-005 · Sequences · finite-edit robustness**

**Question:** If the beginning of the target pattern changes, can its worst global matching penalty still be found exactly?

**What we learned:** Yes. An explicit finite search finds the smallest additive allowance that works at every positive start, and a start inside the search attains it.

**What it lets someone do:** Certify the exact robustness cost for one specified finite prefix edit, not just use a universal overestimate.

**What we cannot conclude:** The theorem does not give a fast practical search or cover arbitrary edits indefinitely far along the sequence.

**Kind:** theorem. **Mathematical status:** Proved; archived Lean check recorded.

<details>
<summary>Exact scope, prior work, evidence and separate downstream work</summary>

**Exact statement and assumptions.** Let m≥0 and let a binary target s agree with digit-parity Thue–Morse at every index k≥m, with no restrictions on its first m bits. Let L_s(v) be the attained maximum matching length in the original own-target BinaryAvoidance graph. Set N(m)=3·2^(m+3)+m and B_s=max_{1≤v≤N(m)}(3L_s(v)−8v), in the integers. Every positive v satisfies 3L_s(v)≤8v+B_s, some positive v≤N(m) attains equality, and an integer B is valid at every positive start iff B_s≤B. Also −1≤B_s≤8m−1. FiniteEditExact.height computes the needed maximum; FiniteEditOptimum.individual_optimum_attained and individual_additive_constant_iff supply the global finite-reduction endpoint.

**Origin.** project posed. A precise source-specific result within the existing sequence programme. Related published problems, constructions and known special cases are credited separately; this grouped card is not a claim to multiple newly solved field questions.

**Prior work.** The own-target graph and unedited/phase matching results are inherited from the Samuel programme and its attributed population construction. The finite-path transport theorem, actual maximum and sharp uniform bound are suppliers, not independently recounted discoveries.

**Our contribution and attribution.** The original continuation strengthens uniform allowance 8m−1 to the exact optimum for each individual edited target, with a proved finite cutoff and attainment. Five promoted modules and selected endpoint counts describe proof organization, not five distinct discoveries.

**Evidence, kept separate:**

- **Hand:** The original proof/status notes and integrated publication inventory identify the completed source-bound theorem. Relevant actual archived endpoint entries were inspected. No fresh transitive mathematical review or external human review is claimed.
- **Formal:** The source repository's 25 September 2026 Lean 4.33.1 formal-audit.json names the relevant endpoints and records only propext, Classical.choice and Quot.sound. Its 405 endpoints cover the wider repository, not 405 sequence discoveries. No checking was rerun.
- **Execution:** Historical source/axiom/build evidence is recorded in the linked audit. No Lean, compiler or scientific runtime was executed for this recovery.
- **Empirical:** An exact mathematical statement for the defined graph, symbolic word or arithmetic code. No measured performance, biological data, security, compression or hardware conclusion is implied.

**Novelty:** Historical priority is unassessed. Recorded correctness and formal checking do not establish novelty; established special cases and methods retain their attribution.

**Separate downstream work (does not reopen this result):** The cutoff is deliberately generous and exponential in m; minimal cutoff and practical runtime are not asserted. m bounds the location of possible edits, not merely their number. No new execution is needed to retain the completed theorem.

**Proof, review and related source links:**

- [Finite-edit transport and uniform stability](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/notes/FINITE-EDIT-STABILITY-FORMALIZATION.md) (proof or status).
- [Complete individual finite-edit optimum](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/notes/REFINEMENT-INDIVIDUAL-FINITE-EDIT.md) (proof or status).
- [Integrated September source coverage](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/publication-2026-09-29/COVERAGE.md) (proof or status).
- [Archived exact endpoint and axiom receipt](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/verification/formal-audit.json) (formal receipt).

**Connections:**

- [CB-SEQ-004](#cb-seq-004): **reused theorem**. The actual all-start height and phase/extremal structure supply the finite reduction and its sharp tail witness.

**Stable key:** sequences.FINITE_EDIT_INDIVIDUAL_OPTIMUM. **Aliases:** Samuel T03; FiniteEditOptimum.

</details>


<a id="cb-seq-006"></a>
### Huge finite matches need not become an infinite match
**CB-SEQ-006 · Sequences · quantitative aperiodic avoidance**

**Question:** Does matching longer and longer finite patterns imply that some infinite match exists?

**What we learned:** Not in this model. A specified word's period-break data bounds its matches, yet suitable aperiodic targets have finite matches exceeding any supplied growth schedule while admitting no infinite match.

**What it lets someone do:** Separate a genuine infinite-realization claim from very large finite evidence, and obtain explicit bounds when a period-break modulus is supplied.

**What we cannot conclude:** There is no one target asserted to beat every growth function, nor a word-independent bound for all aperiodic targets.

**Kind:** theorem. **Mathematical status:** Proved; archived Lean check recorded.

<details>
<summary>Exact scope, prior work, evidence and separate downstream work</summary>

**Exact statement and assumptions.** In the manuscript's own-target graph P_s, a modulus M(v,b) supplies, for each offset d≤v, an index i in [b,M(v,b)) at which s(i) differs from the label required for a constant-offset two-step edge. Equivalently, even d=2e breaks antiperiod e+1 and odd d=2e+1 breaks period e+1. With B_0=0 and B_{r+1}=M(v,B_r), every actual matching prefix from v has length ell<B_{v+1}. If M(v,b)≤b+R, then ell<(v+1)R. Every non-eventually-periodic target has such a modulus, with existence using choice. Conversely, for every f:Nat→Nat there exists a non-eventually-periodic target s, with no infinite matching path in P_s, and strictly increasing starts v_j having finite matching prefixes longer than f(v_j). The target may depend on f. Named audited endpoints include QuantitativeModulus.prefix_length_lt_clock, prefix_length_lt_uniform_windows and SlowAvoidance.arbitrarily_slow_avoidance.

**Origin.** project posed. A precise source-specific result within the existing sequence programme. Related published problems, constructions and known special cases are credited separately; this grouped card is not a claim to multiple newly solved field questions.

**Prior work.** The own-target avoidance construction belongs to the September classification programme; its eventually-periodic positive direction credits Alexander. Iterated bounds and finite-state periodicity are established principles. The exact source-specific modulus and slow-construction claims must not be represented as a universal graph theorem.

**Our contribution and attribution.** The original source makes both sides precise: an explicit bound from supplied failure-of-periodicity data and an arbitrary prescribed slow-growth counterexample to word-independent quantitative inference.

**Evidence, kept separate:**

- **Hand:** The original proof/status notes and integrated publication inventory identify the completed source-bound theorem. Relevant actual archived endpoint entries were inspected. No fresh transitive mathematical review or external human review is claimed.
- **Formal:** The source repository's 25 September 2026 Lean 4.33.1 formal-audit.json names the relevant endpoints and records only propext, Classical.choice and Quot.sound. Its 405 endpoints cover the wider repository, not 405 sequence discoveries. No checking was rerun.
- **Execution:** Historical source/axiom/build evidence is recorded in the linked audit. No Lean, compiler or scientific runtime was executed for this recovery.
- **Empirical:** An exact mathematical statement for the defined graph, symbolic word or arithmetic code. No measured performance, biological data, security, compression or hardware conclusion is implied.

**Novelty:** Historical priority is unassessed. Recorded correctness and formal checking do not establish novelty; established special cases and methods retain their attribution.

**Separate downstream work (does not reopen this result):** A supplied modulus gives an explicit clock; merely knowing a word is aperiodic is not a uniform effective input representation. The construction uses a target-dependent graph, not one graph avoiding every aperiodic target. General biological acquisition and arbitrary graph recognition are separate.

**Proof, review and related source links:**

- [Quantitative modulus theorem and exact source condition](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/notes/QUANTITATIVE-MODULUS-THEOREM.md) (proof or status).
- [Arbitrarily slow avoidance theorem](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/notes/SLOW-AVOIDANCE-FORMALIZATION.md) (proof or status).
- [Original classification manuscript](https://github.com/avg-netizen/biological-unavoidability/blob/3d6175e3e23f67bd68e7be591b5a9a6d04e496a3/paper.md) (proof or status).
- [Integrated September source coverage](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/publication-2026-09-29/COVERAGE.md) (proof or status).
- [Archived exact endpoint and axiom receipt](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/verification/formal-audit.json) (formal receipt).

**Connections:**

No theorem-transfer dependency is asserted by this card.

**Stable key:** sequences.QUANTITATIVE_AND_SLOW_AVOIDANCE. **Aliases:** Samuel T07; QuantitativeModulus; SlowAvoidance.

</details>


<a id="cb-seq-007"></a>
### Typical-scale totals differ sharply from exceptional long matches
**CB-SEQ-007 · Sequences · exact aggregate matching heights**

**Question:** What happens when we total matching lengths across all starts rather than choose the most extreme one?

**What we learned:** An exact formula gives the total below every power of two, and a digit algorithm computes the total below any cutoff. The mean grows logarithmically even though selected starts have linear height.

**What it lets someone do:** Calculate exact aggregate behavior at large cutoffs without enumerating every starting point.

**What we cannot conclude:** A mean alone is not a concentration bound, a typical-value theorem or a limiting distribution.

**Kind:** theorem. **Mathematical status:** Proved by hand; acceptance recorded in complete reading edition.

<details>
<summary>Exact scope, prior work, evidence and separate downstream work</summary>

**Exact statement and assumptions.** For the actual attained matching height L(v) of CB-SEQ-004, let A_k=sum_{0≤v<2^k} L(v). Then A_0=1, A_1=1, A_2=6, and for k≥3, A_k=29(3k+1)2^k/72−(k+3)−(7/9)(−1)^k. Consequently A_k/2^k is asymptotic to (29/24)k. The inherited ten-coordinate digit representation yields a fixed-size algorithm computing sum_{0≤v<N}L(v) in O(log N) integer-matrix operations for positive N, with zero cutoff handled directly. The hand proof includes a finite matrix-annihilator identity and exact base cases; it is not extrapolation from numerical totals.

**Origin.** project posed. A precise source-specific result within the existing sequence programme. Related published problems, constructions and known special cases are credited separately; this grouped card is not a claim to multiple newly solved field questions.

**Prior work.** The regular-sequence summation framework is established in Allouche–Shallit and Heuberger–Krenn–Lechner. The exact inherited recurrence is already proved in the Samuel source. General digit summation is not claimed as a newly invented method.

**Our contribution and attribution.** The October hand proof derives and checks the exact coefficients and arbitrary-cutoff update for this specific graph height. It adds aggregate information beyond the already completed sharp maximum analysis.

**Evidence, kept separate:**

- **Hand:** The complete reading edition contains actual mathematical arguments and explicitly records independent AI hand acceptance. Its archival README says not all original separately hashed proof/checker/review files were recovered. This card does not invent those missing receipts or claim a new review.
- **Formal:** No kernel verification of this hand result is claimed. A separately checked inherited recurrence or another sequence theorem does not automatically formalize this consequence.
- **Execution:** The archive reports exact supplementary controls where relevant. They do not replace the uniform hand proof; original computation banks are not reconstructed or rerun here.
- **Empirical:** An exact mathematical statement for the defined graph, symbolic word or arithmetic code. No measured performance, biological data, security, compression or hardware conclusion is implied.

**Novelty:** Historical priority is unassessed. Recorded correctness and formal checking do not establish novelty; established special cases and methods retain their attribution.

**Separate downstream work (does not reopen this result):** Second moments, concentration and limiting distributions remain separate proposed questions. O(log N) counts fixed-size integer operations, not total bit complexity. The inherited formal recurrence does not make this new summation argument kernel-verified.

**Proof, review and related source links:**

- [Complete hand proof: exact dyadic average and cutoff algorithm](https://github.com/Sodelin/Research-Commons/blob/74ba3079/research/2026-10-05-dot-sequence-reading-editions-0100z/Thue-Morse-Hand-Proofs.md) (proof or status).
- [Inherited exact digit recurrence](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/notes/DIGIT-RECURRENCE.md) (proof or status).
- [Reading-edition acceptance record and mandatory successor corrections](https://github.com/Sodelin/Research-Commons/blob/74ba3079/research/2026-10-05-dot-sequence-reading-editions-0100z/README.md) (proof or status).

**Connections:**

- [CB-SEQ-004](#cb-seq-004): **reused theorem**. Uses the exact graph-to-height digit recurrence, not a fitted recurrence or the unrelated arithmetic-progression formulas.

**Stable key:** sequences.MATCHING_HEIGHT_AGGREGATE. **Aliases:** Thue–Morse dyadic matching-height average; Arbitrary-cutoff height sum.

</details>


<a id="cb-seq-008"></a>
### A precise coding transfers patterns without preserving every property
**CB-SEQ-008 · Sequences · constrained juggling and enumeration**

**Question:** What survives when a binary pattern is turned into a juggling schedule?

**What we learned:** An explicit coding preserves constrained matching lengths exactly, while equal versus unequal block lengths determine whether the prescribed-prefix generating function is rational.

**What it lets someone do:** Use a fully specified encoding to transfer a theorem and understand why restricting a freely concatenable system changes its counting law.

**What we cannot conclude:** This is not a new unrestricted juggling-height bound, an unrestricted counting theorem, or a practical compression result.

**Kind:** theorem. **Mathematical status:** Proved by hand; acceptance recorded in complete reading edition.

<details>
<summary>Exact scope, prior work, evidence and separate downstream work</summary>

**Exact statement and assumptions.** At the three-ball ground state, encode 0 by primitive block (3) and 1 by (4,2). Expand each original matching-graph edge into its own code path, retaining original vertices and distinct internal vertices. Starting only at an original v, the attained constrained throw-match height is H(v)=W(L(v)), where W(2m)=3m and W(2m+1)=3m+1+t(m). For v≥1, H(v)≤4v with equality exactly v=3·2^(2r)−1. Separately, choose two distinct primitive loops at one fixed b-ball state, with positive beat lengths a,c, and count exactly one word for each Thue–Morse block-prefix length, including the empty prefix. Its series F_{a,c}(z) equals [1+(z^a+z^c)/2]/(1−z^(a+c))+(z^a−z^c)P(z^(a+c))/2, where P(x)=product_{r≥0}(1−x^(2^r)). If a=c then F=1/(1−z^a); if a≠c the unit circle is a natural boundary. For b≥2, F(b^(−s))−1 has boundary Re(s)=0.

**Origin.** project posed. A precise source-specific result within the existing sequence programme. Related published problems, constructions and known special cases are credited separately; this grouped card is not a claim to multiple newly solved field questions.

**Prior work.** Primitive juggling-state coding and unrestricted enumeration are established, including Chung–Graham, Elsner–Klyve–Tou and Tou. The Thue–Morse product's natural-boundary theory is classical, as credited to Allouche's discussion. This is a specified application, not a contradiction to their unrestricted rationality results.

**Our contribution and attribution.** The October source supplies an exact observation-preserving constrained-graph adapter and the explicit prefix-series formula, with the different graph, physical-height and enumeration objects kept separate.

**Evidence, kept separate:**

- **Hand:** The complete reading edition contains actual mathematical arguments and explicitly records independent AI hand acceptance. Its archival README says not all original separately hashed proof/checker/review files were recovered. This card does not invent those missing receipts or claim a new review.
- **Formal:** No kernel verification of this hand result is claimed. A separately checked inherited recurrence or another sequence theorem does not automatically formalize this consequence.
- **Execution:** The archive reports exact supplementary controls where relevant. They do not replace the uniform hand proof; original computation banks are not reconstructed or rerun here.
- **Empirical:** An exact mathematical statement for the defined graph, symbolic word or arithmetic code. No measured performance, biological data, security, compression or hardware conclusion is implied.

**Novelty:** Historical priority is unassessed. Recorded correctness and formal checking do not establish novelty; established special cases and methods retain their attribution.

**Separate downstream work (does not reopen this result):** Physical throws remain at most 4 and the routine can continue indefinitely; finite H belongs to the additional constraint graph. The prefix language is not closed under concatenation. Identifying equal physical states must not silently collapse distinct graph vertices. Broader scheduling or compression benefits require separate contracts.

**Proof, review and related source links:**

- [Complete juggling adapter and prefix-series proof](https://github.com/Sodelin/Research-Commons/blob/74ba3079/research/2026-10-05-dot-sequence-reading-editions-0100z/Thue-Morse-Hand-Proofs.md) (proof or status).
- [Historical application map with precise limitations](https://github.com/Sodelin/Research-Commons/blob/74ba3079/research/2026-10-05-dot-sequence-reading-editions-0100z/Prioritized-Thue-Morse-Connections.md) (proof or status).
- [Reading-edition acceptance record and mandatory successor corrections](https://github.com/Sodelin/Research-Commons/blob/74ba3079/research/2026-10-05-dot-sequence-reading-editions-0100z/README.md) (proof or status).

**Connections:**

- [CB-SEQ-004](#cb-seq-004): **proved adapter**. The retained-vertex edge expansion proves H(v)=W(L(v)); it transfers this exact matching observation, not arbitrary graph or juggling properties.

**Stable key:** sequences.CONSTRAINED_JUGGLING_PREFIX_ENUMERATION. **Aliases:** Constrained three-ball Thue–Morse coding; Primitive-loop prefix natural boundary.

</details>


<a id="cb-seq-009"></a>
### A finite pattern reveals its grouping and hidden alignment
**CB-SEQ-009 · Sequences · grouped hierarchy recovery**

**Question:** How long must a raw pattern be before its hidden block scale and grouping become identifiable?

**What we learned:** There are sharp finite window lengths for every fixed grouping parameter and hierarchy level, including exact exceptional small cases.

**What it lets someone do:** Recover a grouping parameter and legal construction phase without being handed the block boundaries.

**What we cannot conclude:** The absolute origin is not recovered, and no single finite window distinguishes every unbounded grouping parameter.

**Kind:** theorem. **Mathematical status:** Proved by hand; acceptance recorded in complete reading edition.

<details>
<summary>Exact scope, prior work, evidence and separate downstream work</summary>

**Exact statement and assumptions.** For n≥1 let u_n be the fixed point starting 0 of tau_n:0→0^n1^n,1→1^n0^n. At known level k≥1, the sharp worst-case raw window length determining its phase modulo (2n)^k is D_n(k)=(2n)^(k−1)(4n^2−n)+1. The least length P_n such that no length-P_n factor of u_n occurs in any u_m with m≠n is P_1=9 and P_n=4n+1 for n≥2. The joint threshold is max(P_n,D_n(k)). The accepted common-factor supplier gives, for s<t, maximum shared factor length C(1,2)=8, C(1,t)=4 for t≥3, C(s,2s)=4s for s≥2, and C(s,t)=3s in the remaining s≥2 cases. These are unknown-occurrence-position observations, not supplied-cut queries.

**Origin.** project posed. A precise source-specific result within the existing sequence programme. Related published problems, constructions and known special cases are credited separately; this grouped card is not a claim to multiple newly solved field questions.

**Prior work.** Recognizability and synchronization have established antecedents, including Durand–Leroy and Klouda–Medkova. These exact grouped-family thresholds do not establish identification of arbitrary written substitution rules; distinct rules can generate the same anchored word.

**Our contribution and attribution.** The October reading edition proves the sharp phase thresholds and parameter/joint corollaries. The common-factor formula is explicitly attributed to its accepted companion review, SHA-256 834eacc2b027a8beef9a42ae27592b1aec3fffd878e7d22b637e41414c6d77bd. That original review body is not reconstructed here.

**Evidence, kept separate:**

- **Hand:** The complete reading edition contains actual mathematical arguments and explicitly records independent AI hand acceptance. Its archival README says not all original separately hashed proof/checker/review files were recovered. This card does not invent those missing receipts or claim a new review.
- **Formal:** No kernel verification of this hand result is claimed. A separately checked inherited recurrence or another sequence theorem does not automatically formalize this consequence.
- **Execution:** The archive reports exact supplementary controls where relevant. They do not replace the uniform hand proof; original computation banks are not reconstructed or rerun here.
- **Empirical:** An exact mathematical statement for the defined graph, symbolic word or arithmetic code. No measured performance, biological data, security, compression or hardware conclusion is implied.

**Novelty:** Historical priority is unassessed. Recorded correctness and formal checking do not establish novelty; established special cases and methods retain their attribution.

**Separate downstream work (does not reopen this result):** The separately hashed original common-factor review remains a source-recovery item, not a newly open theorem. Unique phase is not unique occurrence or absolute origin. For n≥L, all groups have the same length-L inventory of words with at most one change, preventing one finite universal parameter window.

**Proof, review and related source links:**

- [Complete grouped hierarchy recovery and supplier provenance](https://github.com/Sodelin/Research-Commons/blob/74ba3079/research/2026-10-05-dot-sequence-reading-editions-0100z/Pattern-Hierarchies-and-Selected-Digit-Proofs.md) (proof or status).
- [Reading-edition acceptance record and mandatory successor corrections](https://github.com/Sodelin/Research-Commons/blob/74ba3079/research/2026-10-05-dot-sequence-reading-editions-0100z/README.md) (proof or status).

**Connections:**

No theorem-transfer dependency is asserted by this card.

**Stable key:** sequences.GROUPED_PHASE_PARAMETER_IDENTIFICATION. **Aliases:** Grouped whole-motif recovery; Grouped common-factor formula; D_n(k) and P_n thresholds.

</details>


<a id="cb-seq-010"></a>
### Grouped patterns can be richer than ordinary Thue–Morse
**CB-SEQ-010 · Sequences · grouped factor-count comparison**

**Question:** Which grouped substitution produces more distinct short patterns?

**What we learned:** Exact formulas compare all grouping parameters at any fixed length. Ordinary Thue–Morse is not always the richest member of this larger grouped family.

**What it lets someone do:** Perform a complete fixed-scale comparison rather than infer a winner from a finite arbitrary parameter sample.

**What we cannot conclude:** The result does not give a closed formula for the best grouping at every scale or classify all balanced binary substitutions.

**Kind:** theorem. **Mathematical status:** Proved by hand; acceptance recorded in complete reading edition.

<details>
<summary>Exact scope, prior work, evidence and separate downstream work</summary>

**Exact statement and assumptions.** For u_n fixed by 0→0^n1^n,1→1^n0^n and p_n(L) its number of distinct contiguous length-L factors, p_n(0)=1; p_n(L)=2L for 1≤L≤n+1; p_n(L)=4L−2n−2 for n+2≤L≤2n. For L≥2n+1, set k=ceil(L/n), delta=(L−1) mod n; then p_n(L)=(n−delta)P_{2n}(k)+delta P_{2n}(k+1), where P_b counts factors in the established base-b digit-sum-parity word. Its exact all-length formula is supplied and credited in the edition. At fixed L≥1, all n≥L have exactly the factors with at most one change, so n=1,…,L represent every grouped inventory. At L=33, n=3 has 98 distinct factors, while ordinary Thue–Morse has 96.

**Origin.** project posed. A precise source-specific result within the existing sequence programme. Related published problems, constructions and known special cases are credited separately; this grouped card is not a claim to multiple newly solved field questions.

**Prior work.** The chunk companion is the known generalized digit-sum family. Its complexity formulas are credited to Starosta and Peltomäki–Salo; marked-image counting is an established method, including Frid. The contribution does not claim those precursor formulas as new.

**Our contribution and attribution.** The hand proof gives the exact phase-disjoint transfer to the raw grouped word and a finite all-parameter comparison at every fixed scale, including a concrete correction to the idea that ordinary Thue–Morse always maximizes richness.

**Evidence, kept separate:**

- **Hand:** The complete reading edition contains actual mathematical arguments and explicitly records independent AI hand acceptance. Its archival README says not all original separately hashed proof/checker/review files were recovered. This card does not invent those missing receipts or claim a new review.
- **Formal:** No kernel verification of this hand result is claimed. A separately checked inherited recurrence or another sequence theorem does not automatically formalize this consequence.
- **Execution:** The archive reports exact supplementary controls where relevant. They do not replace the uniform hand proof; original computation banks are not reconstructed or rerun here.
- **Empirical:** An exact mathematical statement for the defined graph, symbolic word or arithmetic code. No measured performance, biological data, security, compression or hardware conclusion is implied.

**Novelty:** Historical priority is unassessed. Recorded correctness and formal checking do not establish novelty; established special cases and methods retain their attribution.

**Separate downstream work (does not reopen this result):** No all-L closed maximizing-parameter classification or general balanced-rule census is inferred. The selected-digit family in CB-SEQ-011 is different and may have a different maximizing result without contradiction.

**Proof, review and related source links:**

- [Grouped factor-count formula and complete finite comparison](https://github.com/Sodelin/Research-Commons/blob/74ba3079/research/2026-10-05-dot-sequence-reading-editions-0100z/Pattern-Hierarchies-and-Selected-Digit-Proofs.md) (proof or status).
- [Reading-edition acceptance record and mandatory successor corrections](https://github.com/Sodelin/Research-Commons/blob/74ba3079/research/2026-10-05-dot-sequence-reading-editions-0100z/README.md) (proof or status).

**Connections:**

- [CB-SEQ-009](#cb-seq-009): **same principle**. Uses the same grouped-word family and phase structure, but this card concerns factor counts rather than recovery of an unknown grouping parameter.

**Stable key:** sequences.GROUPED_FACTOR_COMPLEXITY_COMPARISON. **Aliases:** Grouped tau_n factor complexity; L=33 grouped richness comparison.

</details>


<a id="cb-seq-011"></a>
### Selected digit gaps control repetition, branching and distinguishability
**CB-SEQ-011 · Sequences · arbitrary selected binary digits**

**Question:** How does choosing which binary digits to count change an infinite pattern?

**What we learned:** Exact formulas determine its factor counts and strongest repetitions; a complete branching-pattern classification explains the changes, and the full count function identifies the chosen digit positions.

**What it lets someone do:** Specify a digit-selection rule and derive its combinatorial behavior, including the exact scale at which two choices become distinguishable.

**What we cannot conclude:** This is not a classification of every automatic or balanced-substitution sequence, and arbitrary noncomputable selections do not become algorithms.

**Kind:** theorem. **Mathematical status:** Proved by hand; acceptance recorded in complete reading edition.

<details>
<summary>Exact scope, prior work, evidence and separate downstream work</summary>

**Exact statement and assumptions.** Let S={0=s_0<s_1<…} be any infinite set of binary positions and x_S(r) the XOR of r's bits in S. Put A_i=2^(s_i), A_0=1. Its complexity satisfies p_S(0)=1; p_S(L)=2L for 1≤L≤A_1+1; for i≥1, p_S(L)=4L−2(A_i−A_{i−1}+2) on A_i+2≤L≤2A_i−A_{i−1}+1, and p_S(L)=2L+2(A_i−1) on 2A_i−A_{i−1}+2≤L≤A_{i+1}+1. These ranges cover all positive L; differences at L≥2 are 2 or 4. The exact critical exponent is sup_{i≥1}2^(s_i−s_{i−1}), including infinity. Every nonempty bispecial factor has the edition's unique desubstitution description as an alternating-word image, with full extension classification; strong lengths are 2^(s_{i+1}), weak lengths 2^(s_{i+1}+1)−2^(s_i). For L≥1, 2L≤p_S(L)≤p_TM(L). If S,T first differ in membership at position r≥1, their first differing count is at L=2^r+2, differing by 2, so the full complexity function determines S. For finite mask m with S_m={p:p AND m=0}, E=2^(m+1); masks first differing in bit r first differ in count at L=2^(2^r)+2.

**Origin.** project posed. A precise source-specific result within the existing sequence programme. Related published problems, constructions and known special cases are credited separately; this grouped card is not a claim to multiple newly solved field questions.

**Prior work.** Cloitre v2 already gives effective all-level factor-complexity recurrence and finite seeds, so this must not be advertised as solving an untouched v1 open question. Here mask m equals v2 iterate m+1. Equally spaced selections and their complexity/exponent special cases are established in generalized digit-sum work by Starosta, Peltomäki–Salo and Blondin-Massé–Brlek–Glen–Labbé. Cassaigne/Klouda special-factor methods are antecedents.

**Our contribution and attribution.** The October collection supplies explicit seed-free arbitrary-infinite-selection formulas, a repetition theorem allowing varying gaps, a complete bispecial/extension classification, and comparison/identifiability corollaries. This is one grouped source programme, not a count of separately novel discoveries.

**Evidence, kept separate:**

- **Hand:** The complete reading edition contains actual mathematical arguments and explicitly records independent AI hand acceptance. Its archival README says not all original separately hashed proof/checker/review files were recovered. This card does not invent those missing receipts or claim a new review.
- **Formal:** No kernel verification of this hand result is claimed. A separately checked inherited recurrence or another sequence theorem does not automatically formalize this consequence.
- **Execution:** The archive reports exact supplementary controls where relevant. They do not replace the uniform hand proof; original computation banks are not reconstructed or rerun here.
- **Empirical:** An exact mathematical statement for the defined graph, symbolic word or arithmetic code. No measured performance, biological data, security, compression or hardware conclusion is implied.

**Novelty:** Historical priority is unassessed. Recorded correctness and formal checking do not establish novelty; established special cases and methods retain their attribution.

**Separate downstream work (does not reopen this result):** Historical priority of the arbitrary-S formulation remains unassessed. The formula is symbolic for noncomputable S; finite-mask evaluation has an integer-operation bound, not a general computability miracle. Unique canonical bispecial description is not unique occurrence. A single factor count does not identify a factor language, and this family differs from grouped tau_n.

**Proof, review and related source links:**

- [Complete complexity, exponent, bispecial and comparison proofs with prior correction](https://github.com/Sodelin/Research-Commons/blob/74ba3079/research/2026-10-05-dot-sequence-reading-editions-0100z/Pattern-Hierarchies-and-Selected-Digit-Proofs.md) (proof or status).
- [Reading-edition acceptance record and mandatory successor corrections](https://github.com/Sodelin/Research-Commons/blob/74ba3079/research/2026-10-05-dot-sequence-reading-editions-0100z/README.md) (proof or status).
- [Cloitre's explicitly identified revised source](https://arxiv.org/abs/2604.06243v2) (proof or status).

**Connections:**

- [CB-SEQ-010](#cb-seq-010): **same principle**. Both compare factor complexity, but their families differ: Thue–Morse is maximal within the selected-digit family, not within all grouped tau_n words.

**Stable key:** sequences.SELECTED_DIGIT_COMPLETE_INVARIANTS. **Aliases:** Selected-bit mask family; Arbitrary selected-digit complexity; Gap critical exponent; Bispecial-factor classification; Selected-set identifiability.

</details>


<a id="cb-seq-012"></a>
### Every finite prefix can exist without one positive infinite realization
**CB-SEQ-012 · Sequences · structured Collatz valuation codes**

**Question:** Can one positive Collatz start follow a fixed Thue–Morse arrangement of valuation blocks forever?

**What we learned:** Only if that same start lies on a cycle. In two specified growing code families, even that exception is impossible, although every finite prefix remains positively realizable.

**What it lets someone do:** Exclude a concrete infinite-code construction using its repetition structure rather than an arbitrary computation cutoff.

**What we cannot conclude:** This does not prove Collatz, exclude arbitrary aperiodic valuation codes, or rule out every nontrivial positive cycle.

**Kind:** theorem. **Mathematical status:** Proved by hand; named Lean components checked.

<details>
<summary>Exact scope, prior work, evidence and separate downstream work</summary>

**Exact statement and assumptions.** Use the fully accelerated odd map U(n)=(3n+1)/2^(v_2(3n+1)) on positive odd integers. Let t be ordinary binary Thue–Morse starting 0 and let B_0,B_1 be any fixed nonempty finite words of positive integer valuations. If B_{t_0}B_{t_1}… is the exact valuation sequence of one positive odd N, then U^j(N)=N for some j>0. No equal-codeword-length or average-valuation hypothesis is assumed. The special code B_0=(1),B_1=(2), and every fixed pair B_0=1^p3,B_1=1^q3 with p,q≥3, admit no positive realization because their selected returns strictly grow. The cycle exception is essential: B_0=B_1=(2),N=1 realizes the general premise. Equal length-2d valuation prefixes returning at accelerated time 3d with distinct states require 2·32^d<27^d(N+1); balanced Thue–Morse returns provide unbounded d. The full theorem is analytic, with narrower formal collision/numerical components.

**Origin.** project posed. A precise source-specific result within the existing sequence programme. Related published problems, constructions and known special cases are credited separately; this grouped card is not a claim to multiple newly solved field questions.

**Prior work.** Finite valuation/parity congruences, affine cycle arithmetic and finite-word realizability are classical. The public archive makes no certified novelty claim for the complete fixed-morphism statement. Rational-base 3/2 Thue–Morse is a different sequence; an unrecovered rational-input continuation or prior-work correction is not silently substituted for this source.

**Our contribution and attribution.** The existing September source and coordinating review reconstruct the full fixed-word coding, same-start size/congruence contradiction and exact cycle-exclusion subclasses. This resolves the older specific 2-adic anchor's positive-membership gate negatively, not the general Collatz problem.

**Evidence, kept separate:**

- **Hand:** The public MODERN_CONTRIBUTIONS review reconstructs the complete accelerated-word collision, balanced-prefix and cycle-exclusion argument. This card recovers that scoped coordinating review; it is not a fresh independent review.
- **Formal:** Archived PrefixCollision and AffineRepetition modules check narrower actual-shortcut and numerical components. The full odd-word/acceleration bridge, height estimate and Thue–Morse coding theorem remain analytic, not an end-to-end Lean proof.
- **Execution:** The archive records finite indexing/valuation controls and narrow formal checks. Finite controls are supplemental, not the proof of the infinite theorem; none were rerun.
- **Empirical:** An exact mathematical statement for the defined graph, symbolic word or arithmetic code. No measured performance, biological data, security, compression or hardware conclusion is implied.

**Novelty:** Historical priority is unassessed. Recorded correctness and formal checking do not establish novelty; established special cases and methods retain their attribution.

**Separate downstream work (does not reopen this result):** Do not relabel the superseded anchor's positive-membership problem as unresolved. Conversely, no universal orbit coverage, rational-input extension, arbitrary morphism realization theorem beyond the stated fixed binary encoding, or end-to-end Lean acceptance follows. The p,q here are valuation-block lengths, not the unrelated generalized binary-substitution parameters.

**Proof, review and related source links:**

- [Complete fixed Thue–Morse valuation proof](https://github.com/Sodelin/Collatz-Conjecture-Work/blob/026aa4ad4be6453a005ab950b160a9f2204c5271/proof-search/disproof/TM_Prefix_Return_Exclusion_2026-09-05.md) (proof or status).
- [Actual-body coordinating reconstruction and formal boundary](https://github.com/Sodelin/Collatz-Conjecture-Work/blob/026aa4ad4be6453a005ab950b160a9f2204c5271/research-review/consolidation-2026-09-05/MODERN_CONTRIBUTIONS.md) (hand review).
- [Original claim manifest](https://github.com/Sodelin/Collatz-Conjecture-Work/blob/026aa4ad4be6453a005ab950b160a9f2204c5271/publication/claims.json) (proof or status).
- [Exact archived verification scope](https://github.com/Sodelin/Collatz-Conjecture-Work/blob/026aa4ad4be6453a005ab950b160a9f2204c5271/verification/Blind_Recurrence_Verification_2026-09-05.md) (formal receipt).

**Connections:**

- [CB-SEQ-006](#cb-seq-006): **same principle**. Both expose a finite-prefix/infinite-realization gap, in different graph/arithmetic models; neither theorem is used as a proof supplier of the other.

**Stable key:** sequences.COLLATZ_FIXED_TM_VALUATION_OBSTRUCTION. **Aliases:** F-TM-POSITIVE-EXCLUSION-001; Fixed nonerasing Thue–Morse valuation morphisms.

</details>

<a id="cb-feedback-001"></a>
### Recurring reproductive links determine an ancestry property under explicit mixing
**CB-FEEDBACK-001 · Feedback models · recurrent ancestry**

**Question:** When do recurring links between reproductive communities determine long-run ancestry?

**What we learned:** Under strong local mixing and no lineage extinction, an infinite group has the identical-ancestors property (IAP) exactly when all but finitely many members lie in one recurrent strongly connected component.

**What it lets someone do:** Classify the stated ancestry property and construct connected, ancestry-convex component tails without confusing recurring contact with a measured species boundary.

**What we cannot conclude:** The mixing premise is substantial and is not almost surely satisfied by ordinary finite Wright–Fisher reproduction. This does not identify empirical species or maximal clusters.

**Kind:** theorem. **Mathematical status:** Proved by hand; named historical Lean scope checked.

<details>
<summary>Exact scope, prior work, evidence and separate downstream work</summary>

**Exact statement and assumptions.** A finite nonempty deme set, organisms indexed by natural numbers with a separate generation map, finite generation prefixes, occupied cohorts in every deme, one-generation parent edges, same-deme parent coverage, and one uniform positive finite lag giving complete within-deme dissemination from every organism are assumed. Ancestry means a nonempty parent path. The identical-ancestors property (IAP, the source's identical-ancestor-point axiom) says that each member of a set has either finitely many descendants or finitely many non-descendants within that set. For every infinite subset, IAP holds iff it is contained modulo finitely many members in one recurrent strongly connected component; that component is unique. Sparse subsets are allowed: this is not equality with the whole component. Whole-history IAP is equivalent to recurrent strong connectivity. A common-cutoff component tail is infinite, connected, ancestrally convex and reflecting. Concrete one-way and bidirectional examples and uniqueness are included.

**Origin.** project posed. A declared source-specific question within the feedback/ancestry programme. Motivation by prior biology and ancestry literature does not establish that this exact statement was a published open problem.

**Prior work.** Alexander's strict-ancestry and specieslike-cluster predicates, structured-pedigree ancestry mixing, and temporal recurrence/reachability are antecedents. The manuscript explicitly presents a newly posed application question, not an established Alexander conjecture with this wording.

**Our contribution and attribution.** The existing package supplies the exact recurrent-component subset classification and its formal interface, not a universal biological theory. This card restores its already completed status.

**Evidence, kept separate:**

- **Hand:** The completed manuscript and internal AI review were recovered; this indexing pass read the actual arguments and source but does not assert a new independent whole-proof acceptance.
- **Formal:** Selected endpoints in AncestryMixing and AncestryExamples have the archived exit-0 receipt and standard-axiom reports. The five-new-module aggregate records 10 reports for AncestryMixing and 6 for AncestryExamples; auxiliary written extensions are not thereby formalized.
- **Execution:** The 25 September 2026 aggregate local receipt records Lean 4.33.1 with Mathlib 0df444a360eaa60ab8c11dca51a86af692955474 and exit-0 compilation of seven custom modules using cached upstream dependencies. Its 72 selected reports include 53 in five new modules and 19 in two unchanged dependencies, not 72 new discoveries. The saved receipt and selected logs were read; no rerun, clean-machine reconstruction or new hosted-CI check occurred.
- **Empirical:** A theorem about the explicitly defined mathematical population model. No empirical speciation, biological species identification or measured gene-culture mechanism is established.

**Novelty:** Unresolved. This is recovery of existing completed work, not a new theorem or historical-priority claim; established source models and methods retain their attribution.

**Separate downstream work (does not reopen this result):** The conditional Borel–Cantelli adapter and nonuniform per-organism lag sharpening are written but not checked generalized interfaces. Ordinary independent two-parent Wright–Fisher reproduction with population size at least two does not satisfy the theorem's universal no-extinction/dissemination premise almost surely. No finite-data classifier, maximality theorem or empirical-species conclusion follows. B02/B03 frequency recursions do not automatically instantiate this pedigree.

**Proof, review and related source links:**

- [Completed manuscript and exact ancestry assumptions](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/feedback-speciation/MANUSCRIPT.md) (proof or status).
- [Actual recurrent-component proof source](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/feedback-speciation/package/AncestryMixing.lean) (proof or status).
- [Uniqueness and concrete examples](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/feedback-speciation/package/AncestryExamples.lean) (proof or status).
- [Internal review and corrections](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/feedback-speciation/REVIEW-NOTES.md) (hand review).
- [Historical aggregate receipt](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/feedback-speciation/package/verification/receipt.json) (formal receipt).
- [Build and dependency boundaries](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/feedback-speciation/VERIFICATION.md) (formal receipt).

**Connections:**

- [CB-FEEDBACK-005](#cb-feedback-005): **same principle**. Both discuss the identical-ancestors property, but the later actual-law result uses an extinction-permitting synchronization bridge rather than this theorem's no-extinction premise.

**Stable key:** september.FEEDBACK.RECURRENT_ANCESTRY_COMPONENTS. **Aliases:** Samuel B01; AncestryMixing; AncestryExamples.

</details>


<a id="cb-feedback-002"></a>
### Stable cultural differences can coexist with neutral-marker homogenization
**CB-FEEDBACK-002 · Feedback models · culture and neutral exchange**

**Question:** Does persistent cultural difference necessarily preserve a neutral genetic difference?

**What we learned:** No. The stated majority-of-three cultural dynamics can remain polarized while a positively bounded residual exchange makes the neutral-marker difference decay geometrically.

**What it lets someone do:** Separate persistence of one type of difference from persistence of another in a fully specified coupled recurrence.

**What we cannot conclude:** This is one-way cultural control of exchange, not a reciprocal gene-culture or epigenetic model, an ancestry theorem or evidence of empirical speciation.

**Kind:** theorem. **Mathematical status:** Proved by hand; named historical Lean scope checked.

<details>
<summary>Exact scope, prior work, evidence and separate downstream work</summary>

**Exact statement and assumptions.** Use F(x)=3x²−2x³ and the declared symmetric two-coordinate mixture. For 0<m<1/8 and supplied 0<d<1 satisfying (1−2m)d²=1−6m, the polarized point ((1+d)/2,(1−d)/2) is locally asymptotically stable in the full two-dimensional system. The checked rational witness m=7/78,d=3/4 gives (7/8,1/8). Along the actual cultural trajectory, let rho_t=g/(1+k(x_t−y_t)²), with 0<g≤1/2, k≥0, and cultural/neutral initial frequencies in their valid intervals. Writing a=g/(1+k)>0, the neutral frequencies obey |u_t−v_t|≤(1−2a)^t|u_0−v_0|→0. The coupling goes from culture to exchange only.

**Origin.** project posed. A declared source-specific question within the feedback/ancestry programme. Motivation by prior biology and ancestry literature does not establish that this exact statement was a published open problem.

**Prior work.** Majority/conformist maps, linear stability and uniform contraction are established methods. The package presents a self-contained boundary example; it does not attribute every helper to a new discovery.

**Our contribution and attribution.** The existing completed argument joins full-neighborhood stability and a trajectory-faithful neutral contraction, showing precisely why cultural persistence alone does not imply neutral separation.

**Evidence, kept separate:**

- **Hand:** Completed written argument and internal AI review are recovered, not newly derived. The full source body was read in this recovery.
- **Formal:** The historical aggregate includes 19 selected FeedbackDynamics reports with only the recorded standard logical axioms. The rational witness and stated stability/contraction endpoints are covered; the generalized existence and biological-source bridges are not.
- **Execution:** The 25 September 2026 aggregate local receipt records Lean 4.33.1 with Mathlib 0df444a360eaa60ab8c11dca51a86af692955474 and exit-0 compilation of seven custom modules using cached upstream dependencies. Its 72 selected reports include 53 in five new modules and 19 in two unchanged dependencies, not 72 new discoveries. The saved receipt and selected logs were read; no rerun, clean-machine reconstruction or new hosted-CI check occurred.
- **Empirical:** A theorem about the explicitly defined mathematical population model. No empirical speciation, biological species identification or measured gene-culture mechanism is established.

**Novelty:** Unresolved. This is recovery of existing completed work, not a new theorem or historical-priority claim; established source models and methods retain their attribution.

**Separate downstream work (does not reopen this result):** The 1/6 existence/restricted-mode threshold must not replace the 1/8 full-stability condition. General square-root existence is a written step, not a checked endpoint. No reciprocal dynamics, epigenetic variable, source-faithful pedigree instantiation or empirical conclusion is supplied.

**Proof, review and related source links:**

- [Completed manuscript, dynamics section](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/feedback-speciation/MANUSCRIPT.md) (proof or status).
- [Actual coupled recurrence and stability proof](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/feedback-speciation/package/FeedbackDynamics.lean) (proof or status).
- [Internal review](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/feedback-speciation/REVIEW-NOTES.md) (hand review).
- [Historical aggregate receipt](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/feedback-speciation/package/verification/receipt.json) (formal receipt).

**Connections:**

- [CB-FEEDBACK-001](#cb-feedback-001): **same principle**. Both separate phenotype/frequency patterns from ancestry conclusions; this frequency model is not a proved instantiation of the recurrent-pedigree theorem.

**Stable key:** september.FEEDBACK.CULTURAL_POLARIZATION_NEUTRAL_HOMOGENIZATION. **Aliases:** Samuel B02; FeedbackDynamics.

</details>


<a id="cb-feedback-003"></a>
### Positive selection defeats arbitrary admitted affinity changes in one source recursion
**CB-FEEDBACK-003 · Feedback models · affinity and cultural fixation**

**Question:** Can changing affinities indefinitely prevent fixation under constant positive selection in the specified model?

**What we learned:** Not when the initial favored-type odds bound holds. A quantitative bound shrinks at every generation, even for arbitrary admissible affinity sequences.

**What it lets someone do:** Obtain an explicit uniform decay rate for the unfavored cultural frequency along the actual source recursion.

**What we cannot conclude:** This does not prove genetic fixation, exact finite-time fixation, finite-population behavior or a theorem for every cultural-transmission model.

**Kind:** theorem. **Mathematical status:** Proved by hand; named historical Lean scope checked.

<details>
<summary>Exact scope, prior work, evidence and separate downstream work</summary>

**Exact statement and assumptions.** For the declared Fogarty–Zhang–Feldman affinity-bias transmission/selection recursion, let AB,Ab,aB,ab frequencies x1,x2,x3,x4 be nonnegative and sum to one. Selection is one fixed s>0 and the two affinity sequences b1(n),b2(n) lie in [0,1] at every generation. Assume an initial r≥0 with x2≤r x1 and x4≤r x3. With r_n=r/(1+s)^n, both odds inequalities persist and the favored cultural B frequency q_n=x1_n+x3_n satisfies 0≤1−q_n≤r_n/(1+r_n)≤r_n, hence q_n→1. Positive x1,x3 suffice to construct r=max(x2/x1,x4/x3); x2,x4 may vanish. The theorem concerns the actually recursively defined evolve/model sequence, not a sequence assumed to satisfy the desired invariant. A separate exclusion rules out polymorphic fixed points with interior genetic and cultural marginals, including permitted simplex-boundary frequency vectors.

**Origin.** project posed. A declared source-specific question within the feedback/ancestry programme. Motivation by prior biology and ancestry literature does not establish that this exact statement was a published open problem.

**Prior work.** The source equations are those of Fogarty–Zhang–Feldman, DOI 10.1016/j.tpb.2025.08.003. Order preservation and odds contraction are established mathematics. The package's exact model attribution is preserved; another published transmission model is not silently substituted.

**Our contribution and attribution.** The existing package proves the source-specific fixed-point exclusion and a global quantitative fixation extension allowing arbitrary admissible affinity sequences. This is recovery, not a fresh proof or priority certification.

**Evidence, kept separate:**

- **Hand:** The complete rate proof and independent internal AI statement review were read. Their source-model restrictions and corrected boundary cases remain explicit.
- **Formal:** The historical aggregate records 9 selected reports in FogartyAffinity and 9 in FogartyAffinityFixation, with only standard logical axioms. The sharper deficit bound is a join of checked lemmas; the final model endpoint packages the weaker rate and convergence.
- **Execution:** The 25 September 2026 aggregate local receipt records Lean 4.33.1 with Mathlib 0df444a360eaa60ab8c11dca51a86af692955474 and exit-0 compilation of seven custom modules using cached upstream dependencies. Its 72 selected reports include 53 in five new modules and 19 in two unchanged dependencies, not 72 new discoveries. The saved receipt and selected logs were read; no rerun, clean-machine reconstruction or new hosted-CI check occurred.
- **Empirical:** A theorem about the explicitly defined mathematical population model. No empirical speciation, biological species identification or measured gene-culture mechanism is established.

**Novelty:** Unresolved. This is recovery of existing completed work, not a new theorem or historical-priority claim; established source models and methods retain their attribution.

**Separate downstream work (does not reopen this result):** Uniformity retains the given initial odds bound and fixed positive s; it is not uniform as s tends to zero or r grows unbounded. Realized affinity sequences may be arbitrary/adaptively chosen, but no additional stochastic measurability theorem is claimed. No genetic-A fixation, finite-time exact attainment, finite-population extension or empirical-species identification follows.

**Proof, review and related source links:**

- [Complete quantitative proof](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/feedback-speciation/FOGARTY-GLOBAL-RATE.md) (proof or status).
- [Original source recursions and fixed-point exclusion](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/feedback-speciation/package/FogartyAffinity.lean) (proof or status).
- [Actual evolution and fixation source](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/feedback-speciation/package/FogartyAffinityFixation.lean) (proof or status).
- [Independent internal statement review](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/feedback-speciation/rate-statement-review.md) (hand review).
- [Source attribution and model distinction](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/feedback-speciation/SOURCE-ORIGINS.md) (proof or status).
- [Historical aggregate receipt](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/feedback-speciation/package/verification/receipt.json) (formal receipt).

**Stable key:** september.FEEDBACK.FOGARTY_AFFINITY_FIXATION. **Aliases:** Samuel B03; FogartyAffinity; FogartyAffinityFixation.

</details>


<a id="cb-feedback-004"></a>
### Finite sampling reverses a matched deterministic marker-barrier ranking
**CB-FEEDBACK-004 · Feedback models · finite and deterministic comparison**

**Question:** Can finite population sampling reverse which of two mechanisms appears to make a stronger marker barrier?

**What we learned:** Yes, in the stated exact two-deme example: pure induction has the larger finite-population barrier, while the matched deterministic genetic model has the larger barrier.

**What it lets someone do:** Use a fully specified counterexample to avoid transferring an ordering from deterministic dynamics to one finite sampling model.

**What we cannot conclude:** This is not a universal epigenetic advantage, a population-size monotonicity theorem or an empirical claim. The migration and pulse conventions are essential.

**Kind:** theorem. **Mathematical status:** Proved by hand; historical Lean components checked with stated receipt limit.

<details>
<summary>Exact scope, prior work, evidence and separate downstream work</summary>

**Exact statement and assumptions.** There is one diploid adult per deme. Migration uses deterministic weighted pools with m=1/4, not integer migrant exchange. Additive divergent selection has s=1/2, recombination r=1/2, independent gamete and offspring draws allow selfing, and the comparison is genetic mu=0 versus pure reset mu=1/2,phi=1 after mating. Both use the EEbb/eebb secondary-contact state and a one-direction migrant marker pulse before selection; the normalization is preselection B0=m/2=1/8. For the finite kernel, RI_gen=937945083/2233177303<RI_epi=3/7, with exact difference 19130904/2233177303; the pulse-start finite marginal error is at most (99/100)^n. In the matched deterministic recurrence every biological generation at least four has genetic RI at least 1027087570805/2255346713174>3/7. Its separately proved common limit retains that ordering, while pure induction has common marker mean 1/14 and RI=3/7. Reduced deterministic index zero means biological generation one. Marker terminal classes need not be singleton full genotype states.

**Origin.** project posed. A declared source-specific question within the feedback/ancestry programme. Motivation by prior biology and ancestry literature does not establish that this exact statement was a published open problem.

**Prior work.** Classical finite-chain harmonic/absorption arguments and the published reset benchmark are reused. The later Commons finite-population packet uses N≥2 diploids and an exact integer exchanged count 1≤k<N, so it is a related different contract, not a duplicate or direct all-N generalization of the weighted-pool N=1 kernel.

**Our contribution and attribution.** The already completed written and formally supported package gives an exact strict finite-versus-deterministic reversal under the same stated preparation and statistic, rather than only a larger finite-population effect.

**Evidence, kept separate:**

- **Hand:** Complete written source correspondence, common-limit argument and independent internal exact-arithmetic audits were recovered. This indexing pass read the actual bodies and receipts, not a new full-proof review.
- **Formal:** The combined receipt covers 34 selected reports: 11 FiniteFixation, 10 FiniteEpigenetic, 10 DeterministicEpigenetic and 3 RankingReversal. It checks the explicit count kernel, finite limits, reduced finite-tail ordering and joined reversal. Deterministic common-limit existence and full source transport remain written/reviewed, not formally proved in these modules.
- **Execution:** FiniteFixation, FiniteEpigenetic and RankingReversal have recorded exit-0 builds. The original DeterministicEpigenetic process exit is null/unretrieved; its complete standard-axiom log and compiled object were recovered, and the later RankingReversal module imported that object and exited zero. The source labels this PASS_WITH_RECOVERED_EXIT_EVIDENCE. All four saved logs were read; no new build or scientific execution occurred.
- **Empirical:** A theorem about the explicitly defined mathematical population model. No empirical speciation, biological species identification or measured gene-culture mechanism is established.

**Novelty:** Unresolved. This is recovery of existing completed work, not a new theorem or historical-priority claim; established source models and methods retain their attribution.

**Separate downstream work (does not reopen this result):** Deterministic common-limit existence and the full phase/source-to-count-model correspondence have written proof and scoped review but are outside the Lean modules. The formal limiting statement assumes convergence; the unconditional finite-tail ordering does not. The original deterministic compiler-process exit was not retrieved: complete log/object plus a later successful importing module are evidence, not an observed exit-0 for that process. Long decimal approximations are not certified enclosures. No universal population-size trend or empirical speciation claim follows.

**Proof, review and related source links:**

- [Exact finite result and model contract](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/feedback-speciation/finite-epigenetic/FINITE-RESULT.md) (proof or status).
- [Complete deterministic comparison and common-limit argument](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/feedback-speciation/finite-epigenetic/DETERMINISTIC-COMPARISON.md) (proof or status).
- [Independent finite-model audit](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/feedback-speciation/finite-epigenetic/INDEPENDENT-MODEL-AUDIT.md) (hand review).
- [Independent deterministic audit](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/feedback-speciation/finite-epigenetic/DETERMINISTIC-INDEPENDENT-AUDIT.md) (hand review).
- [Joined ranking-reversal Lean source](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/feedback-speciation/finite-epigenetic/RankingReversal.lean) (proof or status).
- [Combined receipt with recovered-exit boundary](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/feedback-speciation/finite-epigenetic/verification/combined-receipt.json) (formal receipt).
- [Related Commons fixed-count N≥2 result, different source contract](https://github.com/Sodelin/Research-Commons/blob/27b143c73a4ac272b560b2974d83ff96df738531/research/2026-09-30-stepchange-scope/PROOF.md) (proof or status).

**Stable key:** september.FEEDBACK.FINITE_DETERMINISTIC_RANKING_REVERSAL. **Aliases:** Samuel B04; FiniteEpigenetic; DeterministicEpigenetic; RankingReversal.

</details>


<a id="cb-feedback-005"></a>
### One shared random process joins a marker barrier to almost-sure ancestry mixing
**CB-FEEDBACK-005 · Feedback models · same-draw marker and parent process**

**Question:** Can a positive marker-barrier statistic coexist with the identical-ancestors property in the very same population process?

**What we learned:** Yes, for the explicitly constructed process. The same random draws produce both the marker path and parent graph, whose whole-history identical-ancestors property (IAP) holds almost surely.

**What it lets someone do:** Connect the declared marker calculation to an actual ancestry process, instead of choosing an unrelated graph or leaving the infinite-process connection pending.

**What we cannot conclude:** This does not equate the statistic with a separately constructed infinite-stream marker-fixation event, cover other genetic regimes or establish an empirical species boundary.

**Kind:** theorem. **Mathematical status:** Proved by hand; named historical Lean scope checked.

<details>
<summary>Exact scope, prior work, evidence and separate downstream work</summary>

**Exact statement and assumptions.** There are two adults per generation, one per deme, with two parent slots per child and selfing allowed. Four independent uniform Fin14 draws per generation are reused for both parental identity and marker homologue; local parent probability is 6/7, foreign 1/7 and homologue probability 1/2. The pure selected-state induction model has a transition-zero marker pulse followed by ordinary inheritance. The completed bounded R1–R6 theorem proves raw/compressed-record transport, all 81 ordinary and nine pulse marginal identities and off-support closure, a measurable count/parent process, and every finite-path frozen-kernel product law. The designated parent-table mass is 36/2401. For an organism born strictly before the chosen future starting generation and k future generations, non-resolution probability is at most (2365/2401)^k, also conditional on any positive-mass complete earlier raw-history event. Whole-history identical-ancestors property (IAP) holds almost surely: each member has finitely many descendants or finitely many non-descendants within that history. The frozen-kernel RI=3/7, finite-path realization and actual-law IAP are conjoined. Exact avoidance probability and non-resolution bound are not equality of events, and marker counts are not independent across generations.

**Origin.** project posed. A declared source-specific question within the feedback/ancestry programme. Motivation by prior biology and ancestry literature does not establish that this exact statement was a published open problem.

**Prior work.** Classical product probability, recurrence of a positive-probability symbol, and extinction-or-spread synchronization are reused. This actual-law proof permits extinction and does not derive its premise from the no-extinction recurrent-component theorem.

**Our contribution and attribution.** The existing B06 completion supplies the same-draw infinite process, measurable finite-path realization and almost-sure ancestry conclusion. B05's finite precursor is retained within this one group; its old uncompiled/R1–R6 pending list is superseded, not a current missing proof.

**Evidence, kept separate:**

- **Hand:** The corrected independent internal semantic review passes the bounded R1–R6 theorem after resolving the earlier measurability and R6-overclaim issues. The completed statement and actual source bodies were read, not rederived here.
- **Formal:** The 25 September 2026 B06 receipt records 36 selected standard-axiom reports across four newly compiled modules: 10 R1R2, 8 Noise, 7 Paths and 11 Ancestry. Earlier custom objects were reused. B05 separately has four checked finite endpoints; these are retained precursor evidence, not forty discoveries.
- **Execution:** All four new B06 modules have recorded exit-zero local builds under the pinned Lean 4.33.1 environment, with saved logs read here. Thirteen custom sources are shipped but a fresh complete replay of all thirteen is not claimed. No new compiler or scientific execution occurred.
- **Empirical:** A theorem about the explicitly defined mathematical population model. No empirical speciation, biological species identification or measured gene-culture mechanism is established.

**Novelty:** Unresolved. This is recovery of existing completed work, not a new theorem or historical-priority claim; established source models and methods retain their attribution.

**Separate downstream work (does not reopen this result):** The source explicitly excludes a separately defined infinite-stream eventual-marker-fixation event identified with fixationValue; that excluded strengthening does not reopen the completed actual-law IAP result. No adaptive genetic regime or empirical species classification follows. A fresh complete 13-custom-module replay/hosted build is not supplied by the four-new-module receipt.

**Proof, review and related source links:**

- [Completed R1–R6 statement and exact exclusions](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/feedback-speciation/pure-induction-ancestry-v2/RESULT-AND-SCOPE.md) (proof or status).
- [Final same-law ancestry theorem](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/feedback-speciation/pure-induction-ancestry-v2/PureInductionAncestry.lean) (proof or status).
- [Paths and measurability](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/feedback-speciation/pure-induction-ancestry-v2/PureInductionPaths.lean) (proof or status).
- [Raw-record and marginal transport](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/feedback-speciation/pure-induction-ancestry-v2/PureInductionR1R2.lean) (proof or status).
- [Actual probability law](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/feedback-speciation/pure-induction-ancestry-v2/PureInductionNoise.lean) (proof or status).
- [Corrected independent internal semantic review](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/feedback-speciation/pure-induction-ancestry-v2/INDEPENDENT-REVIEW.json) (hand review).
- [Historical B06 combined receipt](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/feedback-speciation/pure-induction-ancestry-v2/COMBINED-RECEIPT.json) (formal receipt).
- [Preserved B05 precursor and superseded pending list](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/feedback-speciation/pure-induction-finite/README.md) (proof or status).
- [Historical B05 finite receipt](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/feedback-speciation/pure-induction-finite/verification/worker-receipt.json) (formal receipt).

**Connections:**

- [CB-FEEDBACK-004](#cb-feedback-004): **reused theorem**. Reuses the checked finite marker kernel and frozen RI=3/7 statistic, then proves its same-draw count/parent realization; does not reuse the deterministic common-limit argument.
- [CB-FEEDBACK-001](#cb-feedback-001): **same principle**. Both concern the identical-ancestors property, but this actual-law proof uses extinction-permitting synchronization, not B01's no-extinction premise.

**Stable key:** september.FEEDBACK.SAME_DRAW_MARKER_ANCESTRY. **Aliases:** Samuel B05 precursor; Samuel B06 completion; PureInductionAncestry R1–R6.

</details>

<a id="cb-genome-001"></a>
### A finite ancestry graph does not determine its infinite population's specieslike status
**CB-GENOME-001 · Genome ancestry · infinite-completion limits**

**Question:** Does a finite genome-ancestry graph determine whether its whole infinite completion is specieslike?

**What we learned:** No. Every admitted finite graph has two compatible infinite completions with opposite answers, despite preserving all its old edges and ancestry paths.

**What it lets someone do:** Identify which assumptions about admissible futures are needed before finite ancestry evidence can justify a future-inclusive conclusion.

**What we cannot conclude:** This is not a universal impossibility theorem for DNA inference or biological species identification.

**Kind:** counterexample. **Mathematical status:** Proved; archived Lean check recorded.

<details>
<summary>Exact scope, prior work, evidence and separate downstream work</summary>

**Exact statement and assumptions.** Every finite Wong-model gARG embeds injectively in two connected infinite graph completions preserving and reflecting all old edges and ancestry paths. Both meet the declared date/local-finiteness/root conditions; one whole population is inspecies and maximal specieslike, while the other fails IAP. Here IAP means that each member has finitely many descendants or finitely many non-descendants within the stated set. Therefore no verdict based only on the finite graph is correct for every such completion. Abstract topology completions, not extension of future interval annotations, a genome-to-organism owner map, equal DNA probability laws, or a universal species-inference impossibility.

**Origin.** project posed. The 25 September 2026 genomic-identification note extracts a source-faithful consequence of the existing finite-history completion construction. It is not a claimed author-designated external open problem.

**Prior work.** 25 September 2026 note; elementary decoder corollary of the existing completion theorem, using Wong's representation and Alexander's predicates; no independent novelty claimed.

**Our contribution and attribution.** The existing Samuel package connects every actual finite gARG to explicit opposite infinite graph completions and extracts the exact no-verdict consequence. The elementary inverse-map obstruction is not claimed as a new general principle.

**Evidence, kept separate:**

- **Hand:** The original completion and corollary sources, source-bound scope note and archived endpoint receipt were read. No fresh whole-import mathematical audit or human/external peer review is claimed.
- **Formal:** Archived local Lean 4.33.1 verification.json records exit code zero and the three named FiniteGenomeIdentifiability endpoints with only propext, Classical.choice and Quot.sound. The imported WongAlexander completion supplier is separately preserved at its recorded source pin. This recovery read the corollary and supplier bodies but did not rerun their transitive closure.
- **Execution:** Historical compiler and selected-axiom evidence is linked, with exact source and receipt pins. No build, finite-control rerun or scientific execution occurred during this recovery; no universal native refinement is claimed.
- **Empirical:** A theorem about specified observations and mathematical models, not measured genetic data, a validated species classifier or an experimentally established inheritance law.

**Novelty:** No independent historical-priority claim. The source credits established methods and model predecessors; formal correctness and corpus recovery do not establish novelty.

**Separate downstream work (does not reopen this result):** Future interval-annotation extension, an organism-owner map, a specified genetic observation law and justified biological continuation constraints are distinct additional problems. This completed topology-completion obstruction must not be re-proved as if those applications were its missing premises.

**Proof, review and related source links:**

- [Complete finite-gARG scope and interpretation](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-questions/genomic-identifiability/README.md) (proof or status).
- [Actual no-decoder corollary](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-questions/genomic-identifiability/FiniteGenomeIdentifiability.lean) (proof source).
- [Finite-gARG embedding and completion supplier](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/real/WongAlexander.lean) (proof source).
- [Explicit join/fork completion proof](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/lean/SamuelAlexanderResearch/FiniteHistoryCompletion.lean) (proof source).
- [Archived selected endpoint receipt](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-questions/genomic-identifiability/verification.json) (formal receipt).

**Stable key:** genome.FINITE_COMPLETION. **Aliases:** Samuel G01.

</details>


<a id="cb-genome-002"></a>
### Exact laws identify three-taxon relationships, but finite samples do not give certainty
**CB-GENOME-002 · Genomic inference · known three-taxon control**

**Question:** How can an exact probability law identify a relationship while finite observations remain uncertain?

**What we learned:** The exact non-collapsed three-taxon law identifies the relationship. With positive noise, every finite sample fits every label with positive probability; an error smaller than half the probability gap preserves the correct answer.

**What it lets someone do:** Keep ideal-law identification, uncertainty from finite data and robustness of estimated probabilities separate.

**What we cannot conclude:** The taxa are already designated. This neither discovers species boundaries nor guarantees certainty from finitely many observed genes.

**Kind:** theorem. **Mathematical status:** Proved; archived Lean check recorded.

<details>
<summary>Exact scope, prior work, evidence and separate downstream work</summary>

**Exact statement and assumptions.** For the prescribed law P(s)=1−2c/3 and P(g≠s)=c/3, 0≤c<1 identifies both the rooted label and c; c=1 collapses the labels. For 0<c≤1 every finite ordered sample has positive product mass under every label, precluding a uniformly certain finite decoder. An estimate with coordinate error ε and 2ε<1−c retains the correct strict maximizer; the half-gap boundary is sharp. The singleton-mass adverse witness has mass at least (c/3)^n, not a formally measured total error lower bound. Three preassigned taxa and a prescribed rooted gene-tree law; no coalescent derivation, raw-DNA decoding, species delimitation or aggregate error measure is formalized. The separate Hoeffding bound min(1,2exp(−n(1−c)^2/2)) is a standard written derivation, not a Lean endpoint.

**Origin.** classical prior. Formalization of the known Allman–Degnan–Rhodes three-taxon law and elementary finite-evidence/stability consequences; the separately written statistical bound is a standard application of Hoeffding.

**Prior work.** Allman–Degnan–Rhodes's classical three-taxon coalescent formula and Hoeffding's inequality retain credit; the project expressly makes no mathematical or biological novelty claim.

**Our contribution and attribution.** The original 25 September package formalizes conditional exact-law identification and the sharp deterministic half-gap boundary, while exposing finite-sample support overlap. This card recovers a completed known-model formalization, not new biological or statistical theory.

**Evidence, kept separate:**

- **Hand:** Both exact-law and finite-evidence Lean bodies and their complete scope notes were read. The project explicitly identifies the classical formula and standard statistical deductions as known mathematics; no new novelty or whole-process proof review is asserted.
- **Formal:** Archived Lean 4.33.1 evidence contains six printed exact-law endpoints and eight selected finite-evidence endpoints; the latter receipt is dated 2026-09-25T11:16:46.5925867Z and declares Mathlib 0df444a360eaa60ab8c11dca51a86af692955474. Only standard foundational axioms are recorded. The stochastic-process derivation, aggregate error measure and Hoeffding tail bound are not among these formal endpoints.
- **Execution:** Historical compiler and selected-axiom evidence is linked, with exact source and receipt pins. No build, finite-control rerun or scientific execution occurred during this recovery; no universal native refinement is claimed.
- **Empirical:** A theorem about specified observations and mathematical models, not measured genetic data, a validated species classifier or an experimentally established inheritance law.

**Novelty:** Known classical model and elementary deductions formalized; no mathematical or biological novelty claimed.

**Separate downstream work (does not reopen this result):** The coalescent derivation and exponential parameter bridge, empirical gene-tree reconstruction and dependence/model checks are outside this formalization. The standard written Hoeffding bound is separate from the checked deterministic and singleton-mass statements.

**Proof, review and related source links:**

- [Classical model, attribution and exact-law scope](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-questions/genomic-identifiability/positive/README.md) (prior work).
- [Exact-law proof source](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-questions/genomic-identifiability/positive/ThreeTaxonIdentifiability.lean) (proof source).
- [Archived six exact-law axiom reports](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-questions/genomic-identifiability/positive/validation.txt) (formal receipt).
- [Finite-evidence theorem and separate written tail bound](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-questions/genomic-identifiability/next/FORMAL-SCOPE.md) (proof or status).
- [Finite-evidence proof source](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-questions/genomic-identifiability/next/ThreeTaxonFiniteEvidence.lean) (proof source).
- [Archived eight-endpoint finite-evidence receipt](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-questions/genomic-identifiability/next/verification.json) (formal receipt).

**Stable key:** genome.THREE_TAXON_CONTROL. **Aliases:** Samuel G02.

</details>


<a id="cb-genome-003"></a>
### Missing diploid ownership can change long-term ancestry; informative samples are characterized exactly
**CB-GENOME-003 · Genome ownership · ambiguity and informative sampling**

**Question:** What remains undetermined if every realized copy transmission is known but the pairing of copies into organisms is missing?

**What we learned:** The same complete copy history can have opposite long-term organism-ancestry properties. In the constructed family, exactly characterized ownership samples resolve that ambiguity.

**What it lets someone do:** Specify which individual-association records are essential and distinguish informative infinite records from finite evidence.

**What we cannot conclude:** The result is not about every pedigree, noisy DNA observations or identical stochastic likelihoods. The infinite-record decoder is not a terminating decision algorithm.

**Kind:** theorem. **Mathematical status:** Proved; archived Lean check recorded.

<details>
<summary>Exact scope, prior work, evidence and separate downstream work</summary>

**Exact statement and assumptions.** One fixed eight-lane infinite transmission graph admits, after every prescribed finite mixing-prefix length, two diploid owner schedules with opposite whole-population IAP/specieslike/inspecies status. IAP means that each member has finitely many descendants or finitely many non-descendants within the population. Both have four founders, four organisms per generation, exactly two copies per organism, two distinct parents per nonfounder and two children per organism, weak connectivity and real generation dates; every organism edge is exactly witnessed by transmission. In this mixing/delayed-splitting family, the noiseless lane-0/lane-3 co-ownership record on a fixed mask identifies IAP iff the sampled odd generations are unbounded. Even complete ownership at every even generation fails. With a supplied even upper bound B≥2 on switch times, identification is equivalent to sampling an odd generation after B, and one query at B+1 suffices. Any prescribed prefix length of this mixing history, not every possible ownership prefix. Same realized history is not equality of stochastic likelihoods. No biological law or positive probability for the entire infinite construction, no generic pedigree decoder, no noisy/adaptive sampling and no inference of owner labels from phasing. Exact image edges need not lift organism paths. Infinite-record decoder is set-theoretic, not a uniformly terminating algorithm.

**Origin.** project posed. The 27 September 2026 constrained diploid counterexample and its same-family static-sampling continuation were formulated within the existing genome-to-organism observation programme. General pedigree ambiguity and monitoring distinctions are established predecessors.

**Prior work.** 27 September 2026 construction and sampling continuation. Genetic/genealogical distinctions, pairing and pedigree nonidentifiability are prior work. Thatte's potential-parent representation and Kirkpatrick's stochastic-likelihood nonidentifiability have different contracts. Bounded prior review found no exact combined match; worldwide priority remains unestablished. G04 is an elementary sharp deduction from G03, not a separate general monitoring principle.

**Our contribution and attribution.** The original construction makes the omitted-ownership obstruction hold under exact transmission-edge images, diploid fibres, biparental degree/sex constraints, arbitrary mixing-prefix lengths and opposite actual Alexander predicates. The continuation characterizes all static sampling masks and the supplied-bound one-query case within precisely that family. These are grouped because G04 directly reuses G03, not counted as unrelated discoveries.

**Evidence, kept separate:**

- **Hand:** The original independent internal construction review supplies the all-generation mathematical argument; the later sampling review accepts the actual query, missingness, all-mask quantifiers and bounded-family condition. Final source/receipt successors close the older finite-gARG mapping gate. This recovery read all three G03 modules and the G04 module, without issuing a new transitive or external peer-review certificate.
- **Formal:** The G03 receipt dated 2026-09-27T05:35:21.269315Z records a fresh 31-project-module rebuild and 77 public theorem reports; source identity is by listed per-file SHA256, not merely its pre-replay commit. G04's 2026-09-27T05:50:33.874472Z clean-commit gate at c071d4b895b8fe979211b68ac30240f8833e707d covers five modules and 15 new plus five reused endpoints. Both pin Lean 4.33.1/Mathlib 0df444a360eaa60ab8c11dca51a86af692955474 and standard axioms. These are overlapping scoped receipts, not 97 independent results or one combined ARG replay.
- **Execution:** Historical compiler and selected-axiom evidence is linked, with exact source and receipt pins. No build, finite-control rerun or scientific execution occurred during this recovery; no universal native refinement is claimed.
- **Empirical:** A theorem about specified observations and mathematical models, not measured genetic data, a validated species classifier or an experimentally established inheritance law.

**Novelty:** The recorded bounded primary-source comparison found no exact combined predecessor; worldwide priority remains unestablished. General ownership ambiguity and finite/infinite monitoring principles are prior mathematics.

**Separate downstream work (does not reopen this result):** No noisy/adaptive pedigree theorem, equality of genetic likelihoods or positive-probability realization under a biological reproduction law is supplied. Justifying ownership provenance, arbitrary schedules or a switch bound requires separate evidence. The exact infinite-record criterion is complete and does not promise a uniformly terminating decoder.

**Proof, review and related source links:**

- [Complete ownership construction and exact source maps](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/genome-pedigree/README.md) (proof or status).
- [Actual ownership proof source](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/genome-pedigree/PairingCore.lean) (proof source).
- [Actual finite-gARG truncation proof](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/genome-pedigree/PairingGARG.lean) (proof source).
- [Finite-gARG and real-date adapter](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/genome-pedigree/PairingBridge.lean) (proof source).
- [Independent internal construction review](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/genome-pedigree/PAIRING-FALSIFICATION.md) (hand review).
- [Bounded ownership prior-work comparison](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/genome-pedigree/PAIRING-PRIOR-ART.md) (prior work).
- [Archived 31-module and 77-theorem ownership receipt](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/genome-pedigree/verification/PROOF-RECEIPT.json) (formal receipt).
- [Exact static-sampling criterion and bounded corollary](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/owner-observations/README.md) (proof or status).
- [Actual sampling proof source](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/real/PairingObservation.lean) (proof source).
- [Independent internal final sampling review](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/owner-observations/INDEPENDENT-REVIEW.md) (hand review).
- [Archived exact-commit sampling receipt](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/owner-observations/verification/RESULT.json) (formal receipt).

**Stable key:** genome.OWNERSHIP_AND_SAMPLING. **Aliases:** Samuel G03; Samuel G04.

**Typed connections:**

- [CB-GENOME-001](#cb-genome-001): same principle. Both expose missing information for a future-inclusive target, but arbitrary finite-source completion and fixed complete infinite-source ownership have different quantifiers; neither is silently substituted for the other.

</details>


<a id="cb-genome-004"></a>
### Independent inheritance blocks have an exact recovery probability; matching marginals do not suffice
**CB-GENOME-004 · Pedigree observations · exact recovery and dependence**

**Question:** When do observed symbol matches recover sampled families, and does collecting more blocks always add information?

**What we learned:** The stated independent-block model has an exact recovery probability. Repeated correlated blocks can have every correct one-block marginal yet provide no additional recovery gain.

**What it lets someone do:** Use a precise finite-observation benchmark and check whether an independence assumption really supports the claimed benefit of more data.

**What we cannot conclude:** This does not recover arbitrary pedigrees, prove the full multigeneration REC-GEN theorem, or make ordinary DNA letters unique parent identifiers.

**Kind:** theorem. **Mathematical status:** Proved; archived Lean check recorded.

<details>
<summary>Exact scope, prior work, evidence and separate downstream work</summary>

**Exact statement and assumptions.** With disjoint parental pairs, per-block distinct parent symbols, exact observations and independent fair child/block copying, connect children sharing a symbol in any block. For B≥1 and nonempty family sizes m_i, exact partition recovery has probability ∏_i[1−(2^(m_i−1)−1)2^(−B(m_i−1))]. The estimator uses only observed symbols. A correlated law repeating each child's one fair bit across all blocks retains each full one-block marginal but leaves one-family success at 2^(1−m), independently of positive B. Pathwise, adding blocks cannot spoil a correct recovery even without independence. The formal notation uses m_i=n_i+1 and includes singleton families and the empty family collection by the product convention. Not full multigeneration REC-GEN, estimator optimality, ordinary DNA-symbol collision handling, a continuous ARG-to-block-law coupling, or infinite IAP/species inference. The formal observed-output theorem uses a finite measurable alphabet. The repeated-law formal endpoint is one-family. Written pair-event distribution identifiability, union/error bounds and couple-vertex construction have separately stated non-Lean status.

**Origin.** project posed. A fixed one-generation specialization of the cited independent founder-block model, followed by an explicit dependence control. It does not claim to solve the source's full multigeneration REC-GEN theorem.

**Prior work.** A one-generation specialization motivated by Kim–Mossel–Ramnarayan–Turner's block model, with an elementary component-estimator improvement over the incoming all-three-sharing control. Sources explicitly claim no novelty or first formalization; Mossel–Vulakh simulation work remains prior, not reproduced here.

**Our contribution and attribution.** The original specialization replaces its incoming all-three-sharing control with an observed connected-component estimator, proves its exact finite-family probability, and constructs an actual correlated law with unchanged complete one-block marginals. It retains the written/formal boundaries and expressly makes no novelty claim.

**Evidence, kept separate:**

- **Hand:** The original independent mathematical review accepts the complement/count/product, pair-event and dependence arguments; the later semantic review checks all six mathematical modules' observation/model contracts. This recovery read the complete written theorem and final Recovery/Dependence bodies, not all remaining module bodies. No fresh whole-closure acceptance or human peer review is claimed.
- **Formal:** Archived exact-clean-commit PASS at ae0beee8d04e32c45f28d2f465b924d6816c82a5, dated 2026-09-27T05:23:06.127917Z, covers seven project modules and 31 selected declarations with Lean 4.33.1, Mathlib 0df444a360eaa60ab8c11dca51a86af692955474 and only standard axioms. The observed-output theorem assumes a finite measurable symbol alphabet; the repeated-block formal endpoint is one-family. The written distribution-identifiability, union/error bounds and explicit couple-vertex construction are not additional Lean endpoints.
- **Execution:** Historical compiler and selected-axiom evidence is linked, with exact source and receipt pins. No build, finite-control rerun or scientific execution occurred during this recovery; no universal native refinement is claimed.
- **Empirical:** A theorem about specified observations and mathematical models, not measured genetic data, a validated species classifier or an experimentally established inheritance law.

**Novelty:** No independent historical-priority claim. The source credits established methods and model predecessors; formal correctness and corpus recovery do not establish novelty.

**Separate downstream work (does not reopen this result):** A Wong continuous-ARG-to-independent-block law, realistic linkage/mutation/errors/shared parents, full REC-GEN, infinite Alexander transfer and verified executable complexity are outside scope. Existing written distribution-identifiability and coupling corollaries are complete written deductions but not Lean endpoints here; missing formalization does not reopen their mathematics.

**Proof, review and related source links:**

- [Final observed-family statement and limits](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/pedigree-block/README.md) (proof or status).
- [Complete written derivation and separately scoped corollaries](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/pedigree-block/source/written-precursor/RECOVERY-THEOREM.md) (proof or status).
- [Written-proof independent internal review](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/pedigree-block/source/written-precursor/REVIEW.md) (hand review).
- [Final semantic/source review](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/pedigree-block/STATEMENT-REVIEW.md) (hand review).
- [Actual observed-output recovery proof](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/real/PedigreeBlockRecovery.lean) (proof source).
- [Actual full-marginal dependence counterexample](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/real/PedigreeBlockDependence.lean) (proof source).
- [Exact claim-by-claim formal/written ledger](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/pedigree-block/LEDGER.json) (proof or status).
- [Archived seven-module and 31-endpoint exact-commit receipt](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/pedigree-block/verification/RESULT.json) (formal receipt).

**Stable key:** genome.SAMPLED_FAMILY_RECOVERY. **Aliases:** Samuel G05.

**Typed connections:**

- [CB-GENOME-003](#cb-genome-003): same principle. A complementary finite-observation control with a different explicitly supplied stochastic law; it neither provides the ownership oracle nor establishes infinite-IAP identification.

</details>

<a id="cb-memory-001"></a>
### An exact predictive summary must keep the distinctions that future actions can expose
**CB-MEMORY-001 · Time and memory · exact controlled representations**

**Question:** When can a simpler state predict every allowed next step, and what information must it retain?

**What we learned:** Equal summaries must remain equal after every common action. The coarsest exact predictive state keeps precisely the distinctions between finite future responses. In the stipulated parity model, one memory bit suffices even though no fixed recent-history window does.

**What it lets someone do:** Check whether a proposed summary supports exact controlled predictions, identify missing state, and reuse proved restriction adapters under their actual contracts.

**What we cannot conclude:** This is not a discovery algorithm for unknown dynamics or a finding about physical time, consciousness or biological and human memory.

**Kind:** theorem. **Mathematical status:** Proved; archived Lean check recorded.

<details>
<summary>Exact scope, prior work, evidence and separate downstream work</summary>

**Exact statement and assumptions.** For fixed total deterministic dynamics T:A→X→X on arbitrary carriers, an onto encoding c admits a unique reduced update iff it is fibre-compatible for every action. Outputs after all finite action words, including the empty word, define a quotient to which every onto exact output-preserving representation factors uniquely and surjectively, commuting with actions and outputs. Global depth-k equivalence stability at depth k+1 on every declared state pair implies full finite-future equivalence. Feedback trajectories are preserved only when the actual controller factors through the retained state. In the four-action wait/prime/probe/reset model, the summary (visible bit, history parity/memory bit) commutes for arbitrary finite initial records and all finite words/times, has exactly four predictive classes, and all four are attainable from one initialization. No fixed suffix window determines parity on every record, but one retained parity bit does. Removing or changing the probe changes sufficient information. Actual destructive ancestral restriction to subsets of the original samples and fixed-locus finite-gARG extraction instantiate the controlled map. The imported opposite-completion no-decoder consequence is already recorded at CB-GENOME-001, not a second result here. The global certificate is not sampled agreement, a termination guarantee or an implemented minimization algorithm.

**Completion and validation status.** Proof authorship and mathematics are complete. Formal verification: kernel checked selected release. Independent review: recorded independent ai source review. Reuse the completed exact statement. Missing new execution, formalization or broader-model admission does not reopen its proof. Grouping and theorem counts are not discovery counts.

**Origin.** project posed. M01 and M03 select exact fixed-model questions from the broader time/self-reference source agenda. The predictive continuation completes the earlier arbitrary-history and generic probe-refinement gates; it does not solve the source's entire questions.

**Prior work.** Exact abstraction, behavioral/coalgebraic quotients, action-word distinguishability and sufficient controlled state are established mathematics. The archived comparison credits Rutten, Givan–Dean–Greig, Shalizi–Crutchfield and Littman–Sutton–Singh at their differing model contracts. No fresh complete prior-literature survey is claimed by this recovery.

**Our contribution and attribution.** The original package provides checked universal factorization, exact action/output interfaces, the arbitrary-history parity bridge, a global depth certificate and actual bounded graph adapters. This card combines the explicitly reused exact-abstraction predecessor with its continuation instead of counting them as separate discoveries.

**Evidence, kept separate:**

- **Hand:** The complete deterministic scope review and its final corrections were read, alongside all seven direct deterministic/application Lean bodies. The archived review checks statement and source correspondence, not a separate compiler run or human/external peer review.
- **Formal:** Archived 27 September 2026 receipt records Lean 4.33.1, Mathlib 0df444a360eaa60ab8c11dca51a86af692955474, a fresh rebuild of 37 project sources with zero compiler exits, and 108 selected axiom reports: 92 packet declarations including supporting lemmas plus 16 reused endpoints. Per-file SHA256 is authoritative; the named pre-replay commit may precede input edits. Only propext, Classical.choice and Quot.sound are recorded, with no missing/unexpected reports or sorryAx. External Mathlib reuse and hosted CI remain separate; no new build or full transitive audit occurred here. The arbitrary-history, generic probe decoder and all-time factored-feedback endpoints supersede their earlier written-only or one-step labels. The finite n−m partition bound is written discussion, not an additional Lean endpoint.
- **Execution:** Historical project-build receipts and the separate bounded controlled checker/replay are preserved. Finite enumeration is not the support for arbitrary histories after the later formal continuation. No scientific execution occurred in this recovery.
- **Empirical:** These are statements about fixed mathematical models and declared observations/actions, not empirical biology, consciousness, human or language-model memory, or physical-time necessity.

**Novelty:** Established methods retain credit; this is recovery of completed formalization, explicit contracts and bounded applications, not a new theorem or historical-priority claim.

**Separate downstream work (does not reopen this result):** Automatic adequate-state discovery, general evolving semantics, empirical state/intervention correspondence, a stochastic statistical version of the matched-type/clock null, interval-record dynamics and marked-ARG kernel preservation remain outside this exact theorem. Destructive restriction never restores discarded edges. The ancestry completion supplier and its identical-ancestors property, meaning each member has finitely many descendants or finitely many non-descendants in the stated set, retain CB-GENOME-001's separate scope.

**Proof, review and related source links:**

- [Exact reduction criterion and all-time control preservation](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-problems/time-self-reference/exact-abstraction/ExactAbstraction.lean) (proof source).
- [Coarsest predictive state and global depth certificate](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-problems/time-self-reference/predictive-memory/PredictiveState.lean) (proof source).
- [Arbitrary-history parity and generic probe-refinement proof](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-problems/time-self-reference/predictive-memory/ControlledMemory.lean) (proof source).
- [Same-type/clock and delayed-distinction controls](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-problems/time-self-reference/predictive-memory/HistoryObservation.lean) (proof source).
- [Actual destructive ancestral-restriction adapter](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-problems/time-self-reference/predictive-memory/AncestryObservation.lean) (proof source).
- [Fixed-locus gARG adapter and imported completion consequence](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-problems/time-self-reference/predictive-memory/WongPredictiveBridge.lean) (proof source).
- [Independent deterministic statement/source review](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-problems/time-self-reference/predictive-memory/INDEPENDENT-SCOPE-REVIEW.md) (hand review).
- [Latest source-hashed formal receipt](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-problems/time-self-reference/predictive-memory/verification/PROOF-RECEIPT.json) (formal receipt).
- [Later source-to-result audit and supersession](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-problems/time-self-reference/predictive-memory/AUDIT.md) (proof or status).

**Stable key:** september.MEMORY.EXACT_CONTROLLED_PREDICTIVE_STATE. **Aliases:** Samuel M01; Samuel M03; ExactAbstraction; PredictiveState; ControlledMemory.

**Typed connections:**

- [CB-GENOME-001](#cb-genome-001): reused theorem. WongPredictiveBridge.no_global_iap_decoder invokes the actual_garg_opposite_infinite_completions supplier already indexed by CB-GENOME-001. This is a reused completion consequence, not a newly counted source theorem.
- [CB-SOFTSCI-001](#cb-softsci-001): same principle. Static observation fibres share an information-loss principle, but do not supply controlled universal factorization or the arbitrary-history theorem.

</details>


<a id="cb-memory-002"></a>
### The present group membership does not determine a predecessor-restoring split
**CB-MEMORY-002 · Changing-agent models · predecessor information**

**Question:** If two groups have the same members, must they split in the same way?

**What we learned:** Not when a split restores immediate predecessors: different legal formation histories leave the same current grouping but require different next partitions.

**What it lets someone do:** Identify a concrete piece of hidden history that this split operation must retain before importing a partition-only model.

**What we cannot conclude:** It does not refute all coalition models, prove full scheduler reachability, or describe biological selfhood.

**Kind:** counterexample. **Mathematical status:** Proved; archived Lean check recorded.

<details>
<summary>Exact scope, prior work, evidence and separate downstream work</summary>

**Exact statement and assumptions.** Legal binary merge forests contain each of four persistent sites exactly once. Adjacent merges combine (0,1) then their group with 2, or (1,2) then their group with 0; site 3 remains a spectator. Both current partitions are {{0,1,2},{3}}. Restoring the immediate predecessors of the same composite yields {{0,1},{2},{3}} versus {{0},{1,2},{3}}. The proof preserves legality and excludes every deterministic partition-only split uniformly over admissible split states, even with arbitrary block-family outputs. This is not an illegal-action totalization artifact. Lean adjacency is forest-list adjacency; the separate pinned 2×2 eight-neighbour IPDm check is not a full formal spatial refinement.

**Completion and validation status.** Proof authorship and mathematics are complete. Formal verification: kernel checked selected release. Independent review: recorded independent ai source review. Reuse the completed exact statement. Missing new execution, formalization or broader-model admission does not reopen its proof. Grouping and theorem counts are not discovery counts.

**Origin.** project posed. M02 formalizes the source's predecessor-restoring merge/split operation as a precise bounded obstruction. It is not a solution of the broader theory of games with changing decision makers.

**Prior work.** Fibre-compatibility obstructions are classical and reuse the exact criterion in CB-MEMORY-001. Apt–Witzel coalition formation already permits whole-coalition value comparisons; its preference, compatibility and stability assumptions are not the same as this predecessor-restoring transition contract.

**Our contribution and attribution.** The original finite source-bound witness makes the same present partition and same controlled split produce different restored partitions, with legal histories and an unchanged spectator. A separate bounded implementation control preserves identical active IDs and visible metadata using declared mocks.

**Evidence, kept separate:**

- **Hand:** The complete original source/operation review, merge-history note and actual finite Lean body were read. Full published-paper/source-version equivalence and the stochastic learning scheduler were not verified; no new external or human peer review is claimed.
- **Formal:** The original 25 September two-module receipt covers 16 selected endpoints, including eight merge-history endpoints, with Lean 4.33.1 and only standard foundational axioms. Archived 27 September 2026 receipt records Lean 4.33.1, Mathlib 0df444a360eaa60ab8c11dca51a86af692955474, a fresh rebuild of 37 project sources with zero compiler exits, and 108 selected axiom reports: 92 packet declarations including supporting lemmas plus 16 reused endpoints. Per-file SHA256 is authoritative; the named pre-replay commit may precede input edits. Only propext, Classical.choice and Quot.sound are recorded, with no missing/unexpected reports or sorryAx. External Mathlib reuse and hosted CI remain separate; no new build or full transitive audit occurred here.
- **Execution:** The archived receipt at IPDm eca9b122480b8c654081d6a844176417aefbbcae reports original merge/split AST bodies, six helpers and four board methods with explicit Agent/Tree and NumPy helper mocks. It verifies this operator witness, not a complete simulation, policy scheduler or probabilistic reachability. No execution was repeated.
- **Empirical:** These are statements about fixed mathematical models and declared observations/actions, not empirical biology, consciousness, human or language-model memory, or physical-time necessity.

**Novelty:** Established methods retain credit; this is recovery of completed formalization, explicit contracts and bounded applications, not a new theorem or historical-priority claim.

**Separate downstream work (does not reopen this result):** Full source-game semantics need explicit controllers, inherited policies/memory, payoff transport, legality and any desired stochastic reachability. Equilibrium, convergence, paper-version equivalence and biological identity remain separate. Nondeterministic overapproximations are not excluded.

**Proof, review and related source links:**

- [Complete admissible split proof](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-problems/time-self-reference/exact-abstraction/MergeHistoryProjection.lean) (proof source).
- [Merge-history statement and model limits](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-problems/time-self-reference/exact-abstraction/MERGE-HISTORY.md) (proof or status).
- [Independent source/operation and prior review](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-problems/time-self-reference/independent-rsos-review.md) (hand review).
- [Pinned operator check with explicit mocks](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-problems/time-self-reference/independent-ipdm-operator-test.json) (execution review).
- [Original exact-abstraction verification receipt](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-problems/time-self-reference/exact-abstraction/PUBLIC-VERIFICATION.json) (formal receipt).
- [Later fresh project receipt](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-problems/time-self-reference/predictive-memory/verification/PROOF-RECEIPT.json) (formal receipt).

**Stable key:** september.MEMORY.PREDECESSOR_SPLIT_OBSTRUCTION. **Aliases:** Samuel M02; MergeHistoryProjection.

**Typed connections:**

- [CB-MEMORY-001](#cb-memory-001): reused theorem. MergeHistoryProjection imports ExactAbstraction and instantiates its fibre-compatibility obstruction with the actual legal forest states; the admissible-state strengthening is proved separately.

</details>


<a id="cb-memory-003"></a>
### An exact stochastic summary preserves the full adaptive observation record
**CB-MEMORY-003 · Stochastic models · exact retained experiment laws**

**Question:** When can a smaller probabilistic model replace the original during an adaptive experiment?

**What we learned:** Matching pushed transitions, initial law, decoded observations and controller information preserves the entire finite observation/action record. Separate marginals or perfect output predictions alone need not provide that state-preserving map.

**What it lets someone do:** Check the exact conditions for reduced-model simulation of the declared experiment and avoid inferring latent transition structure from trace agreement alone.

**What we cannot conclude:** It does not automatically cover continuous kernels, omitted controller/sensor memory, unknown chemical realizations or actual biological mechanisms.

**Kind:** theorem. **Mathematical status:** Proved; archived Lean check recorded.

<details>
<summary>Exact scope, prior work, evidence and separate downstream work</summary>

**Exact statement and assumptions.** For K:A→X→PMF X on arbitrary carriers with countably supported probability mass functions, an onto q admits a unique reduced kernel iff pushed next-state laws are constant on every q-fibre for all actions. Pointwise commutation is equivalent to one-step law preservation for all initial PMFs; one fixed mixture is insufficient for the converse. Given an exact kernel, the pushed initial law, output decoding and conditional policy factorization through the full retained history, all finite joint state/action and observation/action transcript laws are preserved, including initial and terminal observations. Preservation itself does not require onto. Randomized observed-history policies have an explicit adapter. Joint next-state/measurement kernels allow correlation, but must be Markov in the declared latent state. Copied/complemented fair bits have equal marginals but different joint laws. A six-state single-action chain has two starts with equal complete output traces at every finite horizon yet different pushed next predictive-profile laws, so no profile kernel commutes with those actual source transitions. Randomized tests of the recorded trace cannot separate these starts; another Markov realization of the same outputs is not excluded.

**Completion and validation status.** Proof authorship and mathematics are complete. Formal verification: kernel checked selected release. Independent review: recorded independent ai source review. Reuse the completed exact statement. Missing new execution, formalization or broader-model admission does not reopen its proof. Grouping and theorem counts are not discovery counts.

**Origin.** project posed. M04 is the exact discrete stochastic successor to the controlled-state package. Its fixed action, state, sensor and policy contracts were explicitly chosen; it does not settle all source questions about changing or living systems.

**Prior work.** Strong lumpability, probability-mass-function transport, and trace equivalence versus stronger state-kernel preservation are established mathematics. The recorded comparison distinguishes observational predictive-state results from intervention-preserving dynamics; no general new theory or priority claim is made.

**Our contribution and attribution.** The original package supplies complete checked adaptive finite joint-history preservation and a correlated-sensor interface, with source-level countercontrols to marginal-only and predictive-profile shortcuts. This recovery restores its completed exact status rather than reopening the earlier stochastic gate.

**Evidence, kept separate:**

- **Hand:** Both complete stochastic Lean bodies, the final exact-scope explanation and the independent statement/example review were read. The final review records no unresolved mathematical or public-scope blocker for the exact implementation. It is an AI source review, not a separate compiler run or external peer review.
- **Formal:** Archived 27 September 2026 receipt records Lean 4.33.1, Mathlib 0df444a360eaa60ab8c11dca51a86af692955474, a fresh rebuild of 37 project sources with zero compiler exits, and 108 selected axiom reports: 92 packet declarations including supporting lemmas plus 16 reused endpoints. Per-file SHA256 is authoritative; the named pre-replay commit may precede input edits. Only propext, Classical.choice and Quot.sound are recorded, with no missing/unexpected reports or sorryAx. External Mathlib reuse and hosted CI remain separate; no new build or full transitive audit occurred here. The stochastic continuation contributes two modules and 36 declarations within that overlapping receipt, not 36 new discoveries. The appended approximate-TV construction is explicitly unmechanized and is not certified by these exact-kernel checks.
- **Execution:** Historical compiler/selected-axiom evidence is linked, not rerun. The all-horizon trace counterexample is proved symbolically, not inferred from finite simulations. No new stochastic experiment or scientific software execution occurred.
- **Empirical:** These are statements about fixed mathematical models and declared observations/actions, not empirical biology, consciousness, human or language-model memory, or physical-time necessity.

**Novelty:** Established methods retain credit; this is recovery of completed formalization, explicit contracts and bounded applications, not a new theorem or historical-priority claim.

**Separate downstream work (does not reopen this result):** General continuous measures, infinite path measures, source-adequate latent states and conditional controller randomness require further interfaces. Persistent sensor drift/memory must be included in latent state. The appended finite-space approximate-TV proposal has a reviewed coupling/sharpness argument but retains microscopic-marginal lifting, transcript representation and formalization obligations; it is not another completed formal gate. No marked-Wong-process or unrestricted hidden-reaction classification follows.

**Proof, review and related source links:**

- [Exact kernels and adaptive full-history preservation](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-problems/time-self-reference/predictive-memory/StochasticAbstraction.lean) (proof source).
- [Full-trace and joint-marginal countercontrols](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-problems/time-self-reference/predictive-memory/StochasticExamples.lean) (proof source).
- [Exact stochastic contract and reserved approximate gate](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-problems/time-self-reference/predictive-memory/STOCHASTIC.md) (proof or status).
- [Independent exact-source review and approximate-status boundary](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-problems/time-self-reference/predictive-memory/STOCHASTIC-SCOPE-REVIEW.md) (hand review).
- [Historical full project and selected-axiom receipt](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-problems/time-self-reference/predictive-memory/verification/PROOF-RECEIPT.json) (formal receipt).

**Stable key:** september.MEMORY.STOCHASTIC_EXPERIMENT_PRESERVATION. **Aliases:** Samuel M04; StochasticAbstraction; StochasticExamples.

**Typed connections:**

- [CB-MEMORY-001](#cb-memory-001): proved adapter. StochasticAbstraction.deterministic_instance embeds a supplied exactly commuting deterministic update as point-mass kernels. This adapter preserves that declared contract, not every broader application mentioned on the deterministic card.
- [CB-GENOME-004](#cb-genome-004): same principle. The actual repeated-block dependence counterexample and the generic copied/complemented-bit example both distinguish joint information from marginals. Their probability models differ; no theorem import or pedigree-law adapter is asserted.

</details>


<a id="cb-memory-004"></a>
### There is an exact error cost for distinguishing an impossible event from a rare one
**CB-MEMORY-004 · Calibration · finite-sample rare-event uncertainty**

**Question:** Does seeing no event prove that it is impossible?

**What we learned:** Not in the stated independent-trial model. The unavoidable finite-sample error and the distinct rules attaining its two sharp optima are already derived.

**What it lets someone do:** State precisely what a zero-count observation does and does not establish, including what a known lower event-rate bound buys.

**What we cannot conclude:** This is not structural nonidentifiability of the complete laws, a theorem for arbitrary dependent histories or validated evolutionary calibration.

**Kind:** theorem. **Mathematical status:** Proved (not Lean formalized).

<details>
<summary>Exact scope, prior work, evidence and separate downstream work</summary>

**Exact statement and assumptions.** Observe n≥0 independent fully observed binary trials. M0 always returns zero; Me has one known fixed event probability 0<e<1. Randomized decisions are allowed. With q=(1−e)^n, the minimum sum of the two error probabilities is q, the minimum worst error is q/(1+q), and equal-prior Bayes error is q/2. Both respective attaining rules are supplied, including n=0. For fixed e>0 error can approach zero as n grows, but cannot be zero for finite n. Allowing arbitrarily small e prevents a uniform finite-n worst-error guarantee below one half. A supplied e_min>0 bounds the all-zero probability by (1−e_min)^n, supporting a specified error level rather than certainty. The known-rate, independent-trial and complete-observation assumptions are load-bearing.

**Completion and validation status.** Proof authorship and mathematics are complete. Formal verification: not kernel verified. Independent review: source reported independent review. Reuse the completed exact statement. Missing new execution, formalization or broader-model admission does not reopen its proof. Grouping and theorem counts are not discovery counts.

**Origin.** classical prior. M05 selects an elementary sharp binary-testing model to clarify one aspect of the source's broader sparse-history calibration question. The specified two-model proof is complete; the full evolutionary question is not thereby solved.

**Prior work.** Classical binary-hypothesis testing and a shared positive-probability observation event provide the lower bound and attaining rules. No new statistical principle or field-level novelty is claimed.

**Our contribution and attribution.** The original written derivation exposes both sharp criteria, the all-zero contribution, the empty-sample boundary and the difference between finite-sample uncertainty and equality of full observation laws. The recovery preserves that completed authorship rather than treating unformalized probability as an unwritten proof.

**Evidence, kept separate:**

- **Hand:** The full general written derivation was read. README and PROOF-STRUCTURE explicitly record an independent mathematical review, but a separate calibration-specific review body was not located in this bounded pass. This is reported review provenance, not a newly supplied whole-proof acceptance receipt.
- **Formal:** No general Lean probability theorem is recorded for this result. The 37-module predictive-memory receipt explicitly keeps calibration written-only; its theorem counts must not be extended to this proof.
- **Execution:** The archived result and later replay record 15 exact rational cases and 834 deterministic rules. These finite checks support examples and arithmetic, not the arbitrary-n/real-rate theorem. No checker was rerun in this recovery.
- **Empirical:** These are statements about fixed mathematical models and declared observations/actions, not empirical biology, consciousness, human or language-model memory, or physical-time necessity.

**Novelty:** Established methods retain credit; this is recovery of completed formalization, explicit contracts and bounded applications, not a new theorem or historical-priority claim.

**Separate downstream work (does not reopen this result):** A general Lean probability formalization, dependent/path-dependent or unknown-rate model specifications and empirical sampling admission are separate. The two complete laws are distinct and asymptotically distinguishable for fixed e>0. Missing formalization or the separately unlocated review body does not reopen the completed written mathematics.

**Proof, review and related source links:**

- [Complete sharp written derivation and both attaining rules](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-problems/time-self-reference/CALIBRATION-BOUND.md) (proof or status).
- [Completion, prior scope and reported independent review](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-problems/time-self-reference/PROOF-STRUCTURE.md) (proof or status).
- [Independent review also recorded in programme README](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-problems/time-self-reference/README.md) (proof or status).
- [Historical exact finite instances](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-problems/time-self-reference/calibration-results.json) (execution review).
- [Later replay and explicit written-not-Lean status](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-problems/time-self-reference/predictive-memory/verification/CALIBRATION-REPLAY.json) (execution review).

**Stable key:** september.MEMORY.RARE_EVENT_CALIBRATION_BOUND. **Aliases:** Samuel M05; Rare-event calibration bound.

**Typed connections:**

- [CB-GENOME-002](#cb-genome-002): same principle. Both separate exact-law distinction from finite-sample uncertainty. The known three-taxon full-support control is not the same two-model sharp randomized-testing theorem; its separately written Hoeffding bound is not imported here.

</details>


<a id="cb-population-001"></a>
### Two children suffice for target avoidance, even with permanent genders
**CB-POPULATION-001 · Infinite populations · sharp degree threshold**

**Question:** How small can the child cap be while a permanent-gender population avoids a prescribed infinite binary target?

**What we learned:** The exact threshold is two; an avoider exists exactly when the cap is at least two and the target is not eventually periodic.

**What it lets someone do:** Use the same three-root, two-child underlying graph for every such target, changing only genders, while retaining inspecies and specieslike guarantees.

**What we cannot conclude:** Three roots are not proved minimal, and this does not introduce a new line-graph operation or empirical population model.

**Kind:** theorem. **Mathematical status:** Proved; archived Lean check recorded.

<details>
<summary>Exact scope, prior work, evidence and separate downstream work</summary>

**Exact statement and assumptions.** For every natural cap and binary infinite word s, there exist an infinite retained vertex set, an actual eligible permanent-binary-gender population with at most cap children per vertex and finite actual roots, and avoidance of s from every starting vertex, iff cap≥2 and s is not eventually periodic. Nonroots have parents of each gender and chronology/finite-prefix conditions are retained. Below two no eligible infinite population exists. The directed line graph of the original P_s has exactly three roots, exactly two children per vertex and two opposite-gender parents at every nonroot, with full infinite-word language preserved without a shifted first letter. The unlabelled graph is fixed across targets; only genders change. The same actual retained witness is specieslike, an inspecies and reflective. Three-root optimality is not part of the result.

**Origin.** project posed. A source-specific exact question in the original Samuel population programme. Classical population definitions, constructions and methods are credited separately; grouping does not imply multiple newly solved external problems.

**Prior work.** Original Samuel-project proof; classical directed line graph and edge-to-vertex color transfer are explicitly credited. It sharpens the pinned avg-netizen P_s manuscript's stated four-root/cap-four vertex-gender lift. The exact narrower corollary is not explicit in that pinned manuscript; worldwide priority remains unresolved.

**Our contribution and attribution.** The original Samuel project supplies the exact fixed-gender degree threshold, actual full-language recoding and simultaneous cap-two species/inspecies guarantees. This is the precise tighter population-model consequence of a classical recoding, not a rediscovery of the underlying manuscript's classification.

**Evidence, kept separate:**

- **Hand:** The complete original proof/scope notes and relevant archived endpoint entries were read, with full or selected actual source bodies as itemized in the recovery report. Existing recorded completion is preserved. This is not a fresh whole-import proof review or external human peer acceptance.
- **Formal:** The archived 25 September 2026 Lean 4.33.1 core audit explicitly records CapTwo.avoiding_population_exists_iff and CapTwoSpecies.cap_two_inspecies_avoider, with their source hashes and only standard foundational axioms. The 405 core selected endpoint rows concern the wider repository, not 405 discoveries. No checking was rerun.
- **Execution:** Historical compiler/selected-axiom receipts are linked with exact source pins. No Lean, compiler or scientific runtime was executed for this recovery.
- **Empirical:** A theorem about the stated infinite graph/population predicates, not measured biology or a validated empirical species classifier.

**Novelty:** Historical priority is unresolved. Established methods and source examples retain their attribution; archived formal correctness and source recovery do not certify novelty.

**Separate downstream work (does not reopen this result):** Least possible root count at cap two, a generic line-graph formalization, broader models and historical priority are separate questions. Older cap-three/four constructions remain valid but are not the optimal child-cap result.

**Proof, review and related source links:**

- [Exact fixed-gender cap threshold](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/notes/CAP-TWO-THRESHOLD.md) (proof or status).
- [Same cap-two inspecies witness](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/notes/CAP-TWO-SPECIES.md) (proof or status).
- [Cap-two actual population and path source](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/lean/SamuelAlexanderResearch/CapTwo.lean) (proof source).
- [Same-witness species source](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/lean/SamuelAlexanderResearch/CapTwoSpecies.lean) (proof source).
- [Classical line-digraph and manuscript comparison](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/notes/source-audits/LINE-GRAPH-PRIOR-ART-AUDIT.md) (prior work).
- [Integrated September result-family coverage](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/publication-2026-09-29/COVERAGE.md) (proof or status).
- [Archived core endpoint and source-hash audit](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/verification/formal-audit.json) (formal receipt).

**Connections:**

- [CB-SEQ-004](#cb-seq-004) (same principle): Both use the original target-dependent P_s construction. Exact all-start Thue–Morse heights do not supply the general fixed-gender cap threshold, and the two statements are not aliases.

**Stable key:** population.FIXED_GENDER_CAP_TWO. **Aliases:** Samuel T04; CapTwo; CapTwoSpecies.

</details>


<a id="cb-population-002"></a>
### Critical populations have exact tail structure and finite-frontier descriptions
**CB-POPULATION-002 · Infinite populations · structure and port schedules**

**Question:** What structure follows from the critical parent/child balance, and when does it realize every infinite word?

**What we learned:** Persistent minimum crossing width fixes the tail adjacency. Every critical population has an exact legal fair finite-port encoding; full-schedule periodicity separately forces universality.

**What it lets someone do:** Replace the infinite tail with an exact port representation and apply the periodic realization theorem only when its genuine labelled-schedule hypothesis is established.

**What we cannot conclude:** The encoder does not make arbitrary schedules periodic or every critical population universal; rigidity is not a word-language theorem.

**Kind:** theorem. **Mathematical status:** Proved; archived Lean check recorded.

<details>
<summary>Exact scope, prior work, evidence and separate downstream work</summary>

**Exact statement and assumptions.** Three distinct statements concern the existing naturally indexed simple InfiniteLabeledPopulation k k, with finite root support, a parent of every required label at each nonroot and child cap k. (1) Rigidity: if every sufficiently late actual cut has crossing count k(k+1)/2, the eventual adjacency is exactly u→v iff u<v≤u+k. One attaining cut does not give this tail conclusion, and adjacency alone does not establish arbitrary-label universality. (2) Encoding, without minimum-width or periodicity assumptions: eventual_encoding constructs a root-free base, C equal to the actual crossing count, initial tokens and a legal fair C-slot schedule; decoded labelled edges agree exactly for every target beyond the base, including edges from pre-base sources, and every actual tail label is below k. Classical finite bijections are used; no regularity, enumeration or fairness is an extra population premise. (3) Conditional realization: if the constructed full named-slot/replacement-label schedule is eventually periodic with positive period p, every infinite word has a strict actual path beginning within one period of that tail. Finite slots do not imply periodicity. The pre-base graph is not reconstructed by the decoder.

**Origin.** project posed. A source-specific exact question in the original Samuel population programme. Classical population definitions, constructions and methods are credited separately; grouping does not imply multiple newly solved external problems.

**Prior work.** Original population-specific adapters and exact rigidity theorem reuse conservation/finite counting, classical finite-frontier/slice methods and compactness. Recorded comparison credits Oliveira and established omega-regular periodic-fragment results. No invention of these methods or worldwide-priority claim.

**Our contribution and attribution.** The original Samuel package proves minimum-width rigidity for every finite label count and the source-faithful fair-port adapter, then transports the separately conditional full-schedule periodic theorem to actual paths. These are separate completed subclaims, not an automatic periodicity deduction.

**Evidence, kept separate:**

- **Hand:** The complete original proof/scope notes and relevant archived endpoint entries were read, with full or selected actual source bodies as itemized in the recovery report. Existing recorded completion is preserved. This is not a fresh whole-import proof review or external human peer acceptance.
- **Formal:** The archived Lean 4.33.1 core audit records GeneralRigidity and PortDynamics endpoints. The real audit records PortEncoding.eventual_encoding and encoded_periodic_realizes with source hashes, exit zero and no warnings in its isolated imported-module rebuild. The canonical sorted/converse written companions are not promoted to Lean endpoints. No checking was rerun.
- **Execution:** Historical compiler/selected-axiom receipts are linked with exact source pins. No Lean, compiler or scientific runtime was executed for this recovery.
- **Empirical:** A theorem about the stated infinite graph/population predicates, not measured biology or a validated empirical species classifier.

**Novelty:** Historical priority is unresolved. Established methods and source examples retain their attribution; archived formal correctness and source recovery do not certify novelty.

**Separate downstream work (does not reopen this result):** The canonical sorted encoder and converse from eventually translation-periodic labelled graphs to eventually periodic canonical schedules are separately written results, not the stated Lean endpoint. Effective infinite-graph algorithms, arbitrary higher-width classification and unconditional universality are separate extensions. Older blanket 'actual encoder missing' labels are superseded by PortEncoding, not by an unproved periodicity claim.

**Proof, review and related source links:**

- [Minimum-crossing rigidity scope](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/notes/GENERAL-RIGIDITY-THEOREM.md) (proof or status).
- [General finite-label rigidity source](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/lean/SamuelAlexanderResearch/GeneralRigidity.lean) (proof source).
- [Actual population-to-port adapter](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/notes/PORT-ENCODING.md) (proof or status).
- [Actual fair encoding and periodic transport source](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/real/PortEncoding.lean) (proof source).
- [Full-schedule periodic realization](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/notes/PORT-DYNAMICS-FORMALIZATION.md) (proof or status).
- [Schedule semantics and realization source](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/lean/SamuelAlexanderResearch/PortDynamics.lean) (proof source).
- [Written canonical-port and converse companions](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/notes/source-audits/PROPOSAL3-FINITE-PORT-AUDIT.md) (proof or status).
- [Recorded primary-method comparison](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/notes/source-audits/PROPOSALS3-10-SOURCE-AUDIT.md) (prior work).
- [Integrated September result-family coverage](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/publication-2026-09-29/COVERAGE.md) (proof or status).
- [Archived core endpoint and source-hash audit](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/verification/formal-audit.json) (formal receipt).
- [Archived isolated real-project rebuild and endpoint audit](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/verification/real-audit.json) (formal receipt).

**Stable key:** population.CRITICAL_TAIL_AND_PORTS. **Aliases:** Samuel T05 and T06; GeneralRigidity; PortEncoding; PortDynamics.

</details>


<a id="cb-population-003"></a>
### Pruning preserves every infinite word; boundary repair preserves avoidance
**CB-POPULATION-003 · Infinite populations · pruning and eligibility repair**

**Question:** Which deletions preserve infinite target languages, and when can a retained population be made eligible without adding edges?

**What we learned:** Productive pruning preserves the full infinite language. On any fixed infinite retained set, finite parent-label deficiency exactly characterizes deletion-only repair, with a canonical maximal retained-edge relation.

**What it lets someone do:** Choose the appropriate operation knowing whether it preserves every infinite realization or only avoidance, and whether connectivity or species properties require extra premises.

**What we cannot conclude:** Boundary repair need not preserve all word realizations, connectivity or species properties, and its optimization keeps the retained vertex set fixed.

**Kind:** theorem. **Mathematical status:** Proved; archived Lean check recorded.

<details>
<summary>Exact scope, prior work, evidence and separate downstream work</summary>

**Exact statement and assumptions.** For an actual BinaryNatPopulation, productive pruning retains exactly vertices with infinitely many strict descendants. Finite roots, finite children and strict natural chronology yield an infinite ancestrally closed core, a constructed birth-order reindexing into the original eligible model, preservation of any supplied child cap and equivalence of the full infinite Boolean-word language. Whole-graph IAP is required only for the additional whole-core inspecies/specieslike conclusion; IAP means each member has finitely many descendants or finitely many non-descendants in the stated set. Unrestricted maximal connected-IAP-convex clusters are descendant-closed and pruning commutes; common-ancestor/reflection-constrained maximality need not imply descendant closure, although convexity plus reflection still makes pruning commute. Separately, for any fixed infinite retained S, finite incoming-label deficiency is equivalent to existence of an eligible deletion-only repair on exactly S. Deleting all remaining incoming edges at deficient vertices gives the greatest permissible retained-edge relation and inclusion-smallest deleted-edge/root sets, with all deleted edges below a finite birth bound. The reindexed repair preserves eligibility, a supplied child cap and every avoided target, not full language equivalence. The actual P_s C0 repair disconnects; C1 has the shifted original unlabelled geometry.

**Origin.** project posed. A source-specific exact question in the original Samuel population programme. Classical population definitions, constructions and methods are credited separately; grouping does not imply multiple newly solved external problems.

**Prior work.** Original simultaneous model/transport theorems using classical pruning and finite-union arguments; Alexander's species predicates and existing shared-root two-ray counterexample remain credited. The deletion criterion is a direct structural deduction, not a worldwide novelty claim.

**Our contribution and attribution.** The original Samuel package proves simultaneous eligibility, reindexing and exact infinite-language preservation for the productive core, separates two maximality predicates, and characterizes the canonical deletion-only repair. The stronger pruning equivalence is not silently assigned to repair.

**Evidence, kept separate:**

- **Hand:** The complete original proof/scope notes and relevant archived endpoint entries were read, with full or selected actual source bodies as itemized in the recovery report. Existing recorded completion is preserved. This is not a fresh whole-import proof review or external human peer acceptance.
- **Formal:** The archived Lean 4.33.1 core audit names ProductiveCore.reindexed_core_language_iff, the cluster/pruning endpoints and BoundaryRepair's existence, optimality and actual-transport endpoints, with source hashes and only standard foundational axioms. The real audit also records its imported ProductiveCore rebuild. This does not assert that every core module was freshly rebuilt by that separate real audit.
- **Execution:** Historical compiler/selected-axiom receipts are linked with exact source pins. No Lean, compiler or scientific runtime was executed for this recovery.
- **Empirical:** A theorem about the stated infinite graph/population predicates, not measured biology or a validated empirical species classifier.

**Novelty:** Historical priority is unresolved. Established methods and source examples retain their attribution; archived formal correctness and source recovery do not certify novelty.

**Separate downstream work (does not reopen this result):** Productive pruning need not preserve finite paths. Repair allows no added or relabelled edges and does not optimize over a different retained S. Arbitrary-real-date/general-alphabet adapters and empirical species interpretation are separate. Alexander's prior shared-root two-ray example must not be counted as a new counterexample.

**Proof, review and related source links:**

- [Productive pruning and maximality distinctions](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/notes/PRODUCTIVE-CORE-THEOREM.md) (proof or status).
- [Actual core, language and cluster source](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/lean/SamuelAlexanderResearch/ProductiveCore.lean) (proof source).
- [Exact repair criterion and scope](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/notes/BOUNDARY-REPAIR-THEOREM.md) (proof or status).
- [Canonical repair and actual population transport](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/lean/SamuelAlexanderResearch/BoundaryRepair.lean) (proof source).
- [Integrated September result-family coverage](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/publication-2026-09-29/COVERAGE.md) (proof or status).
- [Archived core endpoint and source-hash audit](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/verification/formal-audit.json) (formal receipt).

**Stable key:** population.PRODUCTIVE_PRUNING_AND_REPAIR. **Aliases:** Samuel T08 and T09; ProductiveCore; BoundaryRepair.

</details>


<a id="cb-population-004"></a>
### One synthetic cellular automaton exposes the cost of forgetting state
**CB-POPULATION-004 · Cellular automata · state-aware certificates**

**Question:** Can a state-aware invariant be strictly stronger than all fixed phase-blind two-label speed certificates for the same cellular automaton?

**What we learned:** Yes, for the explicit synthetic three-state rule: every valid static certificate has attained east support one, but every finite nonempty spaceship has horizontal displacement zero.

**What it lets someone do:** Use a concrete fully model-linked example of information lost by state-blind abstraction, with an exact real-convex-hull comparison and a nontrivial oscillator.

**What we cannot conclude:** This is one synthetic three-state rule, not Life-like or empirical evidence; static support one does not mean an actual speed-one spaceship exists.

**Kind:** counterexample. **Mathematical status:** Proved; archived Lean check recorded.

<details>
<summary>Exact scope, prior work, evidence and separate downstream work</summary>

**Exact statement and assumptions.** For the specified synthetic three-state dead/r/l cellular automaton on the integer plane, every valid phase-blind fixed two-label local certificate has east-coordinate support exactly one, attained in the intersection of the two full Mathlib convexHull ℝ sets, not merely rational barycentric approximations. For the same actual evolve/iterate rule, potential p(r)=1,p(l)=0 proves that any finite nonempty initial configuration which recurs exactly as a translate after a natural number of steps has horizontal displacement zero, with arbitrary vertical displacement allowed. Thus horizontal velocity is zero for positive period. A finite nonempty two-cell oscillator is proved by full configuration equalities including the dead exterior. The strict separation is between this actual-rule stateful obstruction and this specified whole static-certificate family; it is not a new speed bound for a published or binary Life-like rule.

**Origin.** project posed. A synthetic same-rule test of information lost by a specified static certificate family, using established potential methods. Not an author-designated conjecture for a published Life-like rule.

**Prior work.** Original faithful same-rule separation and formal real-geometry bridge. State potentials, reduced weights and cycle-mean methods are classical; the existing prior-work audit credits Young–Tarjan–Orlin, Karp and the Alexander/CA literature. No invention of potentials or global-priority certification.

**Our contribution and attribution.** The original Samuel project supplies a faithful same-rule strict separation, the actual global evolution proof and the literal full-real-hull adapter. Classical state potentials remain credited; the synthetic example demonstrates a real abstraction limitation without claiming a new bound for a published automaton.

**Evidence, kept separate:**

- **Hand:** The original written audit and independent semantic-review receipt check the local-certificate quantifiers, signs, full configurations and actual evolution bridge. The later full real-hull scope/source and archived endpoint rows were inspected. This recovery did not conduct a fresh whole-import review or external human peer review.
- **Formal:** The archived Lean 4.33.1 core receipt covers the actual update rule, charge strip, recurrence obstruction and oscillator. The real audit covers StatefulCAReal.static_east_support_one and real_static_gap_and_global_obstruction, with an isolated rebuild, exit zero and no warnings. Full real hulls, including irrational weights, are in scope. No compiler or checker was rerun.
- **Execution:** The linked historical receipt records all 729 local rows and eight sample-orbit generations as independent finite checks, alongside compiler/axiom evidence. These finite checks are not the proof of the universal trajectory obstruction. No execution occurred in this recovery.
- **Empirical:** An exact mathematical example for one specified synthetic rule, not measured hardware, a Life-like experiment or a validated physical prediction.

**Novelty:** Historical priority is unresolved. Established methods and source examples retain their attribution; archived formal correctness and source recovery do not certify novelty.

**Separate downstream work (does not reopen this result):** Application to a published or binary Life-like rule, empirical hardware behaviour and optimization over other certificate families are separate problems. Older rational-hull-only wording is superseded by StatefulCAReal for the exact real optimum; the global theorem is not inferred from the finite checker.

**Proof, review and related source links:**

- [Synthetic rule and global stateful obstruction](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/notes/STATEFUL-CA-FORMALIZATION.md) (proof or status).
- [Literal real-hull comparison](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/notes/STATEFUL-CA-REAL.md) (proof or status).
- [Actual cellular-automaton source](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/lean/SamuelAlexanderResearch/StatefulCA.lean) (proof source).
- [Full real geometry source](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/real/StatefulCAReal.lean) (proof source).
- [Archived independent semantic review and checks](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/notes/source-audits/STATEFUL-CA-LEAN-RECEIPT.md) (hand review).
- [Complete written synthetic-rule audit](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/notes/source-audits/PROPOSAL10-STATEFUL-CA-AUDIT.md) (hand review).
- [Recorded primary-method comparison](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/notes/source-audits/PROPOSALS3-10-SOURCE-AUDIT.md) (prior work).
- [Integrated September result-family coverage](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/publication-2026-09-29/COVERAGE.md) (proof or status).
- [Archived core endpoint and source-hash audit](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/verification/formal-audit.json) (formal receipt).
- [Archived isolated real-project rebuild and endpoint audit](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/verification/real-audit.json) (formal receipt).

**Stable key:** population.STATEFUL_CA_STATIC_GAP. **Aliases:** Samuel T10; StatefulCA; StatefulCAReal.

</details>

## What the connection labels mean

- **Proved adapter:** a proved link that preserves the needed assumptions and observations. Its hand/formal evidence level still matters.
- **Reused theorem:** an actual mathematical supplier, applied after its hypotheses have been met.
- **Same principle:** related reasoning only. No theorem implication is asserted.
- **Candidate connection:** a possible or incomplete route, not an established implication.

## Coverage gaps and next indexing pass

- Not claimed: Exhaustive indexing of every research directory.
- Not claimed: Independent new proof audit of every linked theorem.
- Not claimed: Whole-repository kernel verification.
- Not claimed: Novelty or priority certification.
- This is 97 selected claims, not a file-by-file audit of the complete October corpus or a count of independent novel theorems.
- Physics P2–P4 remain source-question entries in the prior register; no completed project solution is asserted here.
- Earlier fair-M2, rare-hybrid matched-cost, HiddenC4 and several finite-cap return/obstruction branches are preserved in the original ledgers but are not individually expanded here.
- Nine additional existing sequence groups are now indexed from the complete reading editions and original Samuel/Collatz repositories. The p=q=2 companion has recorded completed hand acceptance but unrecovered original proof/review bytes; the reviewed LCS lower-bound/relaxation continuation still needs its exact original statement packet. Broader p,q and lower repetition-threshold coverage remain separately scoped; missing original bytes are not mathematical incompletion by default.
- Selected September Samuel/all-level/query, feedback, G01–G05 genome/ownership and M01–M05 controlled-memory/calibration results are now indexed; the wider infinite-ancestry/genome/SoftSciences programmes, exploratory biological/psychological/social domains and full external catalogue are not exhaustively re-audited. The linked 85-declaration Soft Sciences inventory is represented by five source-specific grouped cards, not 85 discoveries; other outside corpora remain incompletely indexed.
- Selected solver caches, quantum-oracle applicability audits, source-repaired molecular workbench mocks and further application diagnostics remain in the October source map rather than separate first-version cards.
- Some exact antecedent attributions are not yet independently indexed at card level. These are labelled rather than converted into novelty claims.
- Formal counts belong to exact snapshots and receipts. Selected 1611, public 1613, recovered 1614 and older 1615 inventories are not interchangeable whole-repository verification claims.

## Registers reconciled rather than replaced

- [Original master statements](https://github.com/Sodelin/Research-Commons/blob/0c0dc21eed1046c405e86a92673a6d473a934b6d/research/2026-10-05-dot-original-g-master-priority-1913z/MASTER-STATEMENTS.md).
- [Dependency/alias ledger](https://github.com/Sodelin/Research-Commons/blob/4f39707b9834744611af3262e97305bc75d8397a/research/2026-10-05-dot-original-g-master-priority-1913z/DEPENDENCY-ALIAS-LEDGER.md).
- [Current accepted-results register](https://github.com/Sodelin/Research-Commons/blob/4f39707b9834744611af3262e97305bc75d8397a/docs/ACCEPTED-RESULTS-AND-REMAINING-WORK.md).
- [October source map](https://github.com/Sodelin/Research-Commons/blob/d32d85ea056360d66fa7cde76094bc824f24702f/docs/OCTOBER-2026-RESEARCH-MAP.md).

No new theorem, compiler execution or empirical experiment was performed to generate this board. Counts describe catalogue coverage, not the number of novel discoveries.



<a id="cb-alexander-002"></a>
### No countable list of hosts contains all the stated avoiding populations
**CB-ALEXANDER-002 · Alexander structures · countable-host nonuniversality**

**Question:** Could a countable catalogue of host populations contain every population that avoids a fixed infinite label pattern?

**What we learned:** No. From any such avoiding population, one can construct another that escapes every host on the list, even with exactly one parent of each label and any finite global allowance for stretching edges.

**What it lets someone do:** Rule out a precise universal-catalogue proposal while retaining the original population conditions, actual roots and fixed-pattern avoidance.

**What we cannot conclude:** This construction does not preserve a fixed bound on children, forbid terminal individuals or exclude noninjective or arbitrarily stretched maps.

**Kind:** theorem. **Mathematical status:** Proved; archived Lean check recorded.

<details>
<summary>Exact scope, prior work, evidence and separate downstream work</summary>

**Exact statement and assumptions.** Fix an actual Alexander population P avoiding an infinite label word s. For every countable family of actual population hosts U_j, there is one positive finite-fibre terminal clone Q of a one-parent-per-label selection of P such that Q avoids s, its actual roots are canonically equivalent to P's, and every nonroot has exactly one incoming parent of every label. Every infinite word realized by Q is realized by P. For every j, every finite global stretch L and every injective map Q→U_j, some source edge does not map to an undirected host path of length at most L. Hosts need not avoid s or have exact parent counts. The actual population assumptions are infinitude, real chronological birthdates with finite birth sublevels, finitely many roots and children per vertex, functional edge labels and parent coverage at each nonroot. Parent selection can shrink the original language; terminal cloning preserves the selected language exactly. For an already exact-parent P, cloning preserves the whole original language. There is no uniform child cap, no terminal-free condition and no uncountable-host or unbounded-stretch conclusion.

**Origin.** published open problem. Alexander's 2013 Biologically unavoidable sequences, §6, explicitly asks about universal avoiding populations. This is a negative answer under the specified injective, finite-global-stretch convention, not every possible interpretation of the open-ended question.

**Prior work.** Classical locally finite graph nonuniversality and local-growth diagonalization retain de Bruijn/Rado attribution through the accessible Lehner discussion in the bounded source audit. Cherlin–Shelah's embedding conventions are distinguished. No claim is made to invent the general diagonal principle or establish worldwide priority for the population-specific strengthening.

**Our contribution and attribution.** The existing 29 September 2026 human-directed Codex package supplies the actual population adapter, parent selection and terminal-clone construction preserving exact incoming counts, roots and the selected language while defeating a prescribed countable family. This card recovers that completed result; it is not the October uniform-child-cap construction.

**Evidence, kept separate:**

- **Hand:** The full embedding audit and later publication source-correspondence audit were read, together with both actual universal/terminal-clone proof modules. They retain the exact-parent, root, language and stretch boundaries. These are recorded internal AI reviews, not independent human/external peer review or a fresh whole-transitive proof audit.
- **Formal:** Lean 4.33.1 with Mathlib 0df444a360eaa60ab8c11dca51a86af692955474 records 10 reused GenericUniversalAvoiders and 16 TerminalCloneAvoiders selected reports, all compiler exits zero and only standard foundational axioms. The strongest source endpoint is avoiding_no_countable_exact_parent_family_from_any_population, with separate canonical root equivalence. Hosted audit checks the byte-identical reused original and the terminal module; source fidelity remains a separate reviewed axis.
- **Execution:** The recorded local Lean 4.33.1 receipts and raw selected-endpoint logs were read. Fresh read-only hosted metadata confirms run 36631876391 succeeded at 1592b89731d10fc49019ff22cf2f93c7bc799118; the actual workflow/audit contracts and identical selected proof blobs at recovery pin e2502c82 were checked. No compiler, build, scientific execution or new theorem validation occurred during this recovery.
- **Empirical:** An exact theorem in a stated infinite labelled-graph model. No measured biological data, validated species classifier or demonstrated population mechanism is asserted.

**Novelty:** Unresolved for the exact population-specific strengthening. Classical methods are credited; proof checking and source recovery do not establish novelty.

**Separate downstream work (does not reopen this result):** The fixed balanced-child-cap branch is already separately completed at CB-ALEXANDER-001 and must be reused, not reopened. Terminal-free populations, different embedding relations and uncountable host classes are different questions; no new result about them is claimed here.

**Proof, review and related source links:**

- [Complete universal-avoider statement and limitations](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-questions/continuation-2026-09-29/RESULTS.md) (proof or status).
- [Generic population, finite-ball and countable-host proof](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-questions/continuation-2026-09-29/embedding/GenericUniversalAvoiders.lean) (proof source).
- [Exact-parent selection and terminal-clone endpoint](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-questions/continuation-2026-09-29/embedding/TerminalCloneAvoiders.lean) (proof source).
- [Independent internal embedding audit](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-questions/continuation-2026-09-29/embedding/audit.md) (hand review).
- [Bounded primary-literature comparison](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-questions/continuation-2026-09-29/literature/evidence-map.md) (prior work).
- [Pinned seven-module source and compiler-log manifest](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-questions/continuation-2026-09-29/verification-manifest.json) (formal receipt).
- [Successful integrated hosted audit at 1592b897](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/actions/runs/36631876391) (formal receipt).
- [Source-question, statement and bounded prior-work audit](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/publication-audit-2026-09-29/alexander/CLAIM-EVIDENCE.md) (hand review).
- [Alexander's original §6 questions, version 2](https://arxiv.org/html/1212.0186v2#S6) (prior work).

**Typed connections:**

- [CB-ALEXANDER-001](#cb-alexander-001), same principle: Both exclude universal hosts, but the existing October card preserves a uniform balanced child cap and treats one host in that class; this countable-host construction has no uniform child cap. Neither exact contract substitutes for the other.

**Stable key:** alexander.COUNTABLE_HOST_OBSTRUCTION. **Aliases:** Samuel A01.

</details>


<a id="cb-alexander-003"></a>
### Matching states either continue forever or have an exact finite height
**CB-ALEXANDER-003 · Alexander structures · classical certificates and matching heights**

**Question:** What exactly separates an infinite pattern-matching continuation from one that must stop?

**What we learned:** Classical rank and pruning methods give an exact answer on reachable states. Under finite branching, every state either continues forever or has an attained longest continuation; complete finite duplication preserves the corresponding finite heights.

**What it lets someone do:** Use an exact source-specific certificate and identify information that matching heights retain or omit, without inventing a new rank theory.

**What we cannot conclude:** This is not a terminating decision procedure for arbitrary infinite inputs, a rank hierarchy distinguishing every avoiding population or an established new ordinal theorem.

**Kind:** theorem. **Mathematical status:** Proved; archived Lean check recorded.

<details>
<summary>Exact scope, prior work, evidence and separate downstream work</summary>

**Exact statement and assumptions.** For a labelled graph and fixed infinite word s, use reachable vertex/phase states (v,k) witnessed by a path spelling the first k letters. Avoidance is equivalent to well-foundedness of forward continuation and to a decreasing ordinal certificate, without a finite-branching premise. With finite per-label children, natural certificates suffice; states surviving all finite successor-pruning rounds form exactly the infinite-continuation core and the greatest successor fixed point. Its complement is forward closed and well-founded. Each such mortal state has a pointwise least natural height h, equal to an attained maximum number of further matching edges, survives precisely n≤h and is removed at h+1; other states may realize the word, so global avoidance is not assumed for this dichotomy. A phase-zero state survives iff its start realizes the full target. A separate complete positive finite-fibre blow-up preserves and reflects reachable phases and every finite continuation length, and transports least attained natural heights through the actual projection. Its avoiding-population endpoint derives the needed hypotheses. This complete blow-up is not terminal cloning and need not preserve exact parent counts. The written composition with countable-host obstruction and written live-core/infinite-tail transport are not separately named combined Lean endpoints.

**Origin.** classical prior. Source-specific formalization and application of well-founded ordinal ranks, finite-branching continuation, greatest fixed points and attained heights. Alexander's 2013 §6 ordinal-characterization question is genuine, but its presence does not establish that this classical instantiation is a novel theorem.

**Prior work.** Standard well-founded rank machinery, König-type finite branching and fixed-point/pruning theory supply the methods; GenericOrdinalCertificate explicitly uses Mathlib ordinal ranks. The complete-blow-up projection is analyzed at the actual reachable-state interface rather than credited as new general rank theory.

**Our contribution and attribution.** The existing 29 September 2026 package formalizes the exact reachable-state criterion, the live/mortal dichotomy without global avoidance, and corresponding finite-height transport. It exposes the difference between the artificial history-tree superroot and actual matching-state heights, and between complete blow-ups and exact-parent terminal clones.

**Evidence, kept separate:**

- **Hand:** The complete generic scope and ordinal audits, publication correspondence audit and all five direct certificate/pruning/mortal/transport modules were read. The October 2 correction is retained rather than replacing it with the older AI-discovered metadata. No new whole-transitive proof acceptance or external human peer review is claimed.
- **Formal:** Five named modules have 8 generic-certificate, 3 ordinal-certificate, 10 pruning, 9 mortal-rank and 7 blow-up selected reports under Lean 4.33.1 and Mathlib 0df444a360eaa60ab8c11dca51a86af692955474. Raw logs report only standard axioms and saved receipts exit zero. Successful hosted audit uses the same selected proof blobs, including byte-identical reused originals. These 37 reports are supporting inventory, not separate discoveries; generic live-core transport and the combined host-obstruction corollary are not separately named formal endpoints.
- **Execution:** The recorded local Lean 4.33.1 receipts and raw selected-endpoint logs were read. Fresh read-only hosted metadata confirms run 36631876391 succeeded at 1592b89731d10fc49019ff22cf2f93c7bc799118; the actual workflow/audit contracts and identical selected proof blobs at recovery pin e2502c82 were checked. No compiler, build, scientific execution or new theorem validation occurred during this recovery.
- **Empirical:** An exact theorem in a stated infinite labelled-graph model. No measured biological data, validated species classifier or demonstrated population mechanism is asserted.

**Novelty:** The 2 October 2026, 19:34 UTC VibeMathed correction states that a distinct new theorem beyond source-specific classical formalization was not established and asks for eligibility reassessment. It does not allege an incorrect Lean proof, request withdrawal or remove verification. No mathematical novelty is asserted by this recovery.

**Separate downstream work (does not reopen this result):** Historical novelty and catalogue eligibility remain distinct assessments. A terminating algorithm for arbitrary infinite inputs, richer rank classification or a construction combining terminal cloning's exact-parent property with all-copy rank preservation would require different results; none is implied here. Missing formalization of the explicitly written auxiliary corollaries does not reopen their written mathematics.

**Proof, review and related source links:**

- [Generic finite certificate and attained height](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-questions/continuation-2026-09-29/formal/GenericCertificate.lean) (proof source).
- [Classical ordinal-certificate equivalence](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-questions/continuation-2026-09-29/formal/GenericOrdinalCertificate.lean) (proof source).
- [Exact surviving core](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-questions/continuation-2026-09-29/formal/GenericPruning.lean) (proof source).
- [Mortal-region least attained ranks](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-questions/continuation-2026-09-29/formal/GenericMortalRank.lean) (proof source).
- [Complete-blow-up finite-height transport](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-questions/continuation-2026-09-29/ordinal-audit/BlowUpRankInvariance.lean) (proof source).
- [Generic proof and definition scope review](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-questions/continuation-2026-09-29/literature/new-proof-scope-review.md) (hand review).
- [Ordinal/history distinction and transport audit](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-questions/continuation-2026-09-29/ordinal-audit/audit.md) (hand review).
- [Pinned seven-module source and compiler-log manifest](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/open-questions/continuation-2026-09-29/verification-manifest.json) (formal receipt).
- [Successful integrated hosted audit at 1592b897](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/actions/runs/36631876391) (formal receipt).
- [Source-question, statement and bounded prior-work audit](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/publication-audit-2026-09-29/alexander/CLAIM-EVIDENCE.md) (hand review).
- [October 2 classical-formalization novelty correction](https://vibemathed.com/problem/ordinal-certificates-and-exact-pruning-characterize-sequence-realization) (prior work).

**Typed connections:**

- [CB-ALEXANDER-002](#cb-alexander-002), same principle: The transport result accompanies the nonuniversality programme, but complete blow-ups and terminal clones have different preservation properties. Exact-parent terminal cloning is not asserted to preserve every copy's height.
- [CB-SEQ-004](#cb-seq-004), same principle: Concrete Thue–Morse height formulas and this generic certificate/core theorem concern related matching states but are not the same theorem or a claimed new dependency.

**Stable key:** alexander.MATCHING_CORE_RANK_TRANSPORT. **Aliases:** Samuel A02; Samuel A03.

</details>


<a id="cb-alexander-004"></a>
### Every organism belongs to a maximal cluster under a fixed founder window
**CB-ALEXANDER-004 · Alexander structures · fixed-window maximal clusters**

**Question:** Can a maximal ancestry cluster exist without requiring one common ancestor?

**What we learned:** Yes, under the stated graph and cluster conditions, a fixed real window containing all founder birthdates gives a complete existence theorem through every organism.

**What it lets someone do:** Replace a common-ancestor constraint with a precisely defined founding-window condition in this mathematical maximality problem.

**What we cannot conclude:** It does not produce a unique species partition, an algorithm for finding clusters or evidence that the condition is biologically adequate.

**Kind:** theorem. **Mathematical status:** Proved; archived Lean check recorded.

<details>
<summary>Exact scope, prior work, evidence and separate downstream work</summary>

**Exact statement and assumptions.** Let organism identifiers be Nat, with real birthdates, strictly chronological parent edges, finite strict real birth sublevels and finite children. Tied birthdates are allowed; identifiers need not be chronological and no finite-root premise is required. For a nonempty set S, founders are its members with no strict ancestor in S, not necessarily ambient roots, and m(S) is its attained earliest birthdate. Fix one real duration Δ. The admissible sets are nonempty, induced-undirected connected, ancestrally convex, satisfy IAP and reflection, and have every founder born by m(S)+Δ. IAP means each member has either finitely many descendants or finitely many non-descendants in S; reflection means every member with infinitely many ambient descendants has infinitely many descendants in S. Every admissible set extends to an inclusion-maximal set in this same class with the same Δ. For every Δ≥0 and every original organism v, such a maximal set containing v exists. The proof supplies the actual seed and transports all competitors back to the original graph and literal dates. This is constrained maximality, not maximality among all specieslike sets. The written coeval-two-founder example shows the window need not imply common ancestry; it is not a separately registered Lean endpoint.

**Origin.** published open problem. Alexander's Specieslike clusters based on identical ancestor points (2026), §6 immediately after Theorem 13, requests alternative sufficient constraints, particularly without common ancestry. This answers a precise mathematical subquestion, not the broader request for demonstrated biological plausibility.

**Prior work.** Alexander's common-ancestor/reflection existence theorem and seed method, together with classical Zorn and finite-branching arguments, retain attribution. The recovered extension substitutes a common real founder window while retaining reflection, convexity, IAP and explicit connectivity. Historical priority is not established by source recovery.

**Our contribution and attribution.** The existing 25 September 2026 human-directed Codex package proves the actual per-organism seed, finite-founder directed-union control and constrained maximal extension on the original real-birthdate graph, including ties and all same-window competitors. It is a complete theorem, not merely Zorn maximality conditional on an unproved seed.

**Evidence, kept separate:**

- **Hand:** The complete theorem note, all eight direct founder-window proof modules and later source-question/statement audit were read. The separate maximal-specieslike audit is used only to distinguish constrained from unrestricted maximality, not as a substitute for a new full founder-proof review. No new whole-transitive or human/external peer review is asserted.
- **Formal:** The 25 September frozen founder packet records eight modules and 50 selected endpoints with Lean 4.33.1, Mathlib 0df444a360eaa60ab8c11dca51a86af692955474 and only standard axioms. Its historical aggregate count 151 is superseded by the later 274-endpoint/61-module real audit; all eight source hashes and all 50 founder axiom lists match. The hosted manifest imports all eight modules and prints those endpoints, including RealSpeciesTheorem.every_vertex_in_maximal_real_window; all eight blobs are unchanged at the recovery pin. The written non-CA example is not an extra formal endpoint.
- **Execution:** The recorded local Lean 4.33.1 receipts and raw selected-endpoint logs were read. Fresh read-only hosted metadata confirms run 36631876391 succeeded at 1592b89731d10fc49019ff22cf2f93c7bc799118; the actual workflow/audit contracts and identical selected proof blobs at recovery pin e2502c82 were checked. No compiler, build, scientific execution or new theorem validation occurred during this recovery.
- **Empirical:** An exact theorem in a stated infinite labelled-graph model. No measured biological data, validated species classifier or demonstrated population mechanism is asserted.

**Novelty:** Unresolved for the exact fixed-window extension. Source correspondence, recorded formal checking and recovery do not establish worldwide novelty or biological applicability.

**Separate downstream work (does not reopen this result):** Unconstrained maximality, uniqueness, a species partition, an effective construction, arbitrary-carrier formal generalization and biological admission are outside this theorem. They must not be treated as missing premises of its already completed Nat-identifier, literal-real-date, same-window conclusion.

**Proof, review and related source links:**

- [Complete real founder-window theorem and boundaries](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/notes/REAL-FOUNDER-WINDOW-THEOREM.md) (proof or status).
- [Actual original-graph final theorem](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/real/RealSpeciesTheorem.lean) (proof source).
- [Actual per-organism seed construction](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/real/SpeciesSeed.lean) (proof source).
- [Directed-union IAP supplier](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/real/DirectedIAP.lean) (proof source).
- [Original dates, ties and founder-window predicates](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/real/RealFounderWindow.lean) (proof source).
- [Frozen eight-module and 50-endpoint founder receipt](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/verification/founder-window-packet.json) (formal receipt).
- [Later real-library audit retaining the founder theorem](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/verification/real-audit.json) (formal receipt).
- [Successful integrated hosted audit at 1592b897](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/actions/runs/36631876391) (formal receipt).
- [Source-question, statement and bounded prior-work audit](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/publication-audit-2026-09-29/alexander/CLAIM-EVIDENCE.md) (hand review).
- [Alexander's 2026 §6 non-common-ancestor question](https://arxiv.org/html/2602.05274v1#S6) (prior work).

**Typed connections:**

- [CB-GENOME-001](#cb-genome-001), same principle: Both use Alexander's future-inclusive ancestry vocabulary. The finite-graph observation obstruction does not prove or contradict this constrained infinite-cluster existence theorem.
- [CB-FEEDBACK-001](#cb-feedback-001), same principle: Recurrent-component IAP classification uses different source assumptions and does not duplicate fixed-window maximal-cluster existence.

**Stable key:** alexander.REAL_FOUNDER_WINDOW. **Aliases:** Samuel A04.

</details>


