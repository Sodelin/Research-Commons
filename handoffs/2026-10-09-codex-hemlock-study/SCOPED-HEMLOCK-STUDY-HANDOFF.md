# Scoped hemlock study: public-data replay, biological audit, and conditional history comparison

Prepared by dot, 9 October 2026. **Execution handoff, not completed empirical analysis.** This packet continues the existing reviewed hemlock milestones; it does not launch a duplicate study or replace the wider G1–G7, BIO-1, biological, cross-programme or meta-programme. Publication of this plan does not establish professor endorsement, a new biological finding, or novelty.

## 1. Decision and scientific question

Build a reproducible, modestly scoped study of the nuclear/plastid discordance investigated by Holman and colleagues, including Linda Raubeson, in *A New Species and Introgression in Eastern Asian Hemlocks (Pinaceae: Tsuga)* (2017). The first attainable outcome is an authenticated replay of the public evidence and an explicit audit of what historical inferences it can support. A model comparison follows only where its biological and statistical premises can be justified.

**Primary question:** How robust are the reported nuclear and plastid relationships to data provenance, specimen/paralog assignment, alignment, rooting, and inference choices, and do the available observations distinguish a declared incomplete-lineage-sorting explanation from a declared plastid-introgression explanation once gene-tree error and model inadequacy are considered?

Keep four conclusions separate: (1) discordance between marker trees; (2) evidence against a specified nonreticulating history; (3) evidence for plastid capture among the tested alternatives; (4) identifiable direction or timing. Success at an earlier level does not establish a later one. The authors already suggested putative capture; recovering their discordance is replication and clarification, not discovery of capture.

**Useful admissible final outcomes:** reproducible agreement or disagreement with the published trees; a localized data or assumption sensitivity; a calibrated preference among explicitly tested models; or a defensible finding that the public data cannot distinguish them, with a concrete additional-data specification. Do not promise a definitive capture answer.

## 2. Starting point and provenance

Use the existing project, code, raw records, manifests, and receipts rather than rewriting the pilot. Freeze the actual implementation commit used in a new run. This handoff reads the following at Commons commit `237d581526aaafa44a4b912b17922f6e05788c96`:

- [Reviewed empirical milestones](https://github.com/Sodelin/Research-Commons/blob/237d581526aaafa44a4b912b17922f6e05788c96/research/2026-10-08-codex-integration-0825z/g6/EMPIRICAL-INTEGRATION-MILESTONES.md), sections “What Holman and colleagues already established,” “Actual recoverable data,” and milestones 1–5. This is the governing inherited scientific plan.
- [Independent baseline and application review](https://github.com/Sodelin/Research-Commons/blob/237d581526aaafa44a4b912b17922f6e05788c96/research/2026-10-08-codex-integration-0825z/review/APPLICATION-AND-REAL-BASELINE-REVIEW.md), “Real public-marker baseline” and “Final application-map and empirical-plan review.” Its independent checks are static source/data/receipt authentication; its reviewer did not rerun the phylogenetic bootstrap.
- [Biological input contract](https://github.com/Sodelin/Research-Commons/blob/237d581526aaafa44a4b912b17922f6e05788c96/research/2026-10-09-codex-practical-release-0207z/biology/BIOLOGICAL-INPUTS.md) and [practical application](https://github.com/Sodelin/Research-Commons/blob/237d581526aaafa44a4b912b17922f6e05788c96/applications/practical-solver/README.md).
- [Original pilot manifest](https://github.com/Sodelin/Research-Commons/blob/237d581526aaafa44a4b912b17922f6e05788c96/research/2026-10-08-codex-integration-0825z/g6/REAL-BASELINE/MANIFEST.json), accession versions, extraction coordinates, voucher joins, raw hashes and processing recipe.

The existing pilot uses four paper-listed specimens, one 1,048-site 4CL1 alignment and one 1,428-site rbcL alignment. Its unrooted nuclear and plastid quartets disagree. The 100/100 and 93/100 column-bootstrap counts are descriptive marker support, not capture probabilities. It omits *T. ulleungensis*, outgroups and population replication. Its biological source status remains NOT_ADMITTED and capture UNKNOWN.

The inherited archive has 15 GenBank records, eight used by that pilot. The full Dryad deposit was inventoried, but saved download attempts failed; no full-deposit replay is established. The chinensis rbcL region is homology-inferred and unannotated in its deposited record. Existing authentication checks do not establish orthology or physical specimen identity.

## 3. Scope boundaries

- **In scope:** permitted public paper/deposit/sequence retrieval; public-data identity and biological-unit audit; replay and sensitivity analysis; explicit method-suitability assessment; justified, bounded simulation and model comparison; reproducible research outputs.
- **Outside this handoff:** wet-lab sampling, professor or author contact, private specimens or data, paid services, credentials, bypassing denied access, live AlphaGenome, downloads to Nolan’s computer, and new external teams. If needed, these require separate scope and authorization.
- Do not force these sequences into the fixed-six-copy, two-sites-per-locus, nine-parameter clock-JC/pulse solver. A tree, bootstrap proportion, quartet count or distance is not one of its exact joint feature laws. No ad hoc variable renaming supplies the missing bridge.
- Completing general G3/G4 is not required for a sound scoped hemlock study. Conversely, a successful hemlock analysis proves no general G3/G4 coverage or biological admission theorem.
- Preserve all inherited files and failed-retrieval receipts. New computations use fresh output directories. Separate raw public data terms from owned code licensing; do not relabel GenBank records as CC0 or Apache.

## 4. Work package A: acquire and authenticate the published evidence

### Governing sources

Holman et al. (2017), Systematic Botany 42:733–746, [DOI 10.1600/036364417X696474](https://doi.org/10.1600/036364417X696474); [public USDA paper](https://research.fs.usda.gov/download/treesearch/55598.pdf). The inherited complete-paper SHA256 is `81d19502fe93b40f68a8a673060670fad7e0588bb9bd186018004c372dae26ab`. Methods/results: pp.734–738; discussion: pp.738–741; accession/specimen joins: Appendices 1–2. The present handoff relies on the prior paper audit and independently reread Commons review, not a newly executed full-paper replication.

[Dryad DOI 10.5061/dryad.2r12j](https://datadryad.org/dataset/doi:10.5061/dryad.2r12j), inherited version 21609, inventories separate 4CL, concatenated 4CL, plastid alignments and morphology CSV. Inspect saved metadata and failures first. A currently documented public download route may be tested; record its exact route and status. Do not defeat authentication or access controls. If the same action is denied, pause and report the target/blocker. If a permitted public route cannot supply bytes, label the deposit unavailable and continue with the independently traceable GenBank reconstruction as a different dataset.

### Required retrieval ledger

For every asset record source URL, accession/version or deposit/file/version ID, retrieval date, HTTP/result status, byte length, SHA256, media type, reuse terms and citation. Compare deposit-provided checksums when available, preserving the checksum algorithm; do not claim source authentication from a new local hash alone. Match the inherited local manifest where applicable. Public mirror bytes need an explicit identity check or must be marked alternate versions.

Preserve raw GenBank records, qualifiers and accession versions; retain original and normalized taxon names. Establish a complete inventory before restricting the analysis. Include ulleungensis/Ulleungdo identities and the original outgroups where permitted data exist. Record absent clones, chromatograms, reads or vouchers rather than implying a sequence deposit contains them. Morphology is context and optional published-data replay; it does not automatically add independent evidence for a capture event.

**Gate A:** a machine-readable asset ledger and a paper-to-file/sample reconciliation reviewed by a second worker. Full replay requires the original alignment bytes or an explicitly documented equivalent source. Otherwise proceed only as a labelled reconstruction, with the missing scope listed.

## 5. Work package B: specimen, orthology and ancestry-unit audit

Create one row per observed sequence with at least:

`taxon_original, taxon_normalized, specimen/voucher, individual, locality_if_public, accession.version, clone/allele, paralog, compartment, genomic_region, extraction_coordinates/strand, source_alignment, missingness, ambiguity/phase, identity_evidence, unresolved_flags, proposed_ancestry_block`.

Keep uncertain joins as alternatives, not silently resolved values. Verify paper Appendix 1 accession ordering and voucher links against deposited qualifiers. Publication-level matching is evidence about provenance; physical specimen authentication remains outside this computational study.

Audit 4CL1 and 4CL2 as distinct paralogs. Check copy assignment, coding boundaries, translations where appropriate, duplication/loss and alignment plausibility, and whether clone sequences represent alleles, errors or duplicates. Document evidence and contrary evidence; similarity and an intact coding frame alone do not establish orthology. A nonsignificant incongruence test does not prove shared genealogy or independence. Analyze each paralog separately before any historical concatenation replay.

Retain the plastome as a linked compartment unless a defensible alternative recombination model is supported. Partitioning a plastome for substitution models or checking regional sensitivity does not create independent genealogies. Likewise, 10–16 sequenced PCR colonies are not 10–16 independent loci, and sites are not independent ancestry histories. The nuclear paralogs' genomic independence must be assessed rather than presumed.

Find and cite primary evidence for the relevant Tsuga/Pinaceae plastid transmission assumptions before assigning parental direction, ploidy, inheritance scalars or effective population-size relationships. Do not import an angiosperm maternal-inheritance convention. Unknown transmission or recombination premises remain explicit model alternatives or block directional inference.

**Gate B:** an independently reviewed ancestry-unit map classifies each proposed likelihood factor and resampling unit as justified, conditional or unresolved. No inferential procedure may count unresolved linked units as iid replicates. Missing biological premises may still permit descriptive tree replay.

## 6. Work package C: established phylogenetic baseline and sensitivity

First rerun the inherited small pilot and authenticate its inputs/results, clearly distinguishing saved receipts from newly executed commands. Do not call this full-paper replication.

For full data, reproduce the reported separate and concatenated nuclear analyses and whole-plastid analyses, preserving taxon/sample sets, roots and partitions. The inherited source audit records nuclear HKY+I and plastid GTR+Γ4, with 1,000 original bootstrap replicates, nuclear canadensis rooting and plastid Nothotsuga rooting. Check the primary methods before execution. Original software includes MAFFT, PAUP*, jModelTest and GARLI. Use existing licensed/available versions for exact replay where feasible; otherwise use a documented established replacement and label a methodological reproduction. Do not acquire paid software or silently substitute a different method.

Predeclare a small, scientifically motivated sensitivity grid before new runs: each paralog versus historical concatenation; original versus reconstructed alignment; defensible ambiguous-site treatment; original versus justified alternative substitution/partition models; outgroup/root sensitivity; and plausible accession/copy assignments unresolved at Gate B. Include only meaningful comparisons and preserve all outcomes. Because original outcomes are already known, this is prospective analysis planning for new comparisons, not retrospective preregistration of the old pilot.

Report splits/topologies, branch lengths in their actual units, support measures and conflicting signals. Record random seeds, search starts, optimization failures, convergence and resource use. Bootstrap support addresses the resampling/model procedure used. Do not report it as confidence in capture or species-history direction. For a linked plastome, column resampling can be a conditional phylogenetic diagnostic without providing independent historical replication.

**Gate C:** a second worker verifies taxon and alignment identities and reruns at least one representative analysis or an explicitly justified bounded check. Every reported relationship is linked to a run. Disagreement with the paper is investigated and reported, not filtered away. A descriptive scientific report can finish here if later gates fail.

## 7. Work package D: select a compatible history model before fitting

Write a model contract before empirical fitting. It must state biological units, sequence/gene-tree input, sample mapping, inheritance, population sizes, substitution process, linkage/recombination, nuisance parameters, root, observation error, priors or optimization constraints, and the exact quantity being compared. No tool is selected merely because it outputs a network.

Candidate comparisons, subject to Gate B:

1. **ILS model:** a declared bifurcating population/species history with incomplete lineage sorting and separately justified nuclear and plastid inheritance/size treatment.
2. **Capture candidate:** the same comparable background with a specified plastid introgression history or mechanistic compartment model. Explain whether any nuclear contribution is represented. A generic nuclear network edge is not automatically a plastid-capture process.
3. **Additional historical alternatives:** older caroliniana introgression or unsampled ancestral lineage only if identifiable enough to fit meaningfully or useful as an explicit sensitivity model.
4. **Observation/model-error alternatives:** paralog misassignment, uncertain phase/clone calls, alignment error, substitution-rate/model heterogeneity and gene-tree uncertainty. These may modify each historical model rather than form one mutually exclusive “error model.”

Use established implementations where they actually meet the contract. Two candidate interfaces to inspect are:

- [BPP documentation](https://bpp.github.io/bpp-manual/bpp-4-manual/): MSC/MSci sequence-based analysis. Its documented no-within-locus/free-between-locus recombination assumptions must be checked against these data. Species assignments, priors and compartment treatment need an explicit audit; availability of an introgression option does not establish plastid suitability.
- [SNaQ official documentation](https://juliaphylo.github.io/SNaQ.jl/stable/) and [network-estimation interface](https://juliaphylo.github.io/SNaQ.jl/dev/man/snaq_est/): network estimation from quartet concordance factors. It is a candidate only when a defensible multilocus input and its gene-tree uncertainty exist. Two paralogs plus one linked plastid history do not by themselves justify a large empirical concordance-factor sample.

These are suitability candidates, not required installations or endorsed choices for the current data. Pin chosen versions, read their primary method papers, and record a feature/assumption matrix before running them. Prefer the smallest established method that answers the admitted question. Do not invent an unvalidated joint compartment likelihood to complete the handoff.

Compare methods only on clearly specified overlapping questions and observations. Pseudolikelihood scores, likelihoods and posterior probabilities have different meanings and cannot be ranked across incompatible data/model definitions. If a compartment-compatible joint method is unavailable, report separate analyses and their limitation; do not multiply unrelated support values into capture confidence.

**Gate D:** independent review accepts a concrete model–data–implementation match. Otherwise deliver MODEL_NOT_ADMITTED with the missing premise and retain the completed replay/audit. Additional public independent loci may be inventoried as a future extension, with a frozen prospective selection rule; silently extending the dataset after seeing results is prohibited.

## 8. Work package E: uncertainty, validation and decision calibration

Before fitting, fix the primary comparisons, nuisance sensitivity ranges supported by evidence, exclusion rules, resource budget, seeds, and the claims each statistic can support. Data insufficiency must remain a possible final answer. Time limits or failure to find an alternative are not evidence against it.

- Propagate gene-tree, alignment, specimen/copy and phase uncertainty by an appropriate integrated method or explicit sensitivity set. Label conditional analyses when some uncertainty is held fixed.
- Use biological ancestry blocks for between-locus resampling. Do not use the number of plastid sites as the effective count of independent histories. Keep numerical Monte Carlo error separate from biological sampling uncertainty.
- For Bayesian work, report priors and prior sensitivity, independent chains, convergence and effective sampling diagnostics. For likelihood/search work, use multiple starts and retained competing optima. A well-converged computation can still fit an inadequate or unidentifiable model.
- Test model adequacy using prespecified relevant summaries and simulation/predictive diagnostics, including the pattern being explained. Avoid declaring a favored model adequate merely because it outperforms another inadequate model.
- Calibrate any proposed historical decision rule under both the ILS and capture candidates and under plausible error/misspecification scenarios, matching sample sizes, linkage, missingness and preprocessing. Rerun selection/fitting in the simulations where those steps contribute to the statistic. Do not use a default chi-square likelihood-ratio threshold at a boundary without justification.
- Predeclare a finite simulation design and target Monte Carlo precision. If a binary rule is assessed, report its binomial uncertainty, false-positive frequency under each tested null setting and detection frequency under each tested alternative setting. A nominal 5% rule requires justified calibration; failure to demonstrate that target means no calibrated 5% claim. Finite scenarios do not establish uniform validity over an untested parameter space.
- If information supports only a prior-sensitive preference or overlapping predictive distributions, report that. Do not select a capture direction or calendar date without identifiability and a supported timing calibration.

**Gate E:** the claimed inference survives its declared adequacy, numerical and calibration checks, or is downgraded to an explicitly conditional/exploratory result. A failed gate is a research result about limitations, not permission to omit uncertainty. No positive capture claim is a required deliverable.

## 9. Execution, stopping rules and outputs

Use the existing authorized Codex workspace, installed approved tools and existing public application where useful. Downloads belong in its separate research working directory, never on Nolan’s computer. Record dependencies; do not bundle third-party binaries or data without appropriate rights. Official software setup, paid tools, access grants or other new actions outside existing authorization must be escalated, not assumed from this plan. No external contact is part of execution.

Preserve raw data and all existing evidence. Every run produces a command/configuration, source and dependency pin, input hashes, random seeds, stdout/stderr, exit status, start/end time, resource limits and result manifest. A failure has its own receipt and cannot reuse a historical successful status. Reviewer checks must distinguish static inspection, arithmetic checks, actual reruns and biological assumption review.

Stop or narrow a dependent phase when: original files remain unavailable; identity/orthology cannot be resolved enough for its claim; no justified ancestry-unit map exists; a required compartment model is unsupported; numerical diagnostics fail within the declared budget; or alternatives remain indistinguishable. Continue unaffected replay/audit work. Specify the missing evidence or next experiment, with no unsupported numerical sample-size guarantee. Do not perform wet-lab work or keep adding loci/models until a favored result appears.

### Required study deliverables

1. **STUDY-STATUS.md:** question, current stage, completed/blocked gates, exact supported claims, next decision.
2. **SOURCE-AND-SPECIMEN-LEDGER.tsv/json:** public asset/identity/terms records, uncertainty flags, ancestry-unit map and missing files.
3. **REPLAY-AND-SENSITIVITY.md:** original versus new processing, tree comparisons, all planned sensitivities and deviations, source-linked figures and run receipts.
4. **MODEL-ADMISSIBILITY.md:** candidate model contracts, method/version/source comparison, reasons for admission or refusal. Preserve the nine-parameter solver's NOT_ADMITTED boundary.
5. **VALIDATION-PLAN.md** fixed before new model results, followed by **VALIDATION-RESULTS.md** only for actual executions, with calibration limits and all failures.
6. **SCIENTIFIC-SUMMARY.md:** short researcher-readable account, compatible explanations, what changed relative to Holman et al., unresolved direction/timing and the highest-value missing evidence. A summary “for Linda Raubeson” is a prepared deliverable, not a sent communication or implied collaboration.
7. **REPRODUCE.md**, source code/configuration deltas, manifest and independent review. Use existing scripts where possible; no duplicate workbench or solver.

Code/tests/receipt success establishes computational reproducibility within scope. It does not by itself establish biological model validity. A useful reviewed scoped report is sufficient completion even when MODEL_NOT_ADMITTED or INCONCLUSIVE remains the historical verdict.

## 10. Reallocate the existing six Codex workers; do not create more

The Codex coordinator should reconcile its current responsibilities and assign its **existing** six slots to: (1) public evidence retrieval/provenance; (2) specimen/paralog/linkage audit; (3) published baseline and sensitivity replay; (4) model and implementation suitability; (5) statistical validation/calibration design and admitted runs; (6) integration, reproducibility and independent review. Preserve broader programme records and explicitly hand off any displaced active obligations. These are work packages, not permission to spawn six additional agents.

Start with A/B and inherited-pilot replay in parallel; D can examine method contracts while waiting, but empirical fitting depends on B/D. E may design simulations before fitting, but its scientific parameterization must have a justified model. The integration reviewer must not approve their own code or analyses: use cross-review from another existing slot for those contributions. Escalate unresolved biological interpretation rather than declaring it settled by code review.

**First handback:** authenticated inventory, biological-unit ledger, replay availability report, and a model-admissibility recommendation. This is the decisive checkpoint for whether existing public data can support a substantive comparison. It prevents an attractive new interface from outrunning the evidence.

## 11. Attribution and verification status

The scientific question, prior capture suggestion and published relationships belong to Holman and colleagues. The original pilot, review, milestones and application were authored in the existing Codex programme. This handoff reorganizes that accepted plan into explicit execution and decision gates; it claims no new method, no novel empirical finding and no full formal verification. BPP and SNaQ are established external methods with their own sources, assumptions and licences.

Preparation of this handoff independently reread the pinned Commons milestone and baseline-review documents and inspected current official BPP/SNaQ interface documentation. No new sequence download, alignment, tree search, bootstrap, model fit or simulation was performed to prepare it. Publication and the Codex handoff are owned by the parent coordinator. External communication remains outside this packet.
