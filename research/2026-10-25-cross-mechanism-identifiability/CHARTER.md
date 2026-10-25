# Which demographic mechanisms do evolutionary observations identify?

Proposed research charter, 25 October 2026. Formulated by dot (OpenAI) following Nolan Downard's request for a broader, application-relevant and openly auditable biological question. Not a solved problem or a novelty claim.

## Master question

For arbitrary finite labelled taxa and sample panels, which claims about introgression, migration and ancestral subdivision are determined by observations **across competing demographic families**, rather than only within a chosen fitted model?

The baseline model union contains finite structured-Kingman histories with unknown finite numbers of demes and epochs, positive finite coalescence rates, positive finite rates on admitted migration edges, and independent per-lineage pulse routing. Missing migration edges have structural zero rates. Every migration model has finite rates and positive-duration intervals; infinite-rate limits are not admitted migration models. Hybrid histories are included. “Ancestral subdivision” requires a declared partition and time-relative communication restriction; it is not automatically disjoint from gene flow.

Compare four explicitly distinct observation levels: unmarked timed genealogies; topology laws; finite sequences under a declared mutation model; and linked-locus observations under an explicit recombination model. Sampling times, copy numbers, phasing and calibration assumptions must match across rivals. A clock, known architecture or independent loci cannot enter silently.

The full deliverable is a constructive characterization of exact observation-equivalence classes and of the mechanism properties constant on those classes, together with finite-data discrimination guarantees or impossibility results. Sample/sequence/linkage costs require stated separation conditions. Fixed-taxon examples are components, not completion. Unknown model size introduces realization/termination barriers related to G3; a finite candidate comparison does not remove them.

## Strongest source connections

- [Lohse–Frantz 2014](https://academic.oup.com/genetics/article/196/4/1241/5935635) distinguish specified admixture/ancestral-structure models using full block information. This is not classification against arbitrary demographic alternatives.
- [Theunert–Slatkin 2017](https://academic.oup.com/gbe/article/9/3/427/2982377) show summary-statistic confounding and useful additional statistics, while explicitly leaving intermediate models unexplored.
- [Cousins–Scally–Durbin 2025](https://doi.org/10.1038/s41588-025-02117-1) exploit adjacent coalescence information but retain model restrictions and population-size identifiability limits.
- [Collier–Gravel–Ragsdale 2026 preprint](https://pubmed.ncbi.nlm.nih.gov/41993441/) uses ancient unphased genomes and two-locus information, and explicitly identifies restricted model-space exploration as an unresolved limitation.

Known IICR confounding and extended-duration admixture are antecedents, not new discoveries. Exact theorem hypotheses and singular-limit prior work remain review gates.

## First component: bounded internal manual review

For any finite sample size and finitely many separated directional independent pulses, replace each pulse by a shrinking finite-rate migration interval. A coupling gives convergence in total variation of full **unmarked** timed-genealogy laws, with an explicit bound proportional to lineage-pair count and total window width. If these replacements include every nontrivial stochastic pulse relevant to the tested predicate and the unchanged remainder contains none, the alternatives are pulse-free. Without a uniform migration-rate cap or a minimum-duration/separation assumption, the proved fixed finite panels, independent-locus collections and common readout kernels then cannot uniformly certify pulse necessity. This uses classical TV continuity/testing principles, not a new statistical theorem. The coordinator manually reviewed the coupling under its stated hypotheses. Six floating-point endpoint controls were executed; external independent review and historical novelty remain unresolved.

This does not prove exact equivalence, settle ancestral-subdivision-only alternatives, or classify linked-locus laws. Existing project finite-epoch alignment results explicitly exclude continuous migration; this component targets that boundary without reopening their accepted scope.

## Open-science deliverables

Publish precise assumptions, attributed source comparisons, proof attempts, counterexamples, negative results and reproducible controls. Keep correctness, novelty, formal checking, executed validation and empirical evidence separate. No new biological data analysis or unrestricted identification claim is presently supported.
