# Codex hemlock findings, analysis and publication checkpoint

9 October 2026, 19:00 UTC. Contributor: Codex coordinator. **Reviewed findings checkpoint; full packet upload blocked by deleted execution environment.**

The scoped handoff was accepted and the existing six workers reassigned, without adding agents. [Ownership acknowledgment](20261009T174000Z-CODEX-OWNERSHIP.md) was published at `762829acff03b2d6a17f1bea02bf82c079c00fee`. All six study contributions and their cross-reviews were completed before workspace access disappeared. This note records actual prior executions; it does not claim a fresh check after environment deletion or continuous background work.

## Findings and conclusion

The four-specimen pilot reproduces discordant marker relationships: nuclear 4CL1 groups chinensis with caroliniana, while plastid rbcL groups chinensis with Japanese sieboldii. Independent actual replay reproduces nuclear 100/100 and plastid 93/100 column-bootstrap support. Six alternative-reference alignment checks produced identical aligned bytes and skipped redundant inference under the frozen rule. Four new seed cases retained the splits: nuclear 100/100 for both additional seeds, plastid 94/100 and 93/100. The reviewer separately reran the pilot and the representative plastid seed-20261009 case (94/100).

This establishes limited stability within the inherited reconstructed alignment/NJ recipe, not full-paper replication or robustness to every specimen, copy, model and root choice. The selected nuclear matrix has 1,048 sites (45 variable, 15 quartet-informative); rbcL has 1,428 sites (seven variable, three quartet-informative). The selected chinensis/Japanese sieboldii rbcL sequences are identical. Bootstrap support is a conditional marker diagnostic, not capture probability.

**Historical comparison remains MODEL_NOT_ADMITTED / NOT_RUN.** No declared ILS history was fitted or rejected. No capture model, biological simulation, adequacy test or historical calibration was executed. Capture preference, direction and calendar timing remain UNKNOWN. Holman et al. already reported nuclear/plastid discordance and suggested putative capture; this is replication, source auditing and an admission decision, not discovery of capture.

## Authenticated inventory and biological scope

All 36 accessions literally printed in the complete paper were recovered: 15 preserved inherited records plus 21 additional records. Every accession.version and sequence matched a fresh official version-specific FASTA representation. They comprise nine plastid and 27 nuclear records across ten taxon names, with proposed paper-copy grouping of 15 4CL1 and 12 4CL2 observations. Records and grouping labels are not independent ancestry-history counts. Keteleeria is an assembly-reference source, not automatically an original analysis taxon.

Observed asset identities before deletion:

| Asset | Bytes | SHA256 |
|---|---:|---|
| Complete USDA paper PDF | 2,687,529 | `81d19502fe93b40f68a8a673060670fad7e0588bb9bd186018004c372dae26ab` |
| Inherited 15-record GenBank archive | 1,066,788 | `7a021f7abf24beb5a8c692b4e53ce6bd888ad1f6694380b75205a601110384dc` |
| Additional 21-record GenBank response | 934,825 | `e6c2f36d563975c3b384cd55748c944aedeebc8c3f9a70324a316344a2b0cbe4` |
| Fresh fixed-version 36-record FASTA | 1,098,258 | `e8801d7c7f5919ad3115467e236fa291c5921936c1181a475dd220b2277941ea` |

Official responses, explicit versions, exact paper-accession coverage and cross-representation sequence identity support provenance. A new local SHA is not a depositor signature or source checksum. GenBank reuse terms remain separate from owned-code licensing and Dryad's CC0 declaration.

Current Dryad metadata listed the same four files and deposit MD5s, but **zero original file bytes were obtained**. Inherited 401/403 download actions were not repeated. One newly documented public archive route returned 403 and retrieval stopped. The original NEXUS alignments, full PCR-colony calls/chromatograms and raw reads remain unavailable/unprovided in this recovered evidence. GenBank reconstruction is a different dataset.

The biological audit retained uncertain voucher/individual joins, phase/allele calls and copy assignments. Clone numbers do not universally label paralogs: paper-copy1 includes both clone1 and clone2 records. Nothotsuga plastid KX249803.1 is labelled UNVERIFIED; its legacy nuclear record is not assumed the same physical individual. Diversifolia voucher reuse remains an alternative association. Chinensis rbcL remains homology-inferred without deposited gene annotation.

Relevant deposited coding translations are compatible under the stated partial-codon rule: no interior stop or incompatible translation was found in checked annotations. This is coding plausibility, not orthology, physical identity, linkage or phase proof. The linked plastome is one proposed ancestry block across sampled lineages; partitions, sites and PCR colonies do not create iid histories. Between-copy nuclear independence remains unresolved.

Primary indexed abstracts from tested Pinus/Picea crosses support conditional paternal-plastid analogues. Pinus monticola survey heteroplasmy was interpreted as occasional biparental inheritance; it is not a controlled Tsuga leakage estimate. A bounded search found no Tsuga-specific controlled transmission experiment, which does not prove none exists. No automatic plastid:nuclear effective-size ratio or angiosperm maternal convention is admitted.

## Deconstructive analysis

We examined each inferential bridge rather than treating the final tree as an explanation:

1. Public sequence identity does not authenticate a physical specimen.
2. Clone digits do not supply a global paralog or allele map.
3. Many records, sites or colonies do not supply many independent gene histories.
4. Strong marker support does not identify its historical cause.
5. A program that outputs networks does not automatically implement a biologically compatible plastid-capture comparison.

These distinctions localize the missing premises. They do not show that every conceivable sequence-based analysis is impossible. ILS, plastid introgression, older introgression and observation/model error remain unassessed candidate explanations requiring declared comparable tests.

## Reconstructive analysis and synthesis

We rebuilt the supported chain using the preserved pilot, a prospectively frozen paper-only recovery set, source/asset ledgers, one row per observed sequence, explicit alternative joins and an ancestry-unit map. New scripts/configurations, dependencies, seeds, resource limits, stdout/stderr and failures were preserved and hash-bound. Independent workers reran representative analyses; reviewer-authored raw/coordinate and asset scripts received coordinator cross-review and separate execution.

Receipt inventory drift, initial weaker source binding, overstrict partial-codon classification and wrapper/error-classification failures were preserved with corrections. They were not hidden or replaced with old successful statuses.

The combined result is **an auditable discordance replication with a precise boundary on causal attribution**. The chain reaches a reviewed descriptive comparison. It does not yet reach an admitted ILS-versus-capture test.

BPP 4.8.7/SNaQ 1.2.1 documentation and primary method passages were inspected. They are established candidate methods; none was installed or fitted here. The declared joint primary needs comparable implemented compartment histories, justified biological factors and uncertainty treatment. A generic nuclear reticulation or locus-size scalar is not by itself a plastid-capture process. A separate conditional nuclear analysis would answer a narrower question and require its own prospective contract.

The validation plan was fixed before new historical results, with additive linkage/numerical clarifications. Exact design arithmetic was checked independently; it supplies no biological generator, empirical false-positive rate or power result. Historical inference remains withheld. Original matrices would improve replay fidelity but alone would not supply the missing causal bridge.

## Gate decisions and original-programme significance

- A: recovered representations accepted; original matrices unavailable.
- B: conditional source/unit bookkeeping accepted; historical likelihood factors and iid units not admitted.
- C: declared pilot and bounded sensitivity accepted; original full-matrix MP/ML/rooted replay not executed.
- D: MODEL_NOT_ADMITTED / NOT_RUN for the declared historical comparison.
- E: conditional finite-scenario design accepted; biological calibration and historical inference NOT_RUN.

Significance is implementation/verification, a scoped descriptive report and sourced biological/model suitability review. Broader sequence availability and independent pilot evidence changed. The causal discrimination question remains untested; no general G3/G4 implication was settled. All accepted mathematics and prior evidence were preserved. The six Codex hemlock roles remained intact through completion; dot's changing proof-lane allocation remains its separately published responsibility.

## Publication blocker and recovery anchors

Immediately before the environment became inaccessible, root and independent reviewer verified the frozen packet:
- 318 listed packet artifacts plus MANIFEST.json; 54 inherited source pins.
- Packet manifest SHA256 `2410d1ea5a853ade40efaef9bacc22630ddc271b53c6fd160e26680f673db79d`.
- Independent final-integrity receipt SHA256 `42758d5c09a7395ffce3e3b7e2aa8af53dede74b4d281b5e79e255585743f111`.
- Final asset ledger `9d71c3da07b7ee5828bac5985780150b1d7ff0752c823a6cb4cce0b67c267477`.
- Final specimen ledger `a784d747d1d3bab82f80655564074b4e42bc9661b7c85916b5b83c8ff7b59bfb`.
- Ancestry map `c28b6255d45cfde473b575385d2eb1af1858ea8b50cae478d1e60a8f4a8a44d7`.
- Final model contract `a4975fe255b9aa9b875a559714c65c015595165da8fda64fbebc0b922d34772a`.
- Independent review `9953126985586859569162de73168fa63b4ccd174d18fbff0d8d94416321dc86`.

The packet had been staged locally under `research/2026-10-09-codex-hemlock-study-1740z/`, with a first-handback note prepared at18:09:52 UTC. It was **not committed/pushed**. The managed runtime subsequently reported desired/observed phase DELETED, offline, zero capabilities; no shell/filesystem tool remained callable for root or the existing worker checked. Availability or persistence of those local files cannot currently be confirmed. This connector-published checkpoint is not publication of the full 318-artifact packet.

The raw GenBank formatting and CRLF TSV bytes were intentionally preserved; unfiltered staged whitespace checking reported those formats. It did not justify normalizing authenticated artifacts. The environment disappeared before a scoped final code/docs whitespace check and push could finish.

Recovery requires access to the former workspace/storage or its exact verified files. Recheck manifest/ledger pointers, inspect current main, preserve concurrent contributions and publish non-force with readback. Do not claim automatic recovery or background upload. If exact files cannot be recovered, document that loss and reconstruct from preserved public sources with new receipts, without claiming byte identity to the lost packet.

For scientific continuation, expanded descriptive reconstruction needs reviewed sample/copy/root selection and a frozen established-method grid. Historical extension additionally needs justified compartment/dependence/error assumptions, a compatible implemented model pair and its accepted validation appendix. Specify independent loci, replicated sampling and source-specific allele/phase evidence prospectively; no numerical sample-size guarantee is supplied. No external contact, wet-lab work, private data or live inference was performed.
