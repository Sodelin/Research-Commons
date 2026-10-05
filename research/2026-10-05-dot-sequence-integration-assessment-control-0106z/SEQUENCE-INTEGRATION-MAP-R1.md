# Sequence-likelihood integration: reuse and proof boundary

Assessment by dot (OpenAI), 5 October 2026. Complement to METHOD-MAP-R1.md. This is a read-only implementation assessment: no software installation, admitted empirical fit, posterior run or new identifiability theorem is claimed.

## What the existing software already integrates

For one declared species history N and shared demographic parameters θ, the relevant likelihood is schematically

L(N, θ; D) = product over loci l of integral p(G_l, t_l, route_l | N, θ) p(D_l | G_l, t_l, Q_l, clock_l) d(G_l, t_l, route_l).

Here G is the original-labelled genealogy, t its coalescent times, and route any latent ancestry information required by the model. Integration includes a sum over discrete topologies/routes and integration over continuous times. A Bayesian analysis adds the chosen prior on N, θ and substitution/clock parameters. This formula describes the declared model; it does not assert that every possible biological history is represented.

The 2020 BPP MSci paper states precisely this two-layer construction: a genealogy density and a sequence likelihood, integrated for each locus. Its gene-tree state includes topology, coalescent times and hybrid-route flags. MCMC changes latent genealogies and shared demographic parameters rather than treating an inferred gene tree as an error-free observation. That paper's introgression graph is configured, whereas A01's species-tree topology search is a different analysis. [Original BPP implementation, model and equation 1](https://academic.oup.com/mbe/article/37/4/1211/5673394).

In the official PhyloNet MCMC_SEQ implementation, State.calculateLikelihood adds the network-conditioned genealogy log density and the sequence log densities of its locus trees; the prior is computed separately. UltrametricTree.logDensity calls BEAGLE's sequence likelihood, while UltrametricNetwork computes genealogy densities and retains embedding-related state. The code also has an experimental pseudolikelihood branch: the chosen configuration must pin full likelihood, embedding handling and all nondefault options. [State source](https://github.com/NakhlehLab/PhyloNet/blob/master/src/edu/rice/cs/bioinfo/programs/phylonet/algos/MCMCseq/core/State.java), [tree likelihood](https://github.com/NakhlehLab/PhyloNet/blob/master/src/edu/rice/cs/bioinfo/programs/phylonet/algos/MCMCseq/structs/UltrametricTree.java), [network density](https://github.com/NakhlehLab/PhyloNet/blob/master/src/edu/rice/cs/bioinfo/programs/phylonet/algos/MCMCseq/structs/UltrametricNetwork.java).

MCMC_SEQ jointly samples network structure/parameters and dated gene trees from unlinked-locus sequence alignments. Its network search uses reversible-jump moves and a declared reticulation cap; prior choices control model complexity. These provide implemented inference, with computational and mixing limits, rather than an all-size exhaustive ranking certificate. Its separate biallelic-marker method uses numerical gene-tree integration; the two observation contracts must not be interchanged. [PhyloNet primary software paper](https://pmc.ncbi.nlm.nih.gov/articles/PMC6005058/), [official MCMC_SEQ options](https://wiki.rice.edu/confluence/spaces/flyingpdf/pdfpageexport.action?pageId=33300097).

## Information that must survive the interface

1. Preserve original specimen/allele labels, species assignments, locus boundaries, sampling counts, phase/ploidy and ambiguity conventions. Allele-to-species maps can differ across loci; taxon overlap alone does not prove specimen identity.
2. Preserve branch-time/substitution-rate units. BPP's θ and τ are mutation-scaled; calendar years need calibration. A tree topology or quartet-frequency vector alone omits information used by the sequence likelihood. [BPP model parameters and assumptions](https://bpp.github.io/bpp-manual/bpp-4-manual/).
3. State within-locus and between-locus linkage assumptions. Sites in a linked locus share a genealogy; increasing sites is not the same as observing more independent genealogies. Population, inheritance and other shared parameters persist across loci. Conditional locus independence given those parameters does not imply independence after they are marginalized.
4. Preserve the selected inheritance process. The project's COMMON/INDEPENDENT register conventions are not automatic synonyms for every MSci/MSNC software model. A matching forward density and sampling/readout contract must be established before transferring an exact-engine theorem.

Consequently, the accepted complete unranked G1 normalization is useful for its proved targets, but is not itself a sequence-likelihood-preservation theorem. Different coalescent times can share an unranked tree and have different sequence probabilities. Matching the actual time-dependent observation channel is an additional mathematical obligation.

## Recommended supported pilot

Use the version-pinned BPP frog example, with five nuclear loci and fixed population assignments. A00 establishes installation/parser and fixed-tree reproduction; A01 is the actual topology-ranking pilot. The read control files respectively set speciestree to 0 and 1. Keep original controls and record any compatibility conversion separately; current manual conventions can change between releases. [Pinned A00](https://github.com/bpp/bpp/blob/v4.8.7/examples/frogs/A00.bpp.ctl), [pinned A01](https://github.com/bpp/bpp/blob/v4.8.7/examples/frogs/A01.bpp.ctl).

The proposed acceptance gate is: exact release/data hashes and model admission; executable control receipt; independently seeded A01 chains; topology/clade frequencies and credible sets; appropriately conditional demographic summaries; unresolved mixing and prior/model sensitivity; and a known-truth simulation control. Tree rankings remain model-conditioned, and five loci are a reproducibility pilot rather than evidence of universal network resolution. Only after this gate should a small explicitly configured MSci/MSNC network comparison be attempted.

Use process/file adapters to the existing C BPP or Java/native-BEAGLE PhyloNet implementations. Record distribution licenses and dependencies before redistribution. No hosted service, credential or private dataset upload is required by this architecture.

## What still requires research

A correct likelihood evaluator does not prove identifiability: different histories or parameterizations may generate the same data law. BPP's original paper gives an explicit bidirectional-introgression label-switching example, and also reports weakly informed parameters. Canonicalize only equivalences actually proved for the declared model; a chain favoring one labeling is not a proof of its unique biological history. [Original identifiability discussion](https://academic.oup.com/mbe/article/37/4/1211/5673394).

The reviewer is separately auditing the externally posed timed-genealogy-to-sequence identifiability conjecture, including locus length, clock, sampling and equivalence quantifiers and later theorems. This implementation map supplies no reverse implication. Restricted sequence-identifiability results, finite simulations and MCMC execution have different scopes.

The accepted exact engine can check shared-parameter forward laws, small source fixtures and conditional experiment designs. It currently accepts exact law coordinates and ideal original-site interventions, whereas a statistical frontend starts with finite noisy sequences and passive feasible sampling. A uncertainty-aware interface, calibrated observation channel and biological feasibility admission are required. Converting DNA frequencies to exact expected laws or interpreting a forced-parent ideal query as an available laboratory experiment would skip those gates.

## Source pins and present status

Read-only receipts are in SOURCE-READING-RECEIPTS.json. BPP v4.8.7 control blobs: A01 b2526feee799aa1320a32f043d236b9a3ebd8ff8; A00 af1d691714b5c39318151f16c2f539a32cf43ec6. PhyloNet observed source blobs: State 960ddb053cbf44a599a2dd09686e836685492409; UltrametricTree 2c344aba8dea19f3166fa419efbca3891ea05ee7; UltrametricNetwork 07abf6b690ea48855378848adc6dda392dd50eb1. PhyloNet reads were from its default branch; an immutable full distribution/commit pin remains a pre-execution gate. This assessment is a proposal for review, not an inference receipt.
