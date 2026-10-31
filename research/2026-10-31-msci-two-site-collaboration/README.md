# What two-site sequence data can say about a fixed introgression model

**Working research note, 31 October 2026.** This manuscript-style overview describes an existing AI-assisted hand-proof research package and invites expert review and collaboration. The full result has not been independently reviewed or completely verified in Lean. A human author list, contribution statement and license for a later archival edition remain to be determined.

## The question

Genomes can contain evidence of populations exchanging ancestry in the past, but different histories can sometimes produce the same observable data. This work asks a narrower mathematical question: if the shape and direction of a particular three-population history are already known, can its numerical parameters be distinguished from the exact distribution of very short sequence observations?

The retained arguments say yes for one specified model. They use nine expected statistics calculated from **two sites per locus** in six labeled sequences. The conclusion concerns the ideal probability distribution across independent loci; it does not say that two sites at a single locus are enough to estimate a history reliably.

## Model and proposed results

The model fixes the population backbone `((A,B),C)` and one instantaneous pulse that sends ancestral lineages from B to C when traced backward in time. Its event times satisfy `0 < h < t1 < t0`; it also has five positive finite population coalescence rates and one pulse probability strictly between zero and one. Each of A, B and C supplies two contemporaneous, phased, labeled haploid samples. At the pulse, each current B lineage block makes an independent routing choice; lineages that have already merged travel as one block. The B population's rate is tied across its two sides of the pulse, and the C rate is separately tied across its sides; B and C need not have equal rates.

The sequence model uses a known, stationary, homogeneous Jukes–Cantor clock. The two homologous sites at a locus share one genealogy and evolve independently conditional on that genealogy. Distinct loci are independent replicates under the same parameters. These are assumptions of the mathematical model, not facts established for a particular dataset.

For a selected sample pair `XY`, write `T_XY` for its coalescence age in mutation-scaled time and `m_XY(k) = E[exp(-(8/3) k T_XY)]` for `k = 1, 2`. The selected feature vector is `(AC1, AC2, CC1, BC1, BC2, AB1, AB2, AA1, BB1)`, where `XYk` denotes `m_XY(k)` and within-taxon pairs use the two samples from that taxon. The sequence observation construction relates these quantities to expected products of site characters under the stated clock and shared-genealogy assumptions.

Within this scope, the retained hand proofs present three distinct conclusions:

1. **Global identification.** Equality of the nine selected exact pair-character expectations implies equality of all nine model parameters. Consequently, equality of the full two-site locus distributions implies equality of those parameters, provided the stated process and observation correspondence holds.
2. **Local behavior.** The Jacobian of the nine features is nonsingular throughout the stated strict parameter domain, including where rates coincide. This does not give a uniform conditioning bound near the domain boundary.
3. **Conditional interval inclusion.** With the specified derivative enclosures, outward interval arithmetic and coordinate conventions, an interval calculation can retain every parameter point compatible with a box of possible features. Inclusion alone does not establish that a compatible point exists or that a box becomes narrower.

The proposed reconstruction recovers the root time and rate from `AC1, AC2`, the C rate from `CC1`, the pulse time and amplitude from the BC moments, the ancestral onset and rate from the AB moments, and the A and B rates from their respective within-taxon moments. The AB step uses a global single-crossing argument. The underlying [identification hand proof](https://github.com/Sodelin/Research-Commons/blob/27b143c73a4ac272b560b2974d83ff96df738531/research/2026-10-05-dot-msci-two-site-nine-feature-identifiability-1150z/THEOREM.md) and [Jacobian and interval hand proof](https://github.com/Sodelin/Research-Commons/blob/27b143c73a4ac272b560b2974d83ff96df738531/research/2026-10-05-dot-msci-joint-jacobian-contractor-1257z/THEOREM.md) give the complete arguments and their inherited dependencies. Their original headers call them candidates; a later internal register records the hand result as completed within its stated scope. The [identification review](https://github.com/Sodelin/Research-Commons/blob/27b143c73a4ac272b560b2974d83ff96df738531/research/2026-10-05-dot-msci-two-site-nine-feature-identifiability-1150z/REVIEW.md) and [Jacobian review](https://github.com/Sodelin/Research-Commons/blob/27b143c73a4ac272b560b2974d83ff96df738531/research/2026-10-05-dot-msci-joint-jacobian-contractor-1257z/REVIEW.md) both name dot (OpenAI) and are not independent human peer reviews.

## What has and has not been checked

The existing Lean compiler owner reports a successful check of the exact selected forward and root-component files, including the analytic identification of root time and rate under their declared assumptions. That report covers two files and a selected audit; it is not a full proof of the nine-parameter theorem. The reported context was Lean 4.33.1 and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. The selected `ForwardDraft.lean` had SHA-256 `8becd27a233481437bfc7a2acd91027362e213368bc8657a2a714c577e9004ec`; `RootDraft.lean` had SHA-256 `f9c22571c83d862bb733d8701011af78f126f79dbbf61e0c3a8a0f4fa01248ba`. The owner reported a brief overlap with another compilation in a distinct context; this note does not claim a sole-process run or an independent rescan of the raw audit. Those source files and the complete audit have not yet been made part of this public note.

The full formal construction of the six-sample genealogy, its pair laws and their connection to the two-site sequence observations remains open. The remaining parameter recovery, Jacobian and interval claims also lack a complete Lean verification. The original proof bodies are attributed in their headers to dot (OpenAI), dated 5 October 2026; a human author list and contribution statement have not been determined.

No implemented inverse, useful sample-size bound, empirical dataset validation or general method for recovering arbitrary networks is established by this package. Estimation from data also requires the model, sampling, phasing, mutation clock and locus-independence assumptions to be justified. Exact identifiability does not by itself ensure a precise or practically useful estimate.

## Context and sources

The question builds on work about sequence-based identifiability and multispecies coalescent models. For example, [Durden and Sullivant](https://doi.org/10.1007/s11538-018-0399-1) study identification from expected k-mer distances in a tree/coalescent setting; [Zhu and Yang](https://doi.org/10.1093/molbev/msab009) study a different three-species model using two sites per locus. [Flouri and colleagues](https://doi.org/10.1093/molbev/msz296) describe a multispecies coalescent with introgression, and [Fogg and colleagues](https://doi.org/10.1093/sysbio/syad030) distinguish different inheritance mechanisms in network coalescent models. These references do not independently verify the result summarized here; broader prior-art and expert review remain open.

## Invitation to collaborate

The project welcomes researchers interested in checking the probability and observation model, reviewing the mathematics and prior literature, improving the Lean formalization, or assessing whether the model has useful biological applications. The goal includes learning the relevant biology and bioinformatics while working with collaborators. Constructive corrections and negative results would be valuable contributions. Discussion or a specific concern can be raised in the [Research Commons issue tracker](https://github.com/Sodelin/Research-Commons/issues).

This is an early research note for discussion. Any later archival deposit or journal submission should identify the responsible human contributors and applicable license, give the selected proof and formalization sources, and update these status statements to match the evidence available at that time.
