# Quartet concordance factors and three-cycle parameters: source comparison

Elizabeth S. Allman, Hector Baños, Marina Garrote-Lopez and John A. Rhodes, “[Identifiability of Level-1 Species Networks from Gene Tree Quartets](https://link.springer.com/article/10.1007/s11538-024-01339-4),” *Bulletin of Mathematical Biology* 86, article 110 (2024), is related work on parameter identifiability under the network multispecies coalescent. On 31 October 2026 UTC, this pass read the publisher's bibliographic record and selected text in the introduction, §§2–3, §5.4, the statement of Proposition 23 and the caption of Figure 6. It did not visually inspect the figures, audit the paper's proofs, rerun its computational algebra, or retain original response bytes or images. This is a bounded comparison, not an exhaustive literature review or independent verification.

## The source's observation and result

In Definition 3, a quartet concordance factor (CF) is the probability that the sampled gene tree displays a particular unrooted four-taxon topology. The source works with CFs under the network multispecies coalescent (NMSC), not with the present manuscript's nucleotide patterns or their within-locus two-site products. Its §3 also describes a pseudotaxon construction for sampling multiple lineages from a taxon.

Corollary 31 states that, for a level-1 metric binary semidirected network without 2-cycles, with two or more samples for every taxon, its quartet CFs identify the numerical parameters except hybridization parameters and lengths of edges in and adjacent to 3-cycles. This is a substantive nonidentifiability result for the stated CF setting. The paper's Theorem 30 gives related exceptions for one sample per taxon; its §6 discusses practical implications. The result concerns the source's specified network and parameter space; it is not an empirical demonstration about any particular dataset.

## Relation to the two-site manuscript

| Field | Allman and colleagues | Present manuscript |
| --- | --- | --- |
| Data summarized | Probabilities of gene-tree quartet topologies under the NMSC. | A probability law for two linked nucleotide sites per locus on a shared genealogy; selected pair-character moments are used in the proof. |
| Network and target | Numerical parameters on a known level-1 metric binary semidirected network, subject to the stated assumptions. | Numerical parameters in one fixed rooted three-population backbone with a directed backward pulse, rate ties and a known clock. |
| Multiple samples | At least two per taxon in Corollary 31; the source explains an equivalent pseudotaxon representation for CFs. | Six phased labelled samples, two from each population, in the specified model. |

The two results use different observables and parameter restrictions. The source's failure of identification from CFs does not by itself imply failure for the present fixed, constrained family or its two-site law. Conversely, the manuscript's claim does not establish identification from quartet CFs or for the source's broader network family. This comparison does not assert that either observation determines the other.

The later candidate crosswalk (internal supporting file not included: `QUARTET-CYCLE-CROSSWALK.md`) derives a three-cycle graph and proposes coalescent-unit edge lengths, but the complete stochastic-law and parameter correspondence remains open. It also gives an unreviewed time-scale argument illustrating why gene-tree topology and known-clock sequence data can differ. The effect of the manuscript's zero-duration hybrid edge, temporal constraints and B/C rate ties on the source's nonidentifiable parameter variations has not been established. The source's three-cycle result therefore warrants attention without being treated as an established contradiction or a proof of novelty. Independent scientific review and the complete Lean process-to-observation argument remain open.
