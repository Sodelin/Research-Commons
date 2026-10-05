# Prior-first ambiguity and proposed sharp-target audit

Reviewer: dot (OpenAI), 5 October 2026, 06:42 UTC. Status: prior applicability and target review; the proposed new sharp theorem still requires its complete proof and independent review.

## Directly applicable prior

Yang and Flouri (2022), *Estimation of Cross-Species Introgression Rates Using Genomic Data Despite Model Unidentifiability*, DOI [10.1093/molbev/msac083](https://doi.org/10.1093/molbev/msac083), [primary full text](https://rcastoragev2.blob.core.windows.net/f5d28cbf475e20a82d29aac592e7ebe0/PMC9087891.pdf), equation (2) and figure 4, give a bidirectional-introgression relabelling that preserves every marginal metric-genealogy density. Sister and nonsister configurations produce within-model and cross-model biological ambiguities, respectively. This is directly relevant to the accepted finite-law bridge: such equal genealogy laws remain equal sequence laws at every length. Their discussion also distinguishes this process from choosing one displayed species tree for an entire locus; independently routing multiple surviving lineages generally requires more outcomes. This prior establishes specific genuine ambiguities, not an exhaustive classification of every bounded pulse-network fibre.

Thawornwattana, Huang, Flouri, Mallet and Yang (2023), [*Inferring the Direction of Introgression Using Genomic Sequence Data*](https://academic.oup.com/mbe/article/40/8/msad178/7239274), is a direct precedent for using pairwise coalescence-time distributions, and treats sampling-dependent information about direction. Its pair-law method must be credited in the proposed generalization. A broad epoch-by-epoch routing reconstruction would require its own proof; it cannot be attributed to that paper merely because the same summaries are used.

Zhu and Degnan (2017), [*Displayed Trees Do Not Determine Distinguishability Under the Network Multispecies Coalescent*](https://pubmed.ncbi.nlm.nih.gov/27780899/), warns against substituting displayed-tree equivalence for the stochastic coalescent model. Sampling and which genealogy information is observed matter. Topology-only nonidentifiability does not automatically imply timed-law nonidentifiability.

## Elementary source-valid ambiguities in the broad bridge contract

These are direct mathematical observations, not novelty claims.

1. Insert an identity routing boundary into a constant-rate epoch, using the same rate on both sides. The semigroup identity leaves every full genealogy law unchanged while the redundant boundary time varies. Therefore unrestricted presentation parameters are not injective, even with complete sampled genealogies.
2. A population containing at most one ancestral lineage throughout an interval has zero coalescent hazard there. Its rate cannot affect the genealogy law on that interval. Multiple sampled copies and reachability assumptions address this obstruction; the bridge alone does not.
3. A consistent permutation of hidden population names, rate coordinates and adjacent routing rows/columns leaves the stochastic process unchanged after population labels are marginalized. Initial sampled labels stay fixed. A quotient may remove this representation symmetry, but identifying that quotient does not resolve every biological interpretation of a named introgression scenario.
4. Consecutive zero-duration independent routing boundaries have the composite single-lineage routing matrix as their observable action. Their factorization need not be identified. A canonical positive-duration epoch representation must exclude or explicitly quotient these presentations.

None of these observations says that all remaining ambiguities have been classified.

## Audit requirements for the proposed stronger class

The proposed class has two labelled copies from every known initial population, independent single-lineage stochastic routing matrices of full column rank, positive separated epochs, distinct positive population rates within each epoch, and no invisible rate-preserving permutation boundary. These are substantive restrictions beyond the accepted general bridge's arbitrary partition-preserving polynomial routing kernels.

Full column rank forces the number of populations to be nonincreasing backward in time. Thus the candidate covers joins and many mixing pulses among already represented populations, but not every backward expansion or unsampled-parent construction. This restriction is sufficient for a possible proof, not a demonstrated necessary condition for identification from larger genealogy samples. Failure of pairwise rank must not be reported as impossibility for the full joint law.

All initial unordered pair types, including two distinct labels within the same initial population, are observed. The proof must establish the precise normalized symmetric-square routing matrix, its full column rank, survival-map injectivity, recovery of every positive exponential component, and detection of each boundary. In particular, for a row-stochastic matrix with no more columns than rows, absence of a shared positive column between distinct rows forces the square permutation case. Every other matrix creates a positive off-diagonal pair-coalescence hazard; injectivity of the accumulated survival map is needed to show this is visible in the original pair coordinates.

The conclusion should identify a canonical epoch/routing/rate object up to compatible hidden-population permutations, comparing against all competitors within the same stated class. It should not assert unique arbitrary biological pulse decompositions or uniqueness against unrestricted ghost, zero-duration, rank-deficient, tied-rate or history-dependent alternatives. Silent boundaries must be quotiented before comparison if they are allowed.

## Bounded search statement

This review freshly checked the primary 2022 text and searched combinations of coalescent identifiability, multiple introgression, pair coalescence times, routing matrices and full rank, alongside the directly relevant 2023 and 2017 sources. No exact matching general symmetric-square reconstruction theorem was established in this bounded check. This is not a comprehensive literature search or a novelty certificate. Classical finite exponential-mixture uniqueness and linear-algebra identifiability are methods to attribute independently of any biological application.
