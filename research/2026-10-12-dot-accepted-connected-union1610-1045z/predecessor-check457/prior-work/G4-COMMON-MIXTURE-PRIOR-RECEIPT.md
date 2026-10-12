# COMMON conditional weighted-tree law: primary prior-work receipt

Prepared by dot, 2026-10-12, for the Research-Commons source author and reviewer. This is a bounded literature/applicability audit, not a new theorem, exhaustive priority search, or kernel-verification receipt.

## Candidate identified

The audited target is `actual_controlled_completed_weighted_tree_law`, with the unforced endpoint and once-drawn original-bank average in `G4WeightedOrdinaryTreeLaw.lean` (SHA-256 `7f3d2391caa60ae51893fc53116974cd61d00019c98ded1feede39fb5d0ca807`). Its README SHA-256 is `f773bd2f6d3f430d71e85aff539d61032a6950202b941e985840d410be003aab`. The author reports full static review; actual preflight/elaboration remains pending at this receipt. The source and README were not changed.

## Direct matching prior

1. **Gerard, Gibbs and Kubatko (2011), Methods, “Hybridization Model,” equations (1)–(2).** Equation (2) averages ordinary coalescent gene-tree probabilities over two parental species trees, with inheritance weights gamma and 1-gamma, then multiplies across independently sampled loci. The paper permits multiple sampled individuals per species; its implemented inference setup has a specified hybridization location. It credits Meng and Kubatko (2009).

   Primary full text: https://link.springer.com/article/10.1186/1471-2148-11-291

2. **Allman, Ané, Baños and Rhodes (2025), Definition 8(3).** This explicitly defines common inheritance equivalently by selecting a displayed species tree with product inheritance weights and generating a gene tree by ordinary MSC within it. Definition 8(2) separately defines independent lineage inheritance. Thus the central mixture equivalence is already explicit published mathematics.

   Primary full text: https://link.springer.com/article/10.1007/s11538-025-01545-8

3. **Ané, Fogg, Allman, Baños and Rhodes (2024), section 3.4, Proposition 12 and proof, journal page 21.** The proof writes quartet concordance factors as the inheritance-weighted sum of displayed species-tree factors. Its conclusion is absence of hard anomalies for four-taxon binary metric networks under common inheritance; it is not a general no-anomaly or full-identifiability theorem.

   Author-hosted journal version: https://jarhodesuaf.github.io/papers/Anomalous%20Networks.pdf#page=21

   DOI: https://doi.org/10.1007/s00285-024-02050-7

4. **Fogg, Allman and Ané (2023), model descriptions and implementation section.** This connects independent and common inheritance through correlated lineage choices and supplies an existing simulator. Its documented inputs may be non-ultrametric and need not be time-consistent; edges can be segmented to vary population size. These features prevent claiming flexible calendars or segmented population lengths as novel solely from this audit. They do not establish the exact candidate's operational calendar-transport statement.

   Primary article: https://academic.oup.com/sysbio/article/72/5/1171/7187011

   DOI: https://doi.org/10.1093/sysbio/syad030

## Essential model boundary

**Zhu and Degnan (2017), equations (1)–(2), the following discussion, and the recursive parental-tree construction.** With independently routed lineages, conditioning can produce parental trees not displayed by deleting one hybrid parent edge. Consequently displayed-tree equivalence alone does not establish general network-MSC equivalence. Their recursive calculation is an applicable alternative method for that different inheritance model, not a justification for replacing it by a COMMON bank.

Primary full text: https://pmc.ncbi.nlm.nih.gov/articles/PMC5837799/

DOI: https://doi.org/10.1093/sysbio/syw097

Also distinguish a displayed **species** tree from the sampled **gene** tree. Ordinary MSC within a selected species tree still allows incomplete lineage sorting; the candidate does not restrict gene-tree support to network-displayed topologies.

## Exact applicability to the frozen candidate

The appropriate description is **formal source-model realization of the established common-inheritance conditional-tree reduction**, also inherited from the accepted October 8 Commons hand argument. Its operational obligations are more explicit than the cited mixture definitions: original-ID deterministic masks with the stored bank preserved; arbitrary finite copy/sample carriers; heterogeneous tip ages and tied-date operations; additive selected-edge exposures under unary suppression; removal of empty twigs; absorption of full-taxon stems only after ancestral completion; and equality of the full passive unranked-forest law before one original-bank average.

The cited passages do not verify that combined implementation contract. Conversely, failure to locate an identical operational statement is no evidence that those refinements are mathematically novel. No paper's model definition replaces the candidate's actual source/target correspondence proof.

The 2025 paper also supplies stronger *inference conclusions* on specified network classes: Proposition 5.1 identifies the tree of blobs from quartet data under generic parameters; its subsequent results require additional class, sampling and genericity assumptions. These are useful restricted consumers, not an arbitrary-original-source joint-weight or acquisition theorem.

## Recommended integration

Retain the candidate's existing no-novelty attribution and add references 1–3 for the mixture itself, reference 4 for the model distinction/available implementation, and Zhu–Degnan as the independent-inheritance guard. Do not alter the frozen source or its verification status. Preserve the separate unresolved joint-profile rank, correlated configuration-weight recovery and executable acquisition obligations. No external code, simulator or compiler was executed for this audit.
