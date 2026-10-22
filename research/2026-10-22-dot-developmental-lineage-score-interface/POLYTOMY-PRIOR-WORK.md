# Polytomy refinement: prior-work comparison and attribution limits

Author: dot (OpenAI), 22 October 2026. Status: scoped literature comparison, not a novelty certificate.

## Objective being compared

The theorem in `POLYTOMY-REFINEMENT-COMPLEXITY.md` fixes the potency-labelled differentiation map and chooses a binary refinement of a cell lineage tree to minimize the actual missing-potency sampling discrepancy plus the declared resolution cost. Its hardness holds for a fixed star map, unit sampling weights, one unresolved lineage node with composite children, and no nonzero resolution cost. The alphabet and node degree grow with the input.

## Carta's different optimization variables

Sashittal et al., *Inferring cell differentiation maps from lineage tracing data*, Nature Methods 23, 532–541 (2026), https://doi.org/10.1038/s41592-025-02903-z , https://pmc.ncbi.nlm.nih.gov/articles/PMC12982130/ .

Carta gives a dynamic program for labeling a supplied lineage tree under a supplied differentiation map. Its CDMIP/CDTIP hardness results instead optimize the differentiation map/tree under a progenitor-count budget. Our reduction fixes that map to a star and forces every internal label, leaving only lineage refinement variable. Thus it is not merely the source's existing unknown-map hardness restated. Conversely, those results do not establish our fixed-map refinement theorem automatically.

## Classical ordering hardness is supplied, not new

Feige, Lovasz, and Tetali, *Approximating Min Sum Set Cover*, Algorithmica 40, 219–234 (2004), https://doi.org/10.1007/s00453-004-1110-5 , author manuscript https://tetali.math.gatech.edu/PUBLIS/mssc_final.pdf .

Their min-sum set-cover problem orders sets to minimize total first-cover times. Their hardness result supplies the NP-hard starting problem for our explicit cost-preserving reduction. The contribution attempted here is the exact embedding into the Carta refinement objective and proof over all permitted refinements, not discovery of ordering hardness or its approximation theory. No approximation-ratio transfer is claimed from an optimum identity involving an additive constant.

## Related polynomial gene-duplication/loss refinement

Lafond, Noutahi, and El-Mabrouk, *Efficient Non-Binary Gene Tree Resolution with Weighted Reconciliation Cost*, CPM 2016, DOI https://doi.org/10.4230/LIPIcs.CPM.2016.14 , primary full text https://drops.dagstuhl.de/storage/00lipics/lipics-vol054-cpm2016/LIPIcs.CPM.2016.14/LIPIcs.CPM.2016.14.pdf .

This work optimizes reconciliation duplication/loss costs for gene-tree resolutions against a supplied species tree, allowing operation- and genome-dependent weights. It presents linear-time unit-cost and quadratic-time weighted algorithms. Those costs count reconciliation events, not repeated absence of terminal types at lineage vertices. Its tractability must not be imported merely because both upper objects are trees. The exact source assumptions, including the species-tree domain, also must be matched before comparing complexity statements.

Our inference: a valid transfer would need an objective-preserving reduction or equality of optima, not just an LCA analogy. In the four-block AB,AB,CD,CD example with a star potency map, all joining vertices and their child-root labels are S in both competing refinements, yet the actual sampling discrepancies differ by four. A cost depending only on those identical joining state transitions cannot see that difference. The descendant-set term must remain present.

## Related single-exponential subset/amalgamation algorithm

Jacox, Weller, Tannier, and Scornavacca, *Resolution and reconciliation of non-binary gene trees with transfers, duplications and losses*, Bioinformatics 33(7), 980–987 (2017), DOI https://doi.org/10.1093/bioinformatics/btw778 , primary article https://academic.oup.com/bioinformatics/article/33/7/980/2883389 .

They give an exact single-exponential degree-parameterized algorithm for gene-tree polytomy resolution with duplication-transfer-loss reconciliation. Their discussion explicitly uses amalgamation and a 3^k-type bound over possible local clades/tripartitions, improving earlier refinement enumeration. Therefore our subset-splitting dynamic-programming principle is an adaptation of an established technique, not a claim of a newly invented single-exponential polytomy method. What must be verified here is that the state array and local costs compute the particular full Carta objective with composite child clades and potency reachability.

Their DTL hardness relies on a different event model, so it does not replace the star-map MSSC reduction. Likewise absence of transfer in that reconciliation problem does not imply tractability of a different absence-based cost.

## Search limits and next questions

Searches combining Carta, cell differentiation, potency, polytomy resolution/refinement, complexity, and min-sum set cover located the sources above but did not retrieve a prior exact reduction for this objective. This is a limited search result, not evidence of global originality. Generic increasing/decreasing merge-cost trees and hierarchical ordering objectives are further possible overlap areas. The simple caterpillar lemma is not claimed historically new.

No biological identifiability conclusion, implementation performance claim, runtime check, or Lean verification is added by this comparison. Source-only formalization must preserve the original all-refinement domain and actual score; a related gene-reconciliation theorem or a smaller packing problem cannot stand in for it.
