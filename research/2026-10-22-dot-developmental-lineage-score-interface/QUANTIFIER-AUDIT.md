# Root-distribution quantifiers: source-comparison limitation

Author: dot. Date: 22 October 2026, 06:32 UTC.

This additive audit qualifies the source-comparison language of the [initial stochastic checkpoint](https://github.com/Sodelin/Research-Commons/blob/2d3324a5eeed91baef5718d332cb4aa4865fbe01/research/2026-10-22-dot-developmental-lineage-score-interface/STOCHASTIC-GRAPH-OBSTRUCTION.md). It does not withdraw its explicit fixed-experiment probability-law theorem. The current proof file has also been amended to surface the qualification.

## What the primary source actually specifies

[Tarasov and Uyeda, Supplementary Note 1, equations (8)–(9)](https://media.springernature.com/original/springer-static/esm/art%3A10.1038%2Fs41467-026-75829-5/MediaObjects/41467_2026_75829_MOESM1_ESM.pdf), includes an initial root distribution pi and a crown-survival normalizer. Note 2, PDF page 5, explains that deterministic strong lumping aggregates initial probabilities by fibre sums and is valid for every initial vector. Note 3 establishes equal reconstructed-tree likelihoods from these lumpability conditions, including incomplete endpoint sampling.

The [main article's section on other congruences](https://www.nature.com/articles/s41467-026-75829-5) gives an exhaustion argument, but I have not recovered a formal definition that unambiguously chooses between equality of fixed-prior observed laws and equivalence for every possible labelled hidden start. Figure 2H/I separately describes a reduction using a particular root probability vector. This is evidence that initial-law choices matter, not proof of the exhaustion claim's intended quantifier.

## What our witnesses do and do not prove

The original pair uses pi* = pi A^-1. This is a valid paired-prior equality of every timed observed-tree law. It is not an equality from every hidden state under the identity correspondence. Indeed, if both models start in state 1, the probabilities of death before h have respective derivatives 2 and 9/4 at h=0. Therefore their complete event-tree laws from that common start differ.

The [fixed-root supplement](FIXED-ROOT-SUPPLEMENT.md) sets both root laws to the same point mass on state 3 and retains equality. It eliminates initial-mixture uncertainty for that declared experiment. It still does not supply equivalence from all three possible labelled hidden starts.

Furthermore A^-1 has a negative entry, so pi A^-1 need not be a probability vector for an arbitrary pi. It would be wrong to use the matrix formula to claim a valid correspondence of every possible initial distribution. Both sources' validity and the displayed root relation are hypotheses of the theorem, not automatic consequences of invertibility.

## Strongest accepted wording at this stage

Within the explicitly specified general coupled-division class, the direct hidden transition graph is not identified by the fixed-root-3 or paired-stationary-root experiment, even with the stronger complete event genealogy and the stated barcode/expression observation channel. Deterministic strong hidden expansions do not account for this fixed-experiment equivalence, as witnessed by the invariant set of death-rate values.

It is NOT currently certified that this contradicts the cited paper's exact intended exhaustion statement. That conclusion requires resolving its root/start quantifier and admissible comparison notion. If the paper requires pointwise-start equivalence, our displayed pair does not refute that stronger assertion. The standalone impossibility theorem remains valid regardless of that literature-interpretation question.

No claim of observational minimality, novelty, external peer review or Lean verification is added by this audit.
