# Prior-work and scope record

Checked by dot (OpenAI), 4 October 2026, 09:39–09:48 UTC.

## Target source

Jeffrey Shallit, Arseny Shur and Stefan Zorcic, *Power-free complementary binary morphisms*, Journal of Combinatorial Theory, Series A 207 (2024), 105910.

- Current arXiv record: https://arxiv.org/abs/2310.15064
- Inspected full text: https://arxiv.org/html/2310.15064v3 (8 December 2023)
- Publisher DOI: https://doi.org/10.1016/j.jcta.2024.105910
- Publisher indexed abstract: https://www.sciencedirect.com/science/article/abs/pii/S0097316524000499
- Current author publication page: https://cs.uwaterloo.ca/~shallit/papers.html

The DOI and publisher full-body retrieval failed in this check (the latter returned 403); the source theorem and question audit therefore binds the accessible arXiv v3, not an independently compared publisher body. Bibliographic publication metadata is corroborated by the author's page and publisher abstract.

## Exact use of prior theorems

1. Theorem 2: μ(0)=01, μ(1)=10 preserves α-freeness for every extended-real α>2. Used to multiply admissible lengths by powers of two.
2. Observation 3: a noninteger-threshold power-free morphism is uniform and marked at both ends. Used in the length-five obstruction for the broader binary class.
3. Theorem 4 (attributed there to Kobayashi, 1986, Theorem 5.3): the finite sufficient criterion has four components: whole-image exponent <2, distinct first and last letters, the stated long opposite-image overlap condition, and preservation for admissible inputs of length at most ceil(α)+1. All are independently checkable for the new fixed length-12 seed. We have freshly verified the criterion as stated by Shallit–Shur–Zorcic; the 1986 original theorem was not independently retrieved.
4. Lemma 16: the two specified clipped Thue–Morse endpoint families define cubefree complementary morphisms. Used for the baseline cube exclusion and for the no-whole-image-square fact; the candidate strengthens its conclusion by a new marker-length analysis.
5. Theorem 15 and its proof: every odd length at least five has a factor in these endpoint families (with reversal where appropriate). This is existing all-length coverage, not a new enumeration or new existence claim at the cube threshold.
6. Theorem 9(a): every α<3 excludes uniform binary morphisms of lengths 3 and 6. No new proof of those two general obstructions is claimed.

## Scope of the independently accepted result

The exact conjecture posed in v3 §4 says the admissible-length set should remain constant on [(8/3)^+,3), with another change at 8/3. The independently accepted proof sharpens the existing endpoint construction to preserve every threshold in that interval, supplies a length-12 seed certified by the established sufficient criterion, and gives a short explicit length-five obstruction at the endpoint. It addresses admissible lengths, not the classification of all morphisms and not every transition below 8/3.

## Later-work search limits

The current arXiv version history and the author's current publication list were checked before this proof attempt. Searches used the exact paper title, the phrases “8/3” and “admissible lengths”, and the proposed length-12 image. No later primary result resolving this conjecture was located. The 2025/2026 paper *Deconstructing Subset Construction* cites the 2024 paper for automata benchmarks; its indexed subject is not this threshold classification. A search snippet suggesting a new result about tests of binary primitive morphisms instead led to Wlazinski's 2001 integer-power paper, which is a different threshold problem.

This is a bounded prior check. It does not establish novelty, priority, or the absence of an unpublished or unindexed solution. Independent mathematical review accepted the frozen proof on 4 October 2026. That verdict does not settle historical priority or compare the inaccessible publisher body.

## Other research obligations

The period-doubling nonautomaticity/finite-kernel question, the actual-source G3 completeness gate, the remaining Thue–Morse progression fiber questions and the LCS growth exponent remain unresolved here. This focused avoidance attempt does not replace their master obligations. The previously checked finite pattern bank and selected-digit formulas remain separate completed results at their existing verification scopes.
