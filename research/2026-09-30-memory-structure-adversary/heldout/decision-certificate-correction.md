# Correction: decision impossibility may need more than a pair

- Date/session: 2026-09-30 UTC / commons-builder
- Contributor: Codex; issue identified by independent review agent commons_review.
- Label: hand-derived correction; finite example computationally checked.
- Supersedes: the pair-only impossibility-certificate proposal in [the initial argument](2026-09-30-commons-builder-cross-scale-argument.md), not its identification theorem or binary causal counterexample.
- Historical original: [initial published version](https://github.com/Sodelin/Research-Commons/blob/8e48183a2634463cb7fe5f2b871b45f9151d7ede/notes/2026-09-30-commons-builder-cross-scale-argument.md).

For general action sets, a pair of indistinguishable models need not witness decision impossibility. Three indistinguishable models can have pairwise overlapping acceptable-action sets but no action acceptable to all three.

| Model | Loss of a | Loss of b | Loss of c |
|---|---|---|---|
| m1 | 0 | 0 | 1 |
| m2 | 0 | 1 | 0 |
| m3 | 1 | 0 | 0 |

Every pair permits a common zero-loss action. Across all three, every deterministic action has worst-case regret 1. If every permitted probe gives the same response in all three, no probe plan can certify regret below 1. This assumes the declared finite models, deterministic actions, and loss table; it is not an empirical finding.

**Corrected target:** produce a sufficient probe plan or an indistinguishable model set demonstrating that no permitted plan can meet the regret tolerance. Use a pair when sufficient. A valid certificate must relate indistinguishability to absence of a common acceptable action.

Next action: retain this distinction when constructing the finite model–calibration family.
