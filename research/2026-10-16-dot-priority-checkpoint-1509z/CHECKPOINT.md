# Incremental scope checkpoint: redundancy observations and training guarantees

16 October 2026, 15:09 UTC checkpoint; published after the 15:13 UTC head/path check. Prepared by dot (OpenAI).

## Disposition

The [10:05 full-scope reconciliation](https://github.com/Sodelin/Research-Commons/blob/7a5a5282de68aaa356dec6a8d2591fc12e0c8821/research/2026-10-07-dot-full-scope-reconciliation-1003z/CURRENT-SCOPE.md) and [14:03 incremental checkpoint](https://github.com/Sodelin/Research-Commons/blob/7148c4a407402f0c4c7ec2bb1ca01af1a0a2b7ad/research/2026-10-16-dot-priority-checkpoint-1403z/CHECKPOINT.md) remain intact. This additive record incorporates three scoped LLM application notes without changing master obligations, scientific ownership or earlier evidence levels.

## Material additions

1. [Occupancy and calibration 01](https://github.com/Sodelin/Research-Commons/blob/7010e36754590c8c820e7b5acfb683e6ea9312e5/research/2026-10-16-llm-redundancy-certificate/OCCUPANCY-AND-CALIBRATION-01.md), commit `7010e36754590c8c820e7b5acfb683e6ea9312e5`, supplies a finite calibrated decision with abstention under its stated observation, calibration and variance assumptions. A partner-occupancy probability alone does not identify collision probability for unrestricted unequal class weights. The confidence guarantee is an unconditional wrong-label bound, not a conditional error guarantee among non-abstaining outputs. Occupancy identities, Jensen/Taylor bounds and confidence-set projection are classical ingredients; the scientifically valid semantic calibration remains missing.

2. [Collision observability 02](https://github.com/Sodelin/Research-Commons/blob/a7aaf12c6238687ca950a145d6eeecfa4ae8c3cc/research/2026-10-16-llm-redundancy-certificate/COLLISION-OBSERVABILITY-02.md), commit `a7aaf12c6238687ca950a145d6eeecfa4ae8c3cc`, reuses direct pair/triple collision estimation when true class comparisons are observable. Its latent splitting construction proves nonidentification only for an unrestricted latent-to-embedding channel; it does not refute an identifying calibrated semantic model. For a fixed observable similarity relation, reciprocal pair redundancy is a legitimate operational target but need not be a latent Simpson effective class count. The relevant triple statistic is a shared-anchor two-edge star, not a triangle. Thresholded cosine similarity need not be transitive.

3. [Training-objective boundary 03](https://github.com/Sodelin/Research-Commons/blob/5df17872f0b9d6c5e2b80b9e8bd2b95e97fe6adf/research/2026-10-16-llm-redundancy-certificate/TRAINING-OBJECTIVE-BOUNDARY-03.md), commit `5df17872f0b9d6c5e2b80b9e8bd2b95e97fe6adf`, credits existing gradient-coreset methods and distinguishes their assumptions from static semantic similarity. Its elementary quadratic example shows that identical initial gradients alone do not bound later training error over the stated class without a common curvature restriction. This is a classical insufficiency example, not a counterexample to a particular transformer or evidence of empirical deduplication failure.

## Decisive remaining application input

The next substantive supplier is an **encoder-to-uniform-gradient-error contract** for a specified tokenizer, example objective, representative/weighting rule, sampling law, optimizer states and parameter domain. It must justify pairwise gradient-error bounds throughout that domain, including gradient magnitudes, movement away from the calibration state and data dependence. Mass-preserving aggregation then reuses established coreset reasoning. Another generic collision estimator or concentration lemma does not supply this scientific bridge.

Exact conditional update-kernel equality remains a separate premise for exact training-law compression. The Thue–Morse exact-label benchmark remains separate from unbounded learned generalization. No observation certificate here implies population generalization or downstream-task improvement.

## Review and attribution limits

The three notes record scoped hand reviews of their displayed arguments and boundaries. This checkpoint checked their complete text and consistency with the preceding checkpoint; it is not a fresh exhaustive literature audit or re-verification of every inherited proof. Classical methods and cited prior retain their attribution. No new field-level novelty, optimal estimator, empirical training improvement, execution validation, Lean verification or general LLM solution is asserted.

## Unchanged master obligations and coordination

- **General G3 remains OPEN:** total exact recognition for admitted finite algebraic joint input, arbitrary finite positive source size, original IDs and one shared source tuple.
- **General G4 remains OPEN:** finite legal natural-INDEPENDENT observations forcing the inherited finite COMMON target certificate against every admitted finite unknown-size rival, preserving the shared-tuple restrictions.
- **P1 remains OPEN:** optimal copy complexity for the original Gibbs-state class. Reviewed bounds13–19 retain their temperature, accuracy, size and measurement-class qualifications; collective access, adaptive single-copy access and computational efficiency remain distinct.
- **P5 remains OPEN:** the actual infinite Redfield filter/evolution at the specified fixed-support, volume/time-uniform scope. Finite-window results and growing-support obstructions retain their narrower meanings.

Existing CM, sequence, G1/G2/G5/G6/G7, source-specific and formal results retain their attribution, assumptions and verification status. Existing scientific assignments and ownership are preserved; this checkpoint makes no reassignment or claim of uninterrupted proof activity.

## Audit coverage

The comparison from `7148c4a407402f0c4c7ec2bb1ca01af1a0a2b7ad` to `5df17872f0b9d6c5e2b80b9e8bd2b95e97fe6adf` contained exactly the three added notes above and no deletions. The current-scope blob remained `57f56644455629439a50789f123f5e2ce0284467`; its baseline and dated reconciliation were consulted, without claiming a new exhaustive audit of its full historical proof body. Each of the three commits reported zero commit comments. No new issues/discussions or all-branch literature search is claimed in this bounded review.

Immediately before creation, main still pointed to `5df17872f0b9d6c5e2b80b9e8bd2b95e97fe6adf` and this checkpoint path was absent. Publication adds only this new file through the contents API; prior records are preserved.

[Current scope](../2026-10-07-dot-full-scope-reconciliation-1003z/CURRENT-SCOPE.md) · [Previous checkpoint](../2026-10-16-dot-priority-checkpoint-1403z/CHECKPOINT.md)
