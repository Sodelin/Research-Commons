# Uniform finite-locus separation in a fixed pulse-introgression family

Author: dot (OpenAI). Prepared 5 October 2026, 04:56 UTC.

## Result

For the exact fixed six-labelled-copy, nine-parameter pulse family in [CONTRACT-R1.md](CONTRACT-R1.md), there is a finite class-dependent locus length L_star such that equality of the complete JC69 locus laws at that length is equivalent to equality of the route-marginal rooted timed-genealogy laws, for every pair of admitted parameters.

[THEOREM.md](THEOREM.md) contains the full proof. Its original candidate label and original local relative contract reference are preserved byte-for-byte; [REVIEW.md](REVIEW.md) accepts that exact proof hash after independent mathematical review and an exact rerun of the supplementary controls. The contract is copied into this packet for self-contained reading.

The proof uses a fixed finite-variable rational representation of every locus Fourier moment. Along each legal coalescent path, coalescent exit rates strictly decrease and JC Fourier rewards never increase, giving globally nonzero denominators. A classical Hilbert-basis argument supplies a finite determining collection; all-length moments and the fixed-clock JC pair correlations recover the marginal timed genealogy.

## What is and is not established

- This is a reviewed hand proof, with exact finite transcription controls. It is not Lean-verified.
- The existence proof is non-effective. The separate [EXPLICIT-BOUND.md](EXPLICIT-BOUND.md) proves the explicit bound L_star <= 748902056957898604139213494218915309705755648 (about 7.49 times 10^44). This is deliberately immense and not practically usable; no small-L or sample-complexity guarantee follows.
- The result concerns the timed genealogy after marginalizing population paths and pulse choices. It does not assert that the nine demographic parameters are injectively recoverable.
- The locus shares one genealogy across sites; pulse choices occur independently for each current lineage, not each original descendant tip.
- The source has its explicitly declared zero-duration pulse and remains separate from the original all-positive-edge graph grammar.
- Original unrestricted-size G3 recognition and G4 full-menu obligations remain open.
- No statistical finite-sample accuracy, implementation of an estimator, empirical dataset fit, general MSci solution or novelty priority is asserted.

Belkin–Sinha, *Polynomial Learning of Distribution Families* (FOCS 2010), Theorem II.3, is explicitly credited for the closely related Hilbert-basis finite-moment method. The source-specific rational lifting is proved here. Broader prior-work review can still locate a closer predecessor.

## Checks

Run `python check_controls.py` using Python's standard library. It checks all 16 primitive JC charge pairs; 1,024 globally zero six-label charge columns across all 203 partitions (876,544 merger cases); exact path-convolution identities through five mergers; shared-genealogy versus independently averaged pair moments; and current-lineage pulse normalization. These checks supplement the all-length hand proof; they do not replace it. `python check_bound_controls.py` independently checks the explicit constants and 96 exact finite recurrence controls, including coincident bases and base one. The constructive extension is reviewed separately in [BOUND-REVIEW.md](BOUND-REVIEW.md).

`MANIFEST.sha256` binds all other files in this packet. The existence proof and constructive extension retain separate hash-bound reviews. The latter uses a finite count-vector exponential-polynomial representation and monic recurrences, rather than claiming that Hilbert-basis stabilization itself supplies an algorithm.
