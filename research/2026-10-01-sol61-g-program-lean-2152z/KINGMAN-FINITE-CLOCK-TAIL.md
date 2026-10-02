# Actual exponential moments and finite Kingman clock tail

Dedicated Sol6.1 Lean contribution, 2026-10-02. The classical underlying
ordinary-population model is attributed to
[Kingman (1982), The Coalescent, pp236–239](https://www.ccg.unam.mx/~vinuesa/tlem/pdfs/Kingman_1982_Coalescent.pdf).
The paper separates the pure-death holding clocks from the labelled partition
jump chain. Its infinite construction is a further result, not supplied merely
by a finite-count identity.

[Exact signatures/axioms](receipts/VerifiedClockTailComponents.log),
[manifest receipt](receipts/VerifiedClockTailComponents-receipt.json),
[combined seventeen-component axiom audit](receipts/VerifiedFullComponentCheckpoint.log).

## Density-derived clock moments

[ExponentialClockMoments.lean](program/ExponentialClockMoments.lean) uses the
actual Mathlib exponential probability density. Gamma shape-two normalization
proves its nonnegative first moment is 1/r for every r>0. Exponential tilting and
normalization prove its exponential transform is r/(r-theta) for theta<r.
Neither moment is an assumed proof premise.

The exact formal quantities are nonnegative Lebesgue integrals, preserving the
complete underlying probability measure. Source SHA256:
`78593f8aac750e4d5bdd6fe0e48adb75350fefd09f230aa7f3304cf56fa75627`.
Successful bounded compile2.61s, about2.99 GiB child RSS.

## Actual finite clock product and uniform Markov bound

[KingmanFiniteClockTail.lean](program/KingmanFiniteClockTail.lean) defines one
independent exponential holding clock of rate choose(k,2) for each level
k=M+1,...,M+q. The initial finite root count is M+q. The nonnegative clock sum
uses the positive part of each real sample, so its definition is valid even on
null negative-sample sets.

Lean derives the first moment of this actual product-measure sum and telescopes
the reciprocal rates to

`2/M - 2/(M+q) <= 2/M`.

For every finite q, M>0 and t>0, Mathlib's proved Markov inequality then gives

`P(nonnegative holding-clock sum >= t) <= 2/(M t)`.

The expectation bound is a conclusion, not an assumed desired source bridge.
At q=0 the sum is empty and its expectation is exactly0. Source SHA256:
`2d79e10d34786a8abbfc2e4ca80f3725a386429e6bbdcf10709838d58a4c40ca`.
Successful bounded compile2.80s, about3.00 GiB child RSS. The receipts pin the
compiler, mathlib, exact source/log/object hashes and all actual parameters.
Printed axioms are exactly propext, Classical.choice and Quot.sound.

## Formal and biological boundary

The current Lean theorem concerns the explicitly defined finite clock sum.
The classical pure-death count interpretation relates this time to the event
that more than M roots remain. A full root-count trajectory/source law, full
labelled forest/jump-chain interpretation, graph-driven reset semantics and
infinite entrance law are separate formal obligations. Arbitrary original
networks with multiple populations do not inherit a one-population time bound
without a source-specific bottleneck/positive-time contract.

Bounded root count also does not bound descendant labels, genealogical history
or full unranked forest state. It is a probability/error truncation statement,
not an exact deterministic compression or a verified recognition minimum.
The stronger exponential/Chernoff candidate is not included in this completed
checkpoint; the newly verified transform supports its next finite-clock check.
