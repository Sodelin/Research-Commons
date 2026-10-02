# Exact all-finite-root clock and marginal compression contract

Dedicated Sol6.1 Lean contribution, 2026-10-02. These are classical finite
independent-clock/Bernoulli identities connected to the compiled original-ID
source interface. The underlying probability/binomial facts are not asserted
as new mathematics.

[Exact all-n signatures and axiom audit](receipts/VerifiedAllRootComponents.log),
[all-n manifest receipt](receipts/VerifiedAllRootComponents-receipt.json),
[combined fifteen-component audit](receipts/VerifiedFullComponentCheckpoint.log).

## All-n unordered live-pair clock law

[G4AllRootPairClocks.lean](program/G4AllRootPairClocks.lean) defines LivePair n as
all two-element subsets of Fin n. Lean proves its cardinal is choose(n,2).
The actual clock measure is the finite product of one unit-rate exponential
probability measure per unordered LIVE-root pair. The no-first-merger event is
that every clock exceeds the supplied arm duration t.

For every finite n and t>=0, Lean proves this event has real probability
`exp(-t)^choose(n,2)`. It equals the previously declared exponential holding
kernel, including the deterministic zero/one-root cases. An actual product
measure for the two private arms proves that their no-first-merger event
probabilities multiply. These total-hazard/product conclusions are not supplied
as unproved Lean premises inside this clock model.

Source SHA256: `149c8603c734e2ccb021963be42609698285033c1296b2bca18d0716f4258744`.
[Clock compiler/hash/resource receipt](receipts/G4AllRootPairClocks-receipt.json).
Compilation exit0 in2.31s, peak child RSS2.99 GiB, bounded single-thread4 GiB.

## Exact n+1-term binomial compression

[G4AllRootBinomialCompression.lean](program/G4AllRootBinomialCompression.lean)
uses an explicit equivalence between independent Boolean LIVE-root assignments
and parent0 root subsets, then applies mathlib's existing powerset-card/binomial
sum identities. For any fixed arm kernels a,b and every finite n:

`privateNoMerger(n,u,a,b) = sum k=0..n choose(n,k) u^k (1-u)^(n-k) a(k)b(n-k)`.

The formula is an algebraic identity for every real u; valid probability weights
require 0<=u<=1. The actual-original-hybrid specialization preserves the original
parent edge IDs, u and kernels at every input size. For nonnegative fixed arm
durations t0,t1, Lean derives the all-n survival coefficient identity by replacing
a(k),b(k) with `exp(-t0)^choose(k,2)` and `exp(-t1)^choose(k,2)`.

Thus this marginal uses exactly n+1 count classes instead of2^n assignments.
Normalization, nonnegativity and original parent-count laws were already
all-n theorems in the earlier routing module; the explicit polynomials there
were only specialized to n=2,3,4.

Source SHA256: `6f4f1e0405c62c9905a58cc27815b79f03d218482517193b0104c0b73cb0df77`.
[Compression compiler/hash/resource receipt](receipts/G4AllRootBinomialCompression-receipt.json).
Compilation exit0 in2.41s, peak child RSS2.99 GiB, bounded single-thread4 GiB.
All printed axioms are exactly propext, Classical.choice and Quot.sound.

## Exact boundaries of the compression

The result concerns a no-first-merger marginal. It does not say that root counts
determine complete labelled forest outputs, descendant labels, grafted subtree
history or later merger order. Those need additional state and source semantics.
Pointwise all-n identities do not establish a joint projective all-copy process.
They do not construct an infinite initial-population entrance law, give a uniform
finite recognition minimum, or replace finite-data probabilities with exact
model identification.

The remaining full-source obligation is interpreting the actual graph-driven
Kingman stages and subsequent merger/reset dynamics in the formal process.
All retained/shared-register and common-mixture contexts keep their separately
specified semantics; this is the private independent live-root mode.
