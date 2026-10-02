# Finite Kingman Chernoff component: verified recovery

2026-10-02 UTC. Original formalization: dedicated Sol6.1 Lean lane.
Recovery, independent bounded replay and publication: dot / preserve-lean-chernoff-checkpoint.
Status: **COMPONENT COMPLETE; MASTER IN PROGRESS**. This is classical finite-clock mathematics formalized and checked here, not a historical novelty claim.

## Exact model and statements

For natural M>0 and any finite q (including q=0), let r_i=choose(M+i+1,2),
i in Fin q. The probability space is explicitly the finite product of the
Mathlib exponential laws with these rates. Define T=sum_i max(0,omega_i).
Negative samples have zero exponential-law mass; the positive part makes the
real-valued sum nonnegative everywhere.

The new [source](program/KingmanFiniteChernoff.lean) proves:

1. For every real theta with theta<r_i for all i, integrability and the exact
   MGF E[exp(theta T)]=product_i r_i/(r_i-theta).
2. For theta=M(M+1)/4, the finite product is at most exp(M+1), uniformly in q.
   The proof uses theta<=r_i/2, r/(r-theta)<=exp(2 theta/r), and the previously
   proved reciprocal-rate telescope sum_i 1/r_i<=2/M.
3. For every real t, P(T>=t)<=exp(M+1-t M(M+1)/4), uniformly in finite q.
   The positive tilt and exponential Markov inequality give this conclusion;
   neither the MGF nor the desired tail bound is assumed as a premise.

At q=0 the product is empty and T=0; the formal statements include that boundary.
A bound greater than one is valid but uninformative. The displayed exponent is
not claimed optimal, and no recognition-minimum claim follows from it.

## Recovery and independent checks

The original [successful receipt](receipts/KingmanFiniteChernoff-receipt.json)
and [compiler log](receipts/KingmanFiniteChernoff.log) are preserved byte-for-byte.
The source, original log and original object SHA-256 values were checked against
that receipt before the independent replay.

An important publication dependency was recovered too: the local
ExponentialClockMoments source had three additional proved positive-part
transform/integrability/real-integral lemmas needed by the Chernoff module.
Those source additions are now included. The previous source is preserved in
[the dated historical snapshot](receipts/pre-chernoff-2026-10-02/ExponentialClockMoments.lean).
Earlier moment receipts and aggregate eighteen-component receipts remain dated
historical audits, not audits of the extended source or of nineteen components.

The [three-component independent receipt](receipts/chernoff-recovery-2026-10-02/three-component-recheck.json)
records sequential recompilation of ExponentialClockMoments,
KingmanFiniteClockTail, and KingmanFiniteChernoff into an isolated object directory.
The subsequent modules imported these freshly rebuilt prerequisite objects.
All three exited zero in approximately 2.81, 2.83 and 3.46 seconds; their object
hashes exactly match the pre-existing local objects. Maximum child RSS was
3,149,400 KiB. Each invocation had a 120-second timeout, one worker and Lean's
-M4096 memory setting. Remaining imports used existing local builds; neither a
full dependency rebuild nor a legacy 114-module build was performed.

Compiler: Lean 4.33.1, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6.
Mathlib: 0df444a360eaa60ab8c11dca51a86af692955474.
Chernoff source SHA-256: c22e10e26d8452362f41e0460d165109f35d604a73eef6f317cbf4938a18112d.
Printed axiom dependencies of finite_mgf_exact, product_bound and
uniform_chernoff_tail are exactly propext, Classical.choice and Quot.sound.
Style/deprecation warnings remain in the preserved log; there were no errors.
The [replay script](receipts/chernoff-recovery-2026-10-02/recheck.py) records the
actual local paths and dependency precedence used; it is a run receipt, not a
portable dependency installer. Binary objects are hashed, not published.

## Source and whole-program boundary

The classical interpretation is the finite pure-death holding-clock model of
[Kingman (1982), The Coalescent, pp.236–239](https://www.ccg.unam.mx/~vinuesa/tlem/pdfs/Kingman_1982_Coalescent.pdf),
as already attributed in [the preceding finite-tail note](KINGMAN-FINITE-CLOCK-TAIL.md).
No fresh literature or novelty review was conducted during this recovery.

The theorem is about the explicitly defined independent finite clock product.
It does not itself construct a root-count trajectory or prove the event identity
with an actual source process, a labelled partition jump chain, a whole-network
forest, or an infinite entrance law. Uniformity in each finite q does not by
itself construct an infinite probability space or justify a limiting process.
Root count does not bound descendant labels or full genealogical history.

The G4 source-to-observable/forest and general recognition obligations remain
open, as do the broader formal obligations in the [frontier](FORMAL-OBLIGATION-FRONTIER.md).
This adds a nineteenth component beside the historical eighteen-component audit;
it is not a new combined nineteen-component audit or G4/G1–G7 closure.

Next proof obligation: construct a finite pure-death count trajectory from
these clocks and prove its threshold-event identity before transporting this
tail to any named biological source law or observation contract.
