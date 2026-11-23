# Goldbach proof assembly: separating checked plumbing from the missing estimate

**Status:** The modular arithmetic and conditional assembly in Assembly.lean kernel-check in Lean 4.33.1. The candidate-supply and finite-coverage premises remain open. No Goldbach proof or VibeMath submission.

Inspired by the split between intermediate estimates and explicit theorem statements in [Alpöge's announcement](https://alpo.ge/remark.pdf) and [the independent RH/Dirichlet-GRH verification](https://math.mit.edu/~drew/grh/#what-was-verified). The proof method is not transferred; the attempt here is to make the interfaces explicit and catch mismatches before combining results.

## Narrow starter target

Let T(k)=210k+192. A **candidate** means T(k)=p+rq with p and q prime and r∈{1,2,3}. For this class a candidate is equivalent to a prime–prime pair. If r=2 then 2 divides p, so p=2 and q=105k+95, a multiple of 5 greater than 5. If r=3 then 3 divides p, so p=3 and q=70k+63, a multiple of 7 greater than 7. The case r=1 gives a prime pair, and every prime pair gives a candidate with r=1. No analytic input is used for this local equivalence.

| Component | Contract | Evidence / open obligation |
| --- | --- | --- |
| Local rejection | Impossible values of r=2 or r=3 for T(k) | Hand argument above, checked lemmas no_factor_two and no_factor_three. |
| Candidate conversion | A single candidate gives a genuine prime pair | Hand argument and checked auditClass_iff. For the audit class this is an equivalence, not an independent route to existence. |
| Supply | For every k above an explicit K, at least one candidate exists | **Open.** A fixed-exponent sieve or a bound on how many targets fail does not discharge this uniform statement. |
| Finite coverage | For every k below that same K, a genuine pair exists | **Not discharged.** This needs an effective K from the preceding component and verified coverage up to it. |
| Assembly | Supply plus finite coverage yields every target in this one progression | Checked combine_at_threshold, which takes both facts as explicit premises. Does not conclude full binary Goldbach. |

## What the published tools can and cannot plug into

- [Li–Liu's second-factor restriction](https://arxiv.org/html/2606.05224v2) gives a fixed positive exponent, not uniform factor membership in {1,2,3}. See the [cutoff audit](../../near-miss-audit/SIEVE-BOUNDARY.md).
- [Li–Liu's preprint on exceptional sets](https://arxiv.org/html/2610.26756v1) concerns the number of exceptional targets, not whether any specific target has an exception.
- The [toy constructions](../README.md) are tests against proposed inputs based only on first-order residue statistics. They are not lemmas about actual primes.
- The [Huang–Li parity-sensitive conditional approach](https://arxiv.org/abs/2005.03811) is a source to audit for a replacement supply contract; its extra shifted input is not inferred here from Dirichlet GRH.

## Verification

Assembly.lean was checked with the official Lean 4.33.1 Linux executable and no Mathlib dependency. The build with `lean --trust=0 -o Assembly.olean Assembly.lean` exited 0. Both `auditClass_iff` and `combine_at_threshold` depend only on the Lean core axioms `propext` and `Quot.sound`; no `sorryAx` or project-specific axiom appears. See [the build log](LEAN-REPLAY.txt). The two hypotheses in combine_at_threshold are premises, not established facts.

## Prior-work audit

[Chen's formalization blueprint](https://subfish-zhou.github.io/goldbach-lean/blueprint/chap-chen.html) already conditions its sieve on whether a factor divides the target; that divisibility idea and the Chinese remainder theorem are classical. [Li–Liu](https://arxiv.org/html/2606.05224v2) supply the asymmetric family that motivates the small-factor interface. A targeted search did not identify this exact choice of progression and small-factor certificate. That does not establish priority, and this note makes no novelty claim. The same equivalence that makes the modular check exact also shows it does not independently make existence easier.
