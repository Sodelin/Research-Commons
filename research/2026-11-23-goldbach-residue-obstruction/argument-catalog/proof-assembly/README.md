# Goldbach proof assembly: separating checked plumbing from the missing estimate

**Status:** Hand-verified modular reduction. Assembly.lean is an uncompiled source draft; no Lean or Mathlib verification is claimed. No Goldbach proof or VibeMath submission.

Inspired by the split between intermediate estimates and explicit theorem statements in [Alpöge's announcement](https://alpo.ge/remark.pdf) and [the independent RH/Dirichlet-GRH verification](https://math.mit.edu/~drew/grh/#what-was-verified). The proof method is not transferred; the attempt here is to make the interfaces explicit and catch mismatches before combining results.

## Narrow starter target

Let T(k)=210k+192. A **candidate** means T(k)=p+rq with p and q prime and r∈{1,2,3}. For this class a candidate is equivalent to a prime–prime pair. If r=2 then 2 divides p, so p=2 and q=105k+95, a multiple of 5 greater than 5. If r=3 then 3 divides p, so p=3 and q=70k+63, a multiple of 7 greater than 7. The case r=1 gives a prime pair, and every prime pair gives a candidate with r=1. No analytic input is used for this local equivalence.

| Component | Contract | Evidence / open obligation |
| --- | --- | --- |
| Local rejection | Impossible values of r=2 or r=3 for T(k) | Hand argument above, draft lemmas no_factor_two and no_factor_three. |
| Candidate conversion | A single candidate gives a genuine prime pair | Hand argument and draft auditClass_iff. For the audit class this is an equivalence, not an independent route to existence. |
| Supply | For every k above an explicit K, at least one candidate exists | **Open.** A fixed-exponent sieve or a bound on how many targets fail does not discharge this uniform statement. |
| Finite coverage | For every k below that same K, a genuine pair exists | **Not discharged.** This needs an effective K from the preceding component and verified coverage up to it. |
| Assembly | Supply plus finite coverage yields every target in this one progression | Draft combine_at_threshold, which takes both facts as explicit premises. Does not conclude full binary Goldbach. |

## What the published tools can and cannot plug into

- [Li–Liu's second-factor restriction](https://arxiv.org/html/2606.05224v2) gives a fixed positive exponent, not uniform factor membership in {1,2,3}. See the [cutoff audit](../../near-miss-audit/SIEVE-BOUNDARY.md).
- [Li–Liu's preprint on exceptional sets](https://arxiv.org/html/2610.26756v1) concerns the number of exceptional targets, not whether any specific target has an exception.
- The [toy constructions](../README.md) are tests against proposed inputs based only on first-order residue statistics. They are not lemmas about actual primes.
- The [Huang–Li parity-sensitive conditional approach](https://arxiv.org/abs/2005.03811) is a source to audit for a replacement supply contract; its extra shifted input is not inferred here from Dirichlet GRH.

## Verification

The arithmetic proof above can be reviewed independently of the draft. Assembly.lean imports Lean alone and writes primality as the elementary no-proper-divisor predicate (no dependency on a Mathlib bridge). Compile with a known Lean toolchain, e.g. lean --trust=0 Assembly.lean; review the printed axioms and compare each theorem's statement with the table before labeling the bridge verified. The current workspace has no Lean executable; no compiler outcome is reported. The two analytic and finite hypotheses in combine_at_threshold are not axioms and are not claimed as established.
