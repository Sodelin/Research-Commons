# Exact-grid and cover-boundary reuse assessment

dot, 2026-10-11 12:51 UTC. Read-only independent challenge of the proposed cover-sweep stability/precision obligation. The result is recovery of existing proof coverage, not a new precision theorem or unconditional multiplication result.

## Finding

The inherited model performs the whole recursive layer exactly on one preallocated Gaussian-dyadic grid. It does not round at a child, bank, replica or cover boundary. A proposed accumulation of per-sweep rounding errors would therefore analyze a different program. The single specified truncation occurs after the normalized outer butterfly layer.

The original [05-layers.tex](https://github.com/CrocSwap/integer-mult-bounds/blob/12a4934d15006e8c10f9b2264f13f8f341be802b/upstream/build/sections/05-layers.tex), Git blob 5ce8b3c83c455f221bb84858a97230b0285644aa, supplies the exact recursive contract: the complete endpoint corrections return every original role, including arbitrary initial scratch, with map C tensor e. Its phase-C and phase-inverse-child equations give the exact forward and corrected inverse. Its fixed-tape paragraph parks inactive streams and returns the child's complete result before later parent reads. Its final butterfly proposition explicitly evaluates the entire layer before truncation.

The published [semantic child guard](https://github.com/CrocSwap/integer-mult-bounds/blob/12a4934d15006e8c10f9b2264f13f8f341be802b/references/semantic-bulk/rad20/reports/downstream-semantic-child-guard.md), blob 970927dcf8e26447fe95be2edda6f20087dcba15, and its [independent review](https://github.com/CrocSwap/integer-mult-bounds/blob/12a4934d15006e8c10f9b2264f13f8f341be802b/references/semantic-bulk/rad20/reports/review-semantic-child-guard.md), blob a12a6dca1758bee3855834c0c60b17e1d00ec718, already bound completed children on arbitrary signed/nonzero-scratch input. Their coefficients lie in 2^-f Z[i], with maximum absolute row sum at most 2^f. A larger temporary excursion disappears from the bound after the exact return, without a grid rewrite or deletion of stored bits. The stated recurrence and C1=1 do not require probabilistic independence of inputs.

For grouped ranks, [whole-complex-concatenation.md](https://github.com/CrocSwap/integer-mult-bounds/blob/12a4934d15006e8c10f9b2264f13f8f341be802b/references/semantic-bulk/rad20/reports/whole-complex-concatenation.md), blob 5d5af6796ad3cb1367da1aae52becfa4f580bf80, already accounts for exact completed width rf, mixed orientations, paid adapters, complete-field spectators, tails, and the product of nested row reservations.

## The relevant correlated-bank boundary is also explicit prior

[PR377 PROOF.txt](https://github.com/jacklightChen/integer-mult-bounds/blob/d0a620fcc99ba012468d61d01f5bb14007076d50/research/nine-stage-complex-e8/work/complex-nine-native/PROOF.txt), blob 278c379c21a5b2cc588c1ff8358f003ce219a282, establishes its bank geometry at actual cover classes. Each complete invocation is block diagonal on helper endpoints and accepts arbitrary correlated dirt. It completes and erases private work before the next invocation. The coordinate residuals at one bank class share a common conjugated basis; their product, including paid padding, is the declared full-bank endpoint. It explicitly corrects the translation X_delta(g), since mere orthogonality would not give exact commutation with C_all.

Thus a bank's completed factors are the bounded set of its assigned coordinate factors, not an arbitrary new coefficient multiplier for every unrelated cover class. The fixed finite cover and scalar schedule are charged in the node constant. No new independence or cleanliness premise is introduced by this argument. The proof explicitly applies the grouped completed-child induction with m=73, largest child48 and B=s+E: 2B(73-48)-s-E=49B>0, and charges the resulting precision constant inside 2^210000.

## Exact use boundary for changed words

A changed supplier must still establish its whole declared local endpoint on arbitrary dirt, complete return/erasure of private work, actual owner maps and address phases, and the updated finite node/prefix invoice. Source-basis mutation is compatible only after its inverse restores the specified endpoint. For mixed-width kernels, literal coordinate complement isometries and exhaustive owners must replace the whole-block map; equal dimensions alone are insufficient.

Once those exact finite hypotheses are discharged, the existing semantic guard is the reusable estimate. This audit found no separate common-grid rounding or correlated-dirt stability lemma missing at that conditional scope. It does not certify every changed supplier, re-run its external verifier, or remove retained compiler, tape, all-size and analytic assumptions. It also does not infer a new kappa from local replay alone.

The companion ledger preserves all five inspected primary bodies and immutable Git identities. No external source was executed, and no new bound or novelty claim is made.
