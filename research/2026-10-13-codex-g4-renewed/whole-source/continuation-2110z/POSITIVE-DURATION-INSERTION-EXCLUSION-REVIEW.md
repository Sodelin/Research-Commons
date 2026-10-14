# Review of positive-duration insertion exclusion

Reviewer: Codex delegated laplace_recovery researcher, 14 October 2026.
**Hand-proof composition review: accepted at the stated inherited source
interfaces.** The reviewer authored the one-sided observable-secant supplier,
so this is an independent review of the lead's composition, not an
independent reproof of that supplier. Sol separately reviewed the supplier.
No computation, formal verification or full G4 closure is claimed.

Reviewed file: [POSITIVE-DURATION-INSERTION-EXCLUSION.md](POSITIVE-DURATION-INSERTION-EXCLUSION.md).
SHA256: `65425a369363f9593a9a8292215dee1caa47f9350ccd576a5fe2052d3a9a69a0`.

The original anchor cover, private slot bookkeeping, shared insertion
measure and all-route finite-exposure premise are explicitly inherited.
Subject to those source interfaces, the proof is correct:

1. A prescribed n-A/one-B completed comb has no nontrivial A-only clade.
   Each A-private slot therefore contributes its no-merger diagonal
   multiplicatively. A B-private slot has one selected root; all other
   slots disappear projectively. The fixed common-clade anchor selection
   prevents any private slot from carrying both colours.
2. At g=0 and n>=2, only k=0 and k=1 contribute to the coin derivative.
   Since d[g(1-g)]/dg=1 at zero, division by the ordinary diagonal gives
   n(exp((n-1)t)-1). After division by exp(t)-1 this is exactly
   n sum_(r=0)^(n-2) exp(rt), extending continuously to n(n-1) at t=0.
   Endpoint g=1 gives the same expression by arm symmetry.
3. Every normalized insertion contribution to this comb is nonnegative.
   A positive measure on t>0 has positive mass on t>=eta for some eta>0;
   the finite anchor cover retains positive such mass for one fixed anchor.
   Thus its relative contribution grows at least c n exp((n-2)eta).
4. The same actual comb and the same secant direction satisfy the supplier's
   fixed polynomial lower bound. Their exact matching equation cannot hold
   for all n against that positive exponential. No effective or uniform
   polynomial degree is required.

The conclusion nu(t>0)=0 is therefore justified. Duration-zero mass has
relative contribution 2 alpha_A lambda_n, so it survives this comparison.
The packet correctly leaves its source-constrained cancellation, bounded
endpoint ghosts and the master finite-certificate obligation open.
