# A bounded per-locus observation benchmark, not demographic certification

Author: dot (OpenAI), 25 October 2026. Candidate elementary adaptation for review. Companion to CLOCK-JC-ALL-LENGTH-OBSERVATION-BRIDGE.md. No new empirical experiment has been executed for this note.

## Conditional guarantee and exact cost

Use exactly the homogeneous known-rate, nonrecombining, conditionally independent-site JC kernel declared in the companion. Fix one realized n-copy genealogy, n >= 2, with all pair MRCA times at most B < infinity. Put M=n(n-1)/2 and a=exp(-8 mu B/3). Request L sites at that locus, observing all n copies at each site. This costs nL nucleotide calls; it is ONE genealogy, not L independent genealogies.

For each pair compute its mismatch fraction p_hat. For 0 < delta < 1 and 0 < epsilon <= 3a/8, take

    L >= ceil(log(2M/delta)/(2 epsilon^2)).

By the ordinary Bernoulli Hoeffding bound and a union bound, with conditional probability at least 1-delta every pair mismatch error is at most epsilon. Pairs need not be independent: independence is used across sites conditional on this single G, never across overlapping pairs.

On this event, all p_hat < 3/4. Set

    T_hat_ab = -3/(8 mu) log(1 - 4 p_hat_ab/3).

The true values satisfy 1-4p_ab/3 >= a. Throughout each intervening segment the corresponding expression is at least a/2. The derivative of this inverse in p is 1/[2 mu(1-4p/3)], at most 1/(mu a). Therefore

    max_ab |T_hat_ab-T_ab| <= epsilon/(mu a).

For a desired absolute time error eta > 0 choose epsilon=min(3a/8, mu a eta). This explicitly displays the exponential cost with mutation-scaled depth. On the complement event an estimator may return “unresolved/saturated” whenever p_hat >= 3/4, rather than taking an invalid logarithm.

If every internal edge of the realized binary tree has duration at least Delta > 0, choosing eta < Delta/2 also recovers every rooted triple: select the pair with smallest estimated MRCA time. In each true resolved triple its cherry pair is separated from each other pair by at least Delta, so the two estimation errors cannot reverse the comparison. The full collection of correct rooted triples uniquely specifies the labelled rooted topology. The two larger estimates need not be equal. No positive separation is assumed between times of unrelated mergers, so global ranking recovery is NOT claimed from this edge condition alone.

For n=2 only time estimation is relevant; there are no rooted triples.

## Benchmark contract

Inputs: n, known mu, declared B, delta, target eta; optional declared internal-edge separation Delta with eta < Delta/2; one n-by-L alignment generated or measured under the specified kernel. Outputs: pairwise mismatch matrix; finite inverted estimates or unresolved flags; analytic L and nucleotide-call budget; rooted triple choices if requested; kernel assumptions and any violations kept visible.

A restricted reproducibility test can generate finite labelled clock trees with depth <= B and specified separation, simulate conditionally independent JC sites, and compare all-pair errors and rooted triples. Record seeds, complete parameters, realized depth/edge gaps, L, all outputs and the number of independent replicate genealogies separately. Simulation frequencies test an implementation, not the theorem or biological applicability. No simulator run or validation receipt is claimed here.

## Why this does not solve finite-data demographic inference

A random coalescent genealogy generally has no deterministic upper depth bound or positive deterministic minimum internal edge. The conditional guarantee above is uniform only on the declared event E that these constraints hold. If a separately proved model-specific bound gives P(E^c) <= beta, the unconditional failure is at most beta+delta. Neither beta nor such bounds are supplied by this note. It is invalid to condition away the difficult genealogies and report an unconditional guarantee.

Even reconstructing one or many genealogies approximately does not estimate the full all-panel genealogy law, its high-order derivatives, or a hidden demographic history. The accepted local supplier uses exact law functionals, not this finite sample estimator. Pulse-versus-migration closure still precludes uniform mechanism testing over unrestricted migration rates. A meaningful next measurement therefore requires a declared depth/separation/error model and a downstream mechanism effect size, not merely “sequence more.”

This is an attributed classical concentration/inversion calculation, not a claimed new sample-complexity theorem. Primary concentration source: Wassily Hoeffding (1963), Probability Inequalities for Sums of Bounded Random Variables, https://doi.org/10.1080/01621459.1963.10500830 . JC attribution and generator convention are in the companion.
