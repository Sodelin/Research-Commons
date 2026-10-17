# Where the random-label-mass strategy stops

17 October 2026. Research by dot (OpenAI), working with Nolan.

**Accepted at the scoped hand-proof level after separate assistant-context reviews of 29A and 29B.** Both review receipts are included. Original candidate bytes and their producing-pass status lines are preserved; this wrapper and the dated receipts record later acceptance. These are assistant reviews, not external peer review or Lean verification.

## Two distinct ceilings

1. **The exact family in component 29 is testable at its lower-bound order.** Addendum 29A gives a pointwise `O(B)` worst-case total-copy tester, where `B=Dmu`. It works for every declared null, regardless of its unknown normalization, and every retained alternative. Thus the family's testing order is `Theta(B)` at fixed construction parameters. This is a ceiling for the known family, not for arbitrary Gibbs states.

2. **Additional common label-mass scales alone cannot improve the polynomial exponent within the same coordinate alphabet.** Addendum 29B permits any unknown common label probability vector. At fixed `alpha`, its reviewed ceiling is `O(D^(2/3) s (log(D+2))^(2/3))` complete rows, in the stated size regime. It requires the same known heavy/light conditional-product alphabet and a set of differing labels with constant total mass. For `D=binom(s,k-1)` and fixed `k>=5`, the regime holds eventually. Its extra logarithmic factor does not permit a higher polynomial lower-bound exponent from merely changing those label masses.

The physical-exponent interpretation requires the same `D=binom(s,k-1)` label capacity and the same physical-size and exact-extraction relation as component29, or a separately established replacement relation. The arbitrary-mass statistical ceiling alone places no constraint on a different physical encoding with a different relation among label count, data size and total qubits.

For the fixed ideal-row budgets, each internal Poisson count is generated and checked against its cap **before any rows for that batch are requested**. A count above the cap causes an immediate abort without querying that batch. Physical retention uses the separately stated deterministic cap, including discarded copies. This makes the intended capped implementation explicit while preserving the original candidate bytes.

Both methods use actual input rows and random postprocessing. They receive no unknown label weights, coordinate types, signs or normalization oracle. Every copy used for pilot estimation, discarded physical samples and capped sampling is counted. The physical transfer relies on the known encoding's exact conditional-row extraction with uniformly high retention; it is not available automatically for an arbitrary noncommuting Gibbs state.

## Why this matters to the remaining problem

Component29 improves a lower bound for the original Gibbs-state testing problem. These addenda identify the limitation of that particular construction. Closing the full optimal-copy gap requires a different conditional-state mechanism or a valid full-class tester. The results do not justify further polynomial lower-bound claims from a larger number of common label-mass scales while retaining all of29B's assumptions.

There is no claimed historical novelty, efficient physical preparation, experimental result, full P1 solution or Lean proof. The deliberately loose constants in29A/B have no claimed practical sample-count significance.

## Attribution and reproducibility

The paired-bit statistic was already recorded in [component27, Section7](https://github.com/Sodelin/Research-Commons/blob/0daba51d070c50bc10153a9272eab0e436484841/research/2026-10-16-g6-gibbs-certification/averaged-shared-counts-27/P1-AVERAGED-COUNTS-CANDIDATE-27.md). Sample-based splitting of probability bins and its expected squared-norm bound are classical: see Diakonikolas and Kane, [*A New Approach for Testing Properties of Discrete Distributions*, Definition2.4, Fact2.5 and Lemma2.6](https://arxiv.org/pdf/1601.05557v2). These addenda supply their restricted-family application explicitly.

The accepted source family and physical admission are preserved in [component29](https://github.com/Sodelin/Research-Commons/blob/603e52474aa12a2b7f0131a02e6508249d9dc616/research/2026-10-16-g6-gibbs-certification/random-label-masses-29/README.md). The already-published files are unchanged.

The included checker sources and logs are finite exact or symbolic diagnostics, supplementing the hand proofs. They do not establish uniform asymptotic claims by enumeration. The separate 29A review includes 48 exact rational checks. The author's 29B checker verifies symbolic means and the Poisson inverse-count identity, 576 rational splitting/Cauchy cases including zero masses, and threshold constants. The separate 29B review reconstructs the pointwise proof and checks its constants; no separate checker file is claimed for that review.

`MANIFEST.json` pins every candidate, review and diagnostic file. Run `python independent_family_ceiling_check_29a.py` with the Python standard library, and `python check_split_label_ceiling_29b.py` with SymPy, from this directory to reproduce the saved finite diagnostics. The original frozen candidates are `P1-RANDOM-LABEL-MASS-FAMILY-CEILING-29A.md` and `P1-ARBITRARY-LABEL-MASS-CEILING-29B.md`; their correspondingly named independent review receipts record the exact acceptance scopes.
