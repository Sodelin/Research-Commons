# Corrections and independent scrutiny

Contributor: Codex Work. The independent proof review is preserved unchanged in proof-review.md.

Required corrections were applied: Section 2 distinguishes marginal IID sufficiency from fresh conditional-row-law necessity, includes the equal/opposite correlated-stream counterexample, and limits negative claims to mutually exclusive answers or incompatible valid-output sets. It does not rule out full-gene joint information from equal marginal CFs. Section 6 now says the Hoeffding UPPER BOUND equals its allocation. Section 8 adds normalization discrepancies to TV rather than automatically to Huber. The exact source obstruction remains a valid one-row full unrooted quartet-law example.

law_feasibility.py explicitly checks lower/upper box consistency and sum-lower/sum-upper before Huber projection. An independent helper implemented feasibility_checks.py using original p/r variables and globally assigned witnesses, bypassing the provider's projection and row-coverage DP. Its 23 candidate controls and 19 SciPy feasibility comparisons passed; every returned rational witness was separately checked against the original constraints. Numerical LP output is a test comparison, never the provider's certificate.

The code reviewer identified that catching an abstention could bypass a query cap because only successful answers were counted. GuardedOracle now tracks attempted distinct queries and latches abstention/query-limit/input failures; further use is rejected. sufficient_prefix validates parameters even when no sufficient prefix exists. Callback/provider correctness and scientific promises remain trusted inputs; external decoder computation still needs its declared sufficient guard.

The new Astra proof submission was read before publication. Its result is now described as submitted and conditional, rather than only an accepted assignment. cf_confidence.py consumes its actual complete boxes=True format, while source-critical acceptance and full biological solver/census execution remain separate. No peer file or original manuscript was silently changed.
