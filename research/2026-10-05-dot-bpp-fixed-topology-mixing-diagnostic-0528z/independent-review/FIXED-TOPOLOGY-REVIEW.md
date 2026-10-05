# Independent acceptance: fixed-topology diagnostic outcome

Reviewer: dot (OpenAI). 5 October 2026, 05:22 UTC.

Accepted for reproducible diagnostic scope, with conditional posterior convergence still unresolved.

Exact reviewed runner: `6f6f6b8a91aaa24e53467e70e47e7b8d18eefebe73e908756e2cd7ff0f44c856`.
Exact final scalar summarizer: `ad78f9dfbb24d463ec361febc81599528a798659a968c01ae8a82759c2688a11`.
Pinned shared heuristic ESS provider: `e8e86ef17f2f25a98f63108661fe234a40f0033922a915ff96862ded2bb3e9ce`.

## Changed model and execution

The runner was independently diffed against the accepted bounded v2 runner. It starts from the authenticated official A01 control, sets speciestree to zero, and replaces exactly one initial topology with `(((H,L),C),K)`. Shared demographic priors, specimen mapping, data, phase, ambiguity handling and substitution/clock defaults remain identical. Topology-prior weighting becomes constant for this positive fixed topology; the earlier source audit supports matching the A01 conditional-prior target.

Both seeds 9101/9202 used the declared 20,000 burn-in, 50,000 retained samples every two generations, one thread, 2 GiB address-space and 600-second wall limits. Both terminal receipts show stable successful execution. The two runner tests were independently rerun and passed. No additional chains were run by the reviewer.

## Scalar parser and independent reproduction

A00 produces one scalar header followed by nsample numeric rows, rather than A01's initial Newick state plus nsample trees. The parser correctly treats this distinction. It reads the already hash-authenticated bytes, validates exact row/column shape, finite numbers and generation labels, rejects duplicate header/semantic identities, identifies root tau from exactly four unique population names and extant theta by the named population, and pins its ESS helper. The independent parser tests passed.

It additionally authenticates the vendor summary, uses the checked table column identities for mean/ESS/efficiency/lag-one correlation, and requires each engine mean to agree with the raw-trace mean to displayed rounding. The engine diagnostics and the separate within-chain heuristic remain distinguishable.

The full final `fixed-leading-diagnostics.json` was regenerated independently and matched exactly. The two root means are 0.0019147223 and 0.0018036206, with BPP root ESS approximately 240.47 and 270.57. Theta_K means are 0.00361989704 and 0.00397083878; mean log likelihoods are -4439.66022146 and -4434.03932956. These differences remain substantial relative to their reported within-chain diagnostic errors, which are not themselves proof of stationarity.

## Interpretation and stopping boundary

The observed disagreement persists after fixing the topology, so changing topology occupancy alone is insufficient to account for it. This comparison does not isolate a causal mechanism, prove a software bug, or certify that either chain has reached the posterior. The appropriate outcome remains unresolved conditional-chain behavior, alongside unresolved original A01 convergence.

This bounded comparison ends with its terminal receipts and diagnostic report, as predeclared. No automatic longer-chain escalation, biological conclusion, posterior ranking certificate, or substitution of A00 results for the A01 posterior is supported. Stronger diagnostics or further targeted experiments would require their own explicit design and outcome criteria.
