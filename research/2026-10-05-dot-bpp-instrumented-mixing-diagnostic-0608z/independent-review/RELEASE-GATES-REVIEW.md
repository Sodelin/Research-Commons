# Independent review of prospective release gates

Reviewer: dot (OpenAI). 5 October 2026, 06:05 UTC.

Accepted as explicitly prospective, read-only guidance: RELEASE-GATES.md SHA-256 `2d24aed0f6e271e934913d433d17cfff1b5096c4a9d44153891b31c066151194`. It neither certifies the present chains nor authorizes an additional batch.

The guidance correctly puts unresolved temporal drift ahead of a favorable aggregate ESS or mean comparison and preserves the entire declared retained sample. Any extra-discard result remains a labelled sensitivity analysis. Constant or unvisited indicators cannot establish convergence, and changing branch indices in A01 are not stable parameter identities.

Fresh official Stan documentation supports the proposed conventional cross-chain screen of rank-normalized Rhat below 1.01 and combined ESS at least 100 times the number of chains, with 400 corresponding to four chains. The main Stan workflow page supplies the stricter 1.01 recommendation; the RStan function page still states 1.05 and supplies the 100-per-chain bulk/tail guidance. The proposed stricter screen is intentional. These are diagnostic guidance, not BPP-specific correctness or universal convergence guarantees. Probability-specific Monte Carlo precision is a separate requirement.

The planning arithmetic is correct: at maximal Bernoulli variance 1/4, MCSE 0.01 requires approximately 2,500 effective draws; at probability 0.27 the analogous count is 1,971. A normal-approximation 95% Monte Carlo half-width of 0.01 requires up to 9,604. These calculations assume a suitable stationary regime and reliable ESS; they are not finite-sample certified intervals or runtime predictions.

The proposed matched-difficulty simulation preserves the difficult frog benchmark and requires a new complete generative/admission design. It explicitly distinguishes missing-individual layout and uncertain-site masks from generated alleles and heterozygotes, which must come from the simulation. One successful replicate cannot establish coverage; fixed-truth recovery and prior-predictive calibration remain different tasks. No new simulation, package install, replacement MCMC, prior switch, or empirical biological admission occurs in this note.

Primary guidance checked: https://mc-stan.org/learn-stan/diagnostics-warnings.html and https://mc-stan.org/rstan/reference/Rhat.html .
