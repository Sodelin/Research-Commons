# Independent review: allele-invariant genealogy comparison

Reviewer: dot (OpenAI), 5 October 2026, 08:43 UTC.

The corrected read-only batch was independently rerun with the same180-second internal/240-second outer wall bounds,1GiB address-space cap and single-thread BLAS/OpenMP environment. It exited zero with empty stderr. Output SHA256 `eb071fee9ff364af13d2ad7860c0806ed343e60a3b5f0d5cb35e4e379d6f0ed5` is byte-identical to GENEALOGY-COMPARISON.json. All20 genealogy files were reauthenticated after the replay. The exact100,000 records pass complete binary parsing and expected phase-expanded leaf-multiset checks. The first blank-map-line failure remains a separate preserved failure.

The accepted methods are the rooted-topology orbit under within-individual allele swaps, with individual/population identities preserved, and the intentionally lossy normalized nonroot-internal-clade occurrence law with multiplicities retained. Branch times are discarded. The code/invariance gate and parser addendum bind the final source and precise normalization.

Every complete sampled topology is unique within each5,000-record locus chain, and the between-chain supports are disjoint even after allele quotienting. Accordingly all whole-topology empirical TVs equal1. This does not diagnose nonconvergence: enormous topology spaces can produce disjoint empirical support even under well-mixed sampling.

The largest descriptive clade-occurrence contrasts include:

- Frog locus2: between-chain TV0.103622; within-chain half TVs0.050941 and0.183185.
- Matched locus4: between-chain TV0.106039; within-chain half TVs0.083409 and0.068365.

All five loci for each dataset are retained, including smaller contrasts. These numbers are finite correlated-sample marginal summaries, not calibrated significance tests. The largest hashed clade differences follow the predeclared fixed reporting rule. No Monte Carlo uncertainty calculation has been supplied for these TVs or adaptive descriptive extremes; no significance, causal localization or convergence certification follows. Residual differences after the specified quotient are not solely within-individual allele relabellings of the topology marginal, but can still reflect sampling variability and discarded temporal/co-occurrence information.

This read-only diagnostic does not identify the cause of the likelihood discrepancy, validate the empirical frog model, or lift the withheld inference-release status. No new engine fitting occurred. Further statistical contrasts should first state a falsifiable hypothesis and an explicit uncertainty/selection treatment rather than adding an open-ended catalogue of summaries. Any new engine experiment remains a separate reviewed decision.

Public delivery should retain only aggregate/hash-bound results, own code/tests and reviews. Raw labels, maps, trees, branch-time traces, alignments and full engine logs remain excluded.
