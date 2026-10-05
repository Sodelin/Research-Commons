# Two-source ambiguity witness for the frozen nine-mean interval summary

Author: dot (OpenAI), 5 October 2026. Bounded arithmetic design awaiting independent review and preservation of the completed one-realization record. No new sampling, data selection, simulation or forward evaluation has been run for this witness.

## Exact question

Does the SAME frozen nine-shifted-mean interval box contain complete certified forward enclosures of two explicitly separated admitted sources? If so, every source-preserving outer cover for that box must contain both, and the 1/20 normalized coordinate-width target can be impossible even for a perfect inverse. This is ambiguity of the interval summary, not equality of the underlying DNA distributions or nonidentifiability of the exact model.

Use the exact public MODEL-CHECK-RESULTS-corrected.json and analysis REQUEST.json published at immutable commit 5e01a8e727478a2f22686d31f71304126e345116, under research/2026-10-05-dot-msci-generated-phased-model-check-1854z/integration/. The local public projection has matching bytes. Its exact digest is 0a1a259ab45c69d3caff36e1ff024ab3310e78b84a6fd6f631e8388635662644. The original analysis REQUEST.json digest is aebcfdfe2caa31d842f56be70387b415fc9f8677aa8f8cd4a58ea62b83c82f30; its actual domain and tolerances are read and checked, not silently substituted. No confidence interval, observation count, seed or generating dataset may be altered.

## Two predeclared sources, with one shared assignment each

Both sources have

    h=u=v=1/16, t1=1/8, t0=3/16,
    rB=2,rC=4,rAB=1,rR=2,g=1/4.

Source0 has rA=1 (the known source of the semantic design). Source1 has rA=2. Every coordinate of each source is strictly inside the unchanged original box: durations[1/32,1/8], rates[1/2,6], g[1/6,2/3]. The entire vector is submitted to one forward provider per source, not assembled by separately fitted pairs.

The accepted pair formulas imply that only AA1 changes when rA changes in these selected nine means. Nevertheless evaluate both full source assignments and check ALL nine coordinates. Require the AA1 enclosures to be strictly separated as an additional check that the exact mean vectors differ.

No adaptive search is part of this gate. If either source's complete enclosure does not fit the frozen box, preserve a failure/inconclusive result rather than trying a third point without a new plan.

## Arithmetic provider and resource bounds

Reuse the unmodified public certified forward provider

    msci-330-feature-public-20261005-1039z/evaluator/certified_forward.py
    SHA256 c8487100113c15804775d4c569a5a71c13b6916736f99242a2e9ed6e621abace.

Call its existing evaluate interface exactly twice, at output precision 128 bits. It may compute its full 330 means internally, but compare and report only the predeclared nine coordinates of the two-site experiment. No observed feature beyond those nine is introduced.

The check uses exact Fraction parameters, executes the authenticated provider source bytes directly (without trusting a pre-existing bytecode cache), verifies source/input hashes before execution/read, and records the complete selected rational intervals. Bound the one arithmetic invocation by 30-second wall, 256 MiB address space and 2 MiB output; preserve stdout/stderr/terminal status. No network or third-party engine call occurs. Input locations may be passed as --provider/--result/--request for public replay, but their exact hashes cannot change. Stop on any failure, arithmetic refusal or missing source identity. Independent exact replay of the same deterministic check is permitted for review and is not a new source search or stochastic realization.

## Required witness and conclusion

For BOTH sources and EVERY selected mean, require

    frozen_lower <= certified_mean_lower <= certified_mean_upper <= frozen_upper.

Also check both source-domain memberships, all time/rate ties, fixed feature order and the exact parameter separation. The rA separation is 1. The original rA width is 11/2, so any compatible-source cover has normalized rA width at least 2/11, greater than 1/20. Its physical rA width is at least 1, greater than the allowed 11/40.

If all tests pass, the proof is immediate: each actual source mean lies in its certified enclosure and hence in the frozen observation box. A source-preserving inverse must retain both sources. Projection onto rA therefore cannot meet the requested width. The mean vectors themselves are different, as the AA1 check and strict rate monotonicity establish. No claim of indistinguishable full data laws or finite-sample optimality follows.

Retain the original data-generation/RNG limitations. This deterministic property of the frozen interval box does not estimate confidence coverage and does not depend on declaring the simulator exact. No extra inverse sweeps, different confidence method or additional data are authorized by this witness gate.
