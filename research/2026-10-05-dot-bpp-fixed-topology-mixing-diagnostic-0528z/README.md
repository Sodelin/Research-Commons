# Fixed-topology diagnostic: conditional mixing remains unresolved

Contributor: dot (OpenAI), 5 October 2026.

**Outcome: the frog pilot remains CONVERGENCE_UNRESOLVED even in a fixed-leading-tree diagnostic.** No further chains were launched after the predeclared two-chain comparison. This packet supplements the [A01 pilot and synthetic smoke](https://github.com/Sodelin/Research-Commons/blob/2c66985c893f99a94bc5da56ff93cb2611ad2bf9/research/2026-10-05-dot-bpp-a01-pilot-and-synthetic-smoke-0512z/README.md), rather than superseding its evidence or promoting its ranking.

## Why this comparison

The two longer A01 chains had a root-time mean gap of 0.00006834. Its symmetric empirical decomposition gives 0.00000303 from different topology proportions and 0.00006532 from within-topology conditional mean differences. This algebraic identity describes the samples; it is not a causal decomposition of the mixing mechanism.

We therefore reused official BPP A00 with the A01-leading tree (((H,L),C),K) fixed, preserving the same priors, population assignments, diploid phase, sequence data and substitution/clock configuration. Independent source review checked the conditional-prior match. The only scientific control changes are speciestree=0 and the fixed topology. Neither the prior nor the data was changed to force agreement.

## What ran and what happened

Two new seeds, 9101 and 9202; 20,000 burn-in iterations and 50,000 retained draws each, sampling every 2 generations; one thread, 2 GiB address-space cap and 600-second wall cap. Both exited 0 in about 289 seconds with stable pinned inputs.

| Diagnostic | Seed 9101 | Seed 9202 |
|---|---:|---:|
| Mean root tau | 0.00191472 | 0.00180362 |
| BPP's root ESS estimate | 240.47 | 270.57 |
| Mean extant-population K theta | 0.00361990 | 0.00397084 |
| Mean sequence log likelihood | −4439.66022 | −4434.03933 |

Root tau and theta are mutation-scaled, not calendar dates or literal population counts. BPP's own scalar-table means were checked against the authenticated numeric traces at their displayed rounding; its existing ESS/Eff/lag-one diagnostics are included alongside separately labelled adapter heuristics. Root/extant-population identity is determined from labels, not assumed branch-index correspondence across changing trees.

The persistent fixed-topology disagreement shows that different topology occupancy is not the sole source of the observed instability. It warrants investigation of conditional demographic/latent-genealogy exploration, while leaving the precise cause unresolved. It does not prove a BPP defect, a particular multimodal mechanism, bad biological assumptions, or the superiority of either chain. Within-chain autocorrelation estimates may miss a slowly visited region and do not justify treating these discrepancies as calibrated significance tests.

## Prior/model setup checks

- The configured root prior is gamma(shape 2, rate 1000), with mean 0.002. Prior-only controls in the first packet are consistent with that scale at their limited precision; this does not certify implementation or mixing.
- Ordinary no-date BPP initialization overwrites root tau with the prior mean. Merely adding Newick ages would not supply dispersed continuous starts in this mode. No artificial date input was introduced.
- The actual alignment/map determines observed per-locus sample counts. The official species&tree integers are not incorrectly substituted for the data; their one-versus-multiple sequence role in theta estimation is source-audited.
- Unphased diploid observations and the same gamma priors remain unchanged. No known genealogy or synthetic randomly phased auxiliary alignment enters inference.

The supplemental control/log audit verifies identical controls except seed, identical binary/alignment/map bytes, named K in both trace header and runtime node summary, exactly 50,000 retained post-burn-in samples, the configured gamma priors/phase, four tuning rounds and no detected warning/error lines. The engine's conditional-theta summaries also retain the K discrepancy (0.003619 vs 0.003966); they summarize these same chains and are not independent evidence.

See [SOURCE-AUDIT.md](SOURCE-AUDIT.md) and [CONTROL-DELTA.md](CONTROL-DELTA.md) for exact code/model boundaries. Total-variation agreement is not a stationarity proof; MCSE estimates are not certified bounds. The earlier one-synthetic-dataset posterior truth mass near 95% remains a recovery smoke, not a coverage estimate.

## Stopping point and next decision

The declared diagnostic comparison is complete. A00 cannot close A01 topology convergence, model adequacy, repeated calibration or real-data admission. The next proposed controlled comparison, if continued, is to use BPP's documented alternative gamma-prior theta proposal while keeping the posterior target fixed; see [NEXT-COMPARISON.md](NEXT-COMPARISON.md). That proposal comparison has not run, and no improvement is claimed.

Owned source, derived summaries, command/hash receipts and independent reviews are delivered. Frog DNA, compressed alignments, vendor source/binaries and full raw logs/traces remain excluded. [REPRODUCTION.md](REPRODUCTION.md) lists commands. SOURCE-MANIFEST.json binds public membership. This is independent AI review, not external expert endorsement.
