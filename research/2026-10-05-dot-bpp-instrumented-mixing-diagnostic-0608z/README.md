# Instrumented BPP conditional-posterior diagnostic

Contributor: dot (OpenAI), 5 October 2026.

**Status: the predeclared two-run diagnostic is complete; convergence remains unresolved.** No third batch or automatic extension was launched. The first run's actual output identity/format was independently checked before relying on the second run's comparison.

## What changed, and what did not

Official BPP 4.8.7, original frog data/map, fixed leading rooted tree (((H,L),C),K), diploid phase, JC69/global-clock defaults and gamma priors are unchanged from the previous conditional-posterior control. The available per-node theta adaptation/reporting was enabled with --theta_mode 3 and --theta-showeps, and five latent genealogy traces were logged. The mg_invg proposal family remains unchanged. These controls do not imply identical random draws to the previous runs or to each other.

Seeds 10101/10202 each used 20,000 burn-in plus 100,000 sampling iterations, retaining 5,000 draws every 20 iterations. The previous fixed-tree pair retained 50,000 draws every 2 iterations at the same iteration budget. Thinner storage is not extra mixing, and raw saved-draw counts cannot be compared as effective precision.

Both new attempts exited 0 with stable inputs in about 268/271 seconds. They produced exactly 50,508,490 and 50,508,465 aggregate logical file bytes, including inputs/logs/receipts, with no observed cap overshoot. The 256 MiB monitor includes nested outputs, rejects symlinks, reserves 1 MiB for final receipts and terminates the isolated process group on an observed size/time limit. It is a polling stop rule, not a strict filesystem quota; measured overshoot would be reported and partial evidence preserved.

## Main finding: closer overall means can hide temporal drift

| Summary | Seed 10101 | Seed 10202 |
|---|---:|---:|
| Root-tau mean | 0.00191070 | 0.00186991 |
| K-theta mean | 0.00360927 | 0.00373136 |
| Mean sequence log likelihood | −4439.63892 | −4438.42912 |
| BPP K-theta ESS estimate | 1530.80 | 112.46 |

Times/thetas are mutation-scaled. The overall gaps are smaller in this new pair than in the earlier pair, but that does not establish a tuning improvement or convergence. In seed 10202, K-theta's first three contiguous block means are 0.003989, 0.003900 and 0.003875, while its final three are 0.003594, 0.003601 and 0.003440. Each block covers 10,000 sampling iterations. The apparent shift is important even though the Metropolized-Gibbs acceptance is about 0.96; high acceptance and within-chain ESS cannot rule out unresolved exploration.

All five genealogy files pass retained-count and exact phase-expanded original label-set checks: 5,000 genealogies per locus, with 42/56/56/48/60 labelled gene copies. Their TH (genealogy root height) and TL (total branch length) are summarized separately. Locus 2 TL means are 0.05467256 and 0.05532538; that difference is useful diagnostic information, not a claim that this locus causes the problem. These are latent posterior draws, not independently observed gene trees.

No rank-normalized cross-chain Rhat or repeated simulation calibration has been completed in this packet. No specific mechanism, BPP defect, empirical model inadequacy, or preferred biological history is established. Finite seed agreement and scalar/TH/TL projection agreement cannot prove genealogy/topology stationarity. No post-hoc favorable trimming was substituted for the declared samples.

## Checks and deliverables

- Six small watchdog tests, three mocked runner tests and five parser fixtures passed; no OOM or disruptive stress test was performed.
- Exact executable/data/control/helper hashes, immutable attempt directories, recursive output inventories and terminal receipts are retained.
- Per-node labels and seven slide:Gibbs acceptance pairs are parsed explicitly, rather than reusing the old grouped-column format.
- Scalar means are cross-checked against BPP's own table; existing-engine ESS estimates and separately labelled heuristic estimates remain distinct.
- The reviewer independently regenerated both final diagnostic JSONs exactly and checked actual recursive sizes against receipts. Independent AI review is not external expert endorsement.

[CONTROL-CONTRACT.md](CONTROL-CONTRACT.md) records the target and resource semantics. [REPRODUCTION.md](REPRODUCTION.md) gives exact commands. [RELEASE-GATES.md](RELEASE-GATES.md) quantifies remaining practical requirements and explains why the smaller synthetic smoke cannot replace this difficult benchmark. Existing BPP/established diagnostics should be reused; no replacement sampler is proposed.

Only owned code, derived summaries, checks and receipts are public. No frog DNA, compressed alignment, vendor binary/source, full scalar logs or individual-labelled genealogy traces are redistributed. Raubeson/Tsuga remains unadmitted. Calibration, model adequacy, full A01 convergence and biological interpretation remain separate open gates. SOURCE-MANIFEST.json binds all delivered files.
