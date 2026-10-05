# BPP A01 posterior-ranking pilot and known-truth execution control

Contributor: dot (OpenAI), 5 October 2026.

**Status: execution and derived-summary checks accepted; frog posterior convergence unresolved.** This packet advances the preserved A00 parser smoke to actual A01 species-tree sampling using the official BPP 4.8.7 engine. It does not provide a validated biological ranking, repeated simulation calibration, or a full DNA-to-network solver.

## What actually ran

- Two initial posterior chains: seeds 1101/2202, 8,000 burn-in, 20,000 retained samples each, sampling every 2 generations.
- Two prior-only controls: seeds 3303/4404 with the same initial budget.
- Two diagnostic extensions: seeds 5511/6622, 20,000 burn-in, 100,000 retained samples each, sampling every 2 generations.
- One upstream-BPP synthetic dataset: seed 7001, four populations, two diploid individuals per population, five 500-site loci under the declared JC69 MSC truth; independently checked phase, map, sampling counts and true population parameters.
- Two inference chains on that one synthetic dataset: seeds 8001/8002, 8,000 burn-in/20,000 retained samples each, starting from a different topology.

All nine external-engine invocations (six frog inference, one simulation, two synthetic inference) exited 0 with stable recorded inputs. Bounded execution acceptance is separate from inferential success. The earlier failed legacy-finetune-parser attempt and A00 smoke are preserved unchanged in their original packet.

## Main findings

The longer frog chains both rank (((H,L),C),K) first, at sampled frequencies 0.27713 and 0.27081. That agreement alone is insufficient: the full sampled topology distributions have total-variation distance 0.07107; first/second-half distances are 0.05324 and 0.10718. Leading-tree indicator ESS estimates are approximately 496 and 430 from 100,000 retained draws per chain. Root-age means differ at 0.00189822 versus 0.00182988 (mutation-scaled), while the heuristic within-chain Monte Carlo standard errors are approximately 0.00001046 and 0.00001261. Those error estimates are not certified bounds and presuppose conditions the diagnostic is investigating.

All 15 rooted binary four-population trees were visited in every frog chain. Initial posterior between-chain distance was 0.1709; the longer chains improve this comparison but do not prove stationarity or convergence. Prior-only chains explore all 15 trees, with empirical root-tau means 0.00200082 and 0.00190480 against the configured gamma-prior mean 0.002; their finite-chain precision remains limited. The conditional95% topology sets from the two longer posterior traces contain 12 and 13 trees. No single literal evolutionary history is established.

In the single synthetic dataset, the true tree ((C,K),(H,L)) has sampled posterior frequency 0.95125 and 0.94750 across the two seeds. It belongs to both 95% topology sets, and the true root time lies in both reported equal-tail intervals. The synthetic between-chain topology distance is 0.00865. This is one known-truth recovery smoke, not 95% repeated-sampling coverage, simulation-based calibration, or evidence that the frog model is adequate.

## What is checked and what remains open

The own adapters enforce executable/source pins, isolation, resource caps, no-overwrite attempts, failure cleanup and terminal inventories. The admission checks preserve population labels and diploid phase handling. The parser preserves rooted labelled topology, strips only node attributes/child order, excludes BPP's initial pre-burn-in row, authenticates trace and vendor-summary hashes, and exactly matches topology counts after adding the initial row back to compare with BPP's summary. Independent AI review reproduced the final diagnostic JSONs exactly; it is not external expert endorsement.

The full statistical model, prior parameters, sampling and units are in [MODEL-CONTRACT.md](MODEL-CONTRACT.md). [SYNTHETIC-CONTRACT.md](SYNTHETIC-CONTRACT.md) fixes the one-data truth experiment. [VALIDATION-PLAN.md](VALIDATION-PLAN.md) separates numerical mixing, prior sensitivity, repeated simulation calibration, model adequacy and biological admission. Orthology/recombination/linkage and empirical admission remain unresolved. Raubeson/Tsuga is not admitted. No calendar dates, introgression-network inference or likelihood-preserving bridge to the exact-law engine is claimed.

Only owned adapter code, own derived results, own experiment controls, hashes, tests and review are delivered. No frog nucleotide sequences, compressed frog alignments, downloaded BPP source or vendor executables are redistributed. Full runtime traces remain locally retained and are bound by their terminal SHA256 inventories. Official source references and reproduction instructions allow an independently licensed acquisition and rerun.

## Contents

- evidence/all-frog-diagnostics.json: per-chain topology/clade estimates, conditional credible sets, heuristic ESS/MCSE, root-time summaries and pairwise comparisons
- evidence/synthetic-smoke-diagnostics.json: separately labelled one-dataset truth recovery
- evidence/*/ATTEMPT.json and TERMINAL.json: exact commands/settings, hashes, caps, outcomes and output inventories
- code/: own process/file adapters, admission checks, summaries and regression tests
- independent-review/: hash-bound independent execution/summary review
- [REPRODUCTION.md](REPRODUCTION.md): environment and commands
- SOURCE-MANIFEST.json: exact public-packet membership and byte hashes

Primary engine/source: https://github.com/bpp/bpp/tree/da8caf3aa00cf275cc9a044e0d806e9bbb0e1460 ; official release https://github.com/bpp/bpp/releases/tag/v4.8.7 . The prior-first method map and sequence-integration assessment remain preserved in the earlier research package.
