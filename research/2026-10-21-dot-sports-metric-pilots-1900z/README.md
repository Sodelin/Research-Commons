# Sports metric pilots: first reviewed checkpoints

Author: dot (OpenAI-assisted research), prepared for Nolan. Date: 2026-10-21.

## Scope and status

Nolan requested separate basketball and baseball design and independent-review efforts, using existing statistics as baselines and preserving reusable research in Research Commons. These are distinct sports prototypes. They do not close or change G1–G7 or the materials/nanowire master obligations. LLM research remains paused. No predictive superiority or novelty is established.

- [Basketball](basketball/README.md): a support-aware offensive role-portability experiment. An executed synthetic diagnostic compares a common-context baseline with player-specific context slopes. Conditional-mean MSE improves from 8.386006 to 1.993107 when heterogeneous effects are built into the simulation, but worsens from 0.153702 to 0.340440 in the zero-interaction negative control. Units are arbitrary simulated response units squared, not NBA points. No NBA model has been fitted. Missing overlap is demonstrated by two observationally identical training worlds with target means 8 and -4.
- [Baseball](baseball/README.md): a proposed test of handedness-standardized versus matched raw recent changes in a fixed 60-day batting-value forecast. A real one-day ingestion audit inspected 3,704 pitches and 931 completed plate appearances. Seven exact synthetic accounting checks passed. No MLB forecast has been fitted or scored. The review corrected proposed-analysis selection, denominator and exposure-accounting problems; it does not allege errors in established professional systems.

## Coordinating verification

The coordinator independently reran the exact basketball publication script, the baseball seven-assertion synthetic script, and the baseball audit against the already-acquired local CSV. All exited successfully and reproduced the reported figures. This was a replay of the local source snapshot, not an independent reacquisition. The optional baseball downloader was syntax-checked only; the original acquisition used a different ordinary HTTP client.

## Data and publication boundaries

This packet contains original methods, code, synthetic outputs, derived aggregate audits and source references. It excludes private fantasy-account information, raw third-party sports tables, credentials and restricted datasets. Public visibility does not itself grant bulk acquisition, model-training or redistribution permission. Historical ratings revised after refits cannot be treated as archived originally published forecasts.

## Next gates

Basketball requires a permitted complete possession/lineup dataset and verified historical timestamps, followed by score and lineup reconciliation. Baseball requires exact frozen event weights, historically valid features and a multi-season development/evaluation panel. Use matched baselines and chronological holdouts; retain negative findings. The independent reviews and each protocol specify remaining assumptions. Full-scope records are not rewritten for these separately scoped pilots.
