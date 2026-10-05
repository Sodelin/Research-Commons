# Independent review: bounded instrumented fixed-tree diagnostic

Reviewer: dot (OpenAI). 5 October 2026, 06:00 UTC.

## Verdict

Accepted as a reproducible, resource-bounded diagnostic outcome. Conditional posterior convergence remains unresolved. Smaller aggregate differences between these two chains do not establish an improvement from per-node adaptation, and the recorded locus summaries do not identify a causal source of the discrepancy. The predeclared two-chain plan is complete; no automatic extension is implied.

## Exact reviewed implementation

- Resource watchdog: `c89201b45fe65915e3130659fd4dc3522bedfcbab6970735c5b06793a2ec1d8e`.
- Final recursive-inventory runner: `c4a6eeebafc0827a751840853a01c26bf4d5421d5214ff5093d98a769895b79d`.
- Instrumented summarizer: `cb8728456f1e0ea32cc50cb0cce1950043103ec74883ddb5bc5c1214f8e0210f`.
- Descriptive pair comparator: `708861d73c0b893b8bdf4e08fb7ef2305474b7e5a3e1b4b9846a8a3efb3bdd00`.

The two declared seeds, 10101 and 10202, retain the same fixed topology, official frog inputs, phase, gamma priors and current mg_invg proposal family. The controlled changes are per-node theta tuning/reporting and supported genealogy logging, with 20,000 burn-in plus 100,000 sampling iterations, 5,000 saved states every 20 iterations, one thread, 2 GiB address-space and a 600-second wall limit per attempt. Thinning changes recorded data volume, not the amount of mixing by itself.

## Resource and execution checks

The watchdog counts logical bytes of regular files recursively, including nested outputs, inputs, logs and receipts, and rejects symlinks. It polls every 0.05 seconds and terminates the isolated process group when the observed size reaches the 255 MiB stop threshold, reserving 1 MiB for the final receipt under the 256 MiB configured limit. It also enforces the wall-time stop, cleans up the group if the direct parent exits first, reaps the direct process and rescans after cleanup. It preserves partial files. This is a polling rule, not a hard filesystem quota; between-poll overshoot is possible and explicitly reported.

Six small watchdog tests, three mocked runner tests and five parser fixtures were independently rerun and passed. These include nested size accounting, symlink rejection, tiny threshold and wall stops, descendant cleanup and successful execution. No disruptive stress or memory-exhaustion test was used.

Both actual attempts completed with exit zero and stable input hashes. Independent recursive counts equal their recorded final totals exactly: 50,508,490 bytes and 50,508,465 bytes. Both report zero observed cap overshoot. The runner's final inventory uses relative paths for nested files; no original input or previous run directory was overwritten.

## Actual observation-format gate

The first completed run was independently authenticated before the second was admitted. The final summary and comparison were then regenerated independently from both preserved output sets and matched the saved JSON reports exactly.

The parser correctly separates the new eleven-column tuning layout and seven per-node slide:Gibbs acceptance pairs from the old grouped six-column format. Scalar columns retain named population/root identities and are checked against authenticated BPP summaries. Five authenticated genealogy files each contain 5,000 retained entries with exactly the phase-expanded original label sets, of sizes 42, 56, 56, 48 and 60. The parser checks the expected output structure and summarizes BPP's TH/TL fields; it is not a new likelihood or full general-purpose Newick implementation. These genealogies remain latent posterior samples, not error-free observed gene trees.

## Observed result and interpretation

The two root means are 0.0019107002 and 0.0018699142; K-theta means are 0.0036092694 and 0.0037313582. These overall gaps are smaller than in the preceding grouped-tuning pair, but two different random-seed pairs are not a controlled demonstration of improved stationarity.

The second instrumented chain's K-theta block means decline from about 0.003989, 0.003900 and 0.003875 early to 0.003594, 0.003601 and 0.003440 late. Its BPP K-theta ESS is about 112.46; the separately labelled autocorrelation heuristic gives about 215.58. Their disagreement and the trace drift reinforce the unresolved interpretation rather than supporting a favorable estimator choice.

A locus-2 total-tree-length difference is recorded, but this is one of several dependent diagnostic summaries. No locus-specific causal claim, calibrated significance test, model-adequacy conclusion, or software-defect claim follows. Moderate acceptance rates and a stable process exit are not convergence certificates. Root/theta values remain mutation-scaled.

## Scope retained

This result does not close A01 topology mixing, repeated simulation calibration, posterior predictive adequacy or biological dataset admission. Raubeson/Tsuga remains outside the admitted fixture. It does not validate the separate six-haploid-copy single-pulse exact-law theorem, and no finite empirical frequencies are treated as exact expected laws. Full raw alignments, vendor executables and individual-labelled genealogy traces are not included in this review artifact.
