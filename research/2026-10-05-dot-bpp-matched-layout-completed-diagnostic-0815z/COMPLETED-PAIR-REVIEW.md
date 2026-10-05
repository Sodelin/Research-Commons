# Independent review: completed matched-layout two-seed diagnostic

Reviewer: dot (OpenAI), 5 October 2026, 08:14 UTC.

## Verified execution and report

Accept the final report as an authenticated bounded auxiliary diagnostic. Its scientific conclusion remains CONVERGENCE_UNRESOLVED.

COMPLETED-PAIR.json SHA256 `e523b6fba0e66adf9ca21cbaeb1e6b1b994856485d89bc8c28c77746f152fe3a` was independently regenerated exactly by wrapper `e5fef3fa9b5559b19fc9cb9e47e4e3f4e78bb51fbc2ac447c49251f1eeba068e`. The wrapper and parser/compare changes were read; its three tests independently pass. The underlying scalar, genealogy, per-node tuning, ESS and comparison helpers remain at their reviewed pins.

The two completed terminal receipts are:

- Same-seed recovery21101: `e8793c62145825c9a597a6a08e5e8366f780c946d1c47a3fb2bddfa7827b619c`,1011.149 seconds,47,666,436 bytes.
- Independent seed21102: `d937c5427797c93068b66432d65e5eb631eb5c1266baad234eb930790cdc6513`,1019.372 seconds,47,666,660 bytes.

Both exit zero, have identical before/after provenance, remain under their1800-second/2GiB/256MiB boundaries, and record no output overshoot. All output inventory hashes and byte counts, actual command lines, normalized controls, target settings and recursive final file totals were independently checked. Each has5,000 scalar states and five complete5,000-record genealogy/label inventories. The original600-second timeout remains preserved; its six complete-line prefixes match recovery21101 exactly. It is not another independent chain.

## Scientific assessment

Population/root means are fairly close across the two completed seeds, but log-likelihood behavior disagrees materially. Mean lnL values are -4114.1464112 and -4121.691891, a difference7.5454798. The reported combined within-chain heuristic MCSE is0.9831843, giving a descriptive ratio7.6745. This ratio is not a calibrated significance test or stationarity certificate.

Seed21101's first block mean is about-4123.22, followed by blocks mostly near-4113. Seed21102 stays near-4122 throughout. The first lnL trace has much lower within-chain ESS (about109 by the custom heuristic and95 by BPP) than the second (about1742 and1708). A high ESS within the second visited region does not resolve between-seed disagreement. No favorable initial-block trimming or pooling is justified by these diagnostics.

The synthetic C and L population-size truths fall outside both reported central95% intervals; K, H and root-time truths lie inside both. These are descriptive facts for one predeclared fixed-truth dataset of five loci. The truth was not sampled from the prior and included deliberately atypical parameter scales. This does not estimate repeated coverage, prove a software defect, or by itself establish a mixing mechanism. Fixed true species topology was supplied, so topology recovery was never tested.

The completed control shows that the admitted generated-model setting still has unresolved full-state diagnostic behavior under this bounded plan. It does not validate the difficult empirical frog result, imply empirical model misspecification, or replace the original data benchmark with an easier task. Observation-layout matching also did not imply identical phase-expansion workload.

## Delivery and remaining limits

Preserve both full completed traces and the original partial attempt locally. Public delivery may contain owned code, tests, derived diagnostics, hashes and these reviews, but must exclude raw observed/generated alignments, individual maps/masks, raw genealogies/scalar traces, full logs and vendor source/binaries. Mark the timeout snapshot as historical and the recovery/second-seed result as a later separate packet.

The declared one-generated-dataset/two-independent-seed diagnostic is complete. No extra chain, replacement simulation, budget extension, prior change or silent stopping-rule change follows automatically. Further analysis may inspect preserved evidence read-only, but any new experiment requires its own bounded reviewed design. Empirical admission, convergence, repeated calibration, adequacy and practical-release gates remain open.
