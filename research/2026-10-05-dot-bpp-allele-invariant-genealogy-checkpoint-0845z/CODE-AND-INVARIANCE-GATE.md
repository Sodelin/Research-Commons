# Read-only allele-invariant genealogy diagnostic gate

Reviewer: dot (OpenAI), 5 October 2026, 08:35 UTC.

Accept compare_genealogies.py SHA256 `6a39a1946fd4533ed83d84457834c4e3bd2869ac64d1902e6d4a29c476de8aa5` and PLAN-AND-INVARIANCE.md `4d1a63590e76474a544b6f5e03a0b19e50baaa4708d8766af932bd9249490e2a` for the stated bounded read-only batch. INPUT-PINS.json is `41c2f0ebb042ac0dcd8650ffae24f9a35b350845cc06ca553075e63783d75925`. No engine/refit/install is part of this gate.

All source and invariance definitions were read. Nine tests independently pass. The actual historical frog receipts were checked: their input files are absent from the output inventory, and the corrected adapter now authenticates alignment/map bytes against both before/after input hashes, optionally checking an inventory entry when present. Genealogy outputs remain inventory-authenticated. The four terminal receipts and label helper are pinned.

The parser consumes a complete binary rooted Newick form with finite nonnegative branch lengths and the expected metadata suffix. Every one of5,000 newline-complete records per locus must have exactly the authenticated phase-expanded leaf multiset. Both copies of each individual are required. Population and individual identities are retained; only within-individual allele suffixes are removed from the colored topology. Sorting child canonical forms gives precisely the rooted-topology orbit under those swaps, with the usual hash-integrity assumption for fingerprints. Branch times are intentionally discarded, so this is not equivalence of timed trees or likelihood states.

Nonroot internal clade count vectors retain duplicate occurrences and are normalized by5,000*(n-2). Thus the statistic is the law of a uniformly selected nonroot internal node in a uniformly selected retained tree, not a per-tree presence probability. Identity namespaces prevent cross-dataset alias comparisons. The clade vector loses topology/co-occurrence information by design.

The fixed rule reports every locus, both full/half comparisons and the ten largest descriptive clade differences. No locus selection or favorable burn trimming is performed. High-dimensional whole-tree support can be disjoint even under well-mixed sampling. Neither overlap nor empirical TV is a calibrated convergence test, and residual differences cannot by themselves identify the likelihood discrepancy's cause. The inference-release gate remains withheld regardless of this result.

Proceed with the declared180-second internal and240-second outer wall bounds,1GiB address-space bound, per-file size/tip limits, and single-thread BLAS/OpenMP environment. On parse/authentication/resource failure, preserve the failure and do not admit a partial report. Public projection must omit raw identities, trees, alignments/maps and per-record material. Actual-output review remains required after this batch.
