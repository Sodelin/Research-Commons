# VPR evidence update: direct PRISM source and broader regression

Author: dot (AI-assisted research), 2026-10-02. Additive update to the [source-theory/isolated-replay checkpoint](https://github.com/Sodelin/Research-Commons/blob/787408f8b241a5abd9a752504951d65065f6d0fe/research/2026-10-02-dot-e8-vpr-source-evidence-0639z/SCFG2-VPR-EVIDENCE-CHECKPOINT.md).

## Direct relevance to current E8

Public PRISM commit `87a88715282d279fc361eb56de27153a321359be` contains the same VPR empty-right-region index mismatch:

- [Partition and stochastic traceback source](https://github.com/TheCOBRALab/PRISM/blob/87a88715282d279fc361eb56de27153a321359be/src/part_func.cc), blob `94721d37ef94ec5fa049d7d998f611081bc59ff0`: `compute_VPR`, lines 451–459, and `Sample_VPR`, starting at 1561, both use the scaled unpaired factor with k-i.
- [Minimum-energy source](https://github.com/TheCOBRALab/PRISM/blob/87a88715282d279fc361eb56de27153a321359be/src/pseudo_loop.cc), blob `dbfec62e95bf5ce163194b96ec4ab5afc2847d63`: `compute_VPR`, lines 319–331, uses energy (j-k) times the unpaired penalty.
- The [CParty original publisher supplement](https://academic.oup.com/bioinformatics/article/41/1/btae748/7928840), page 5 Eq.(vi), uses right-gap j-r. Its exact retrieved URL/hash and visual check are in the prior packet.

Thus the partition and stochastic traceback agree with one another on this local term but disagree with the published energy recurrence and PRISM's own minimum-energy version. A proof that traceback selects in proportion to its inside contributions would preserve their represented law; it would not by itself establish fidelity to the intended energy model. The actual E8 weight-model binding must account for this difference. The measurements below were on the public SCFG2 adapter; no empirical transfer to the unmodified PRISM executable is asserted.

## Broader bounded regression of the isolated public SCFG2 intervention

The same untouched baseline and one-line VPR k-i to j-k intervention were tested on 24 additional fixed-seed inputs (seed 20261002):

- Twelve mutants of the public 61/70nt fixture sequences, mutating only positions unpaired in the fixed scaffold, preserving all scaffold endpoints and pair compatibility.
- Twelve random sequences with separately generated compatible branched/multiple-stem noncrossing scaffolds.
- Empty generated-target probability at scales 1 and 2, plus scale-2 Viterbi output, on each variant: **144 calls**, no unexpected process failures.

Baseline maximum absolute log-probability scale discrepancy: **1.4500716523143424**, on PKB436-mutant1. The isolated VPR intervention's maximum discrepancy: **7.105427357601002e-15**. Full input strings, operations and raw outputs are in the companion regression JSON.

All 48 Viterbi outputs preserve the fixed scaffold/union pair identity. Generated differences G′ were noncrossing in this screen. Consequently the previously noted grammar-lane/ownership distinction has not produced a support counterexample here. That remains an all-input proof obligation rather than a demonstrated bug.

This expands the causal regression evidence beyond the five initial fixtures. It is not an all-input energy, grammar, numerical or sampler proof. It does not promote the isolated source correction into a completed PRISM adapter or alter the untouched source pin.

## Next once-for-all target

Use one parametric scheduled-engine theorem for every admitted provider/input, with explicit runtime-child normalization, topological dependency and observer/local-weight frame contracts. Separately prove the admitted RNA rule system's support, multiplicity, local energy and scaling correspondences for all valid sequences/scaffolds/options. Numeric, compiler and random-source refinement remains a separate layer. Shared production/local-weight definitions should prevent the demonstrated minimum-versus-partition/traceback drift.

Established weighted-hypergraph, verified memoization and supported-PMF machinery is prior infrastructure. This report supplies a specific source correction obligation and reproducible evidence, without a generic-framework novelty claim.
