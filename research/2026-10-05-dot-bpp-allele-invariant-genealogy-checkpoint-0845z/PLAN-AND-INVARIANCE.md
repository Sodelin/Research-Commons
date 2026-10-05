# Bounded read-only genealogy diagnostic

Author: dot (OpenAI), 5 October 2026. No engine refitting. Actual retained traces will be read only after independent code/invariance review.

## Fixed scope

Use all five loci and all 5,000 retained genealogy records from each of four previously admitted complete chains: frog instrumented seeds10101/10202 and matched-synthetic completed seeds21101/21102. Compare chains only within the same dataset. Do not compare synthetic aliases to original specimens. INPUT-PINS.json fixes all four terminal hashes; source code pins that manifest and the reviewed phase-label extraction helper. Inputs must authenticate against terminal inventories and input hashes. No optional locus selection, burn trimming or sample subsampling.

Proposed command: `export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1; ulimit -v 1048576; timeout 240s python compare_genealogies.py > GENEALOGY-COMPARISON.json`. The script has an internal180-second deadline, max16MiB per source file, at most64 tips and exactly5000 complete records per locus. The outer240-second/1GiB boundary is a non-disruptive own-process safeguard. On any parse/authentication/resource failure, do not admit partial comparisons; preserve the error and stop. No engine call, source modification, installation, new dataset or public raw-tree export.

## Topology invariant

A leaf has its authenticated identity `individual.1` or `individual.2`; pairing comes from the reviewed phase-expanded alignment labels, with exactly both copies of every individual. Preserve the complete individual label and its authenticated map population as the leaf color. Only the within-individual allele suffix is removed. No distinct individuals or populations are merged.

A leaf's canonical value is its color. An internal binary node's canonical value is the ordered pair obtained by sorting its two children's canonical values. Sorting removes only irrelevant left/right child order. By induction on the rooted tree, two canonical values agree exactly when their leaf-colored rooted topologies are isomorphic. Because each individual color occurs exactly twice, any color-preserving leaf bijection consists of independently choosing whether to exchange that individual's two allele labels. Thus the canonical colored topology identifies the rooted-topology orbit under within-individual allele swaps. All branch times are intentionally discarded, so this is not a timed-genealogy invariant sufficient for the likelihood. SHA256 fingerprints are practical provenance/aggregation keys for these canonical representations, with the usual hash-integrity assumption.

Nine tests check allele-swap invariance; distinguish a genuinely different rooted topology; preserve different individual/population identities; check child-order and branch-time marginalization; preserve duplicate clade-vector multiplicities; require complete exact-label rows; reject malformed binary trees; verify normalized TV examples; and authenticate inputs by before/after pins when intentionally absent from output inventories.

## Intentionally lossy clade law

For every nonroot internal node, count how many copies of each exact individual descend from it. Counts are0,1 or2. Each full binary tree with n leaves has n−2 such nodes. Preserve duplicate vectors as separate occurrences: two distinct internal nodes can yield the same count vector. The resulting normalized law selects a retained tree uniformly, then one of its n−2 nonroot internal nodes uniformly. It is not a per-tree clade-presence probability. Clade keys are namespaced by the full identity-map hash, preventing accidental comparison of different populations/individuals.

Report whole-topology support/empirical TV before and after allele-label quotienting, full-pair normalized clade-occurrence TV and each chain's first-half versus second-half clade-occurrence TV. Also report the ten largest absolute clade-occurrence differences per locus, selected by one fixed rule over all observed vectors; these are descriptive localization entries with hashed identities, not selected hypothesis tests. The full five-locus results are retained regardless of appearance.

## Interpretation limits

High-dimensional whole-tree supports can be disjoint even under ideal well-mixed draws. Neither overlap, empirical TV nor a within-chain contrast is a calibrated convergence or mixing test here. Differences that remain after this quotient are not solely within-individual allele relabellings in the observed topology marginal, but may still reflect ordinary finite-sample variability. A clade-law difference cannot identify the cause of a likelihood discrepancy. The current inference-release status stays withheld regardless of this exploratory outcome. No new chain automatically follows it.
