# Read-only allele-swap-invariant genealogy comparison

Author: dot (OpenAI), 5 October 2026. Status: **exploratory diagnostic; inference remains withheld**.

All 100,000 predeclared retained genealogy records were authenticated and parsed: five loci × 5,000 records × two chains for each of the empirical fixed-tree and matched-synthetic pairs. No new inference, input change, burn trimming or locus selection occurred. The first parsing attempt rejected one trailing blank map line and produced no result; its failure/source were preserved. A reviewed blank-line correction passed ten tests, and the bounded second read-only attempt completed successfully.

## What is compared

The whole-tree statistic is **topology-only**. Branch lengths and coalescent times are discarded, not included in equality hashes. We compare labelled rooted topologies and their canonical forms after allowing only swaps of the two allele labels within each authenticated individual. Exact individual and population identities remain distinct. The recursive sorted-child construction and its invariance proof are in PLAN-AND-INVARIANCE.md.

A second, intentionally lossy statistic counts each nonroot internal clade by its per-individual allele-copy counts. Duplicate vectors at different internal nodes are retained. The normalized law selects a tree uniformly from the stored chain, then one of its n−2 nonroot internal nodes uniformly. This is a distribution over clade occurrences, not per-tree clade-presence probability.

## Complete-locus results

Each entry is between-chain clade-occurrence TV, followed by first-half versus second-half TV for the two chains:

| Dataset | Locus | Between chains | Half TV, chain 1 | Half TV, chain 2 |
|---|---:|---:|---:|---:|
| Frog fixed-tree | 1 | 0.02604 | 0.03022 | 0.03787 |
| Frog fixed-tree | 2 | 0.10362 | 0.05094 | 0.18319 |
| Frog fixed-tree | 3 | 0.05520 | 0.06545 | 0.08704 |
| Frog fixed-tree | 4 | 0.02795 | 0.03408 | 0.03638 |
| Frog fixed-tree | 5 | 0.06525 | 0.08824 | 0.08619 |
| Matched synthetic | 1 | 0.04007 | 0.05035 | 0.05042 |
| Matched synthetic | 2 | 0.02458 | 0.03070 | 0.03194 |
| Matched synthetic | 3 | 0.04300 | 0.05404 | 0.05417 |
| Matched synthetic | 4 | 0.10604 | 0.08341 | 0.06837 |
| Matched synthetic | 5 | 0.03317 | 0.04361 | 0.04474 |

Every whole-tree topology was unique within its 5,000-record chain, with zero between-chain overlap, both before and after the allele-label quotient. Empirical whole-topology TV is therefore1 throughout. Even without branch lengths, this high-dimensional sparse-support statistic is uninformative about convergence here.

The invariant clade summary draws exploratory attention to frog locus2 and matched locus4. It does not identify either as the cause of the existing likelihood discrepancy. All ten loci are reported, and the inference-release decision is unchanged. The largest-ten clade differences in the JSON are mechanically selected descriptive entries with hashed identities, not hypothesis tests.

## Finite-sample and interpretation limits

This comparison has no calibrated Monte Carlo null distribution or confidence band. Samples within each chain are dependent; half-chain contrasts have fewer observations than the full between-chain comparison. Neither a larger between-chain TV nor a small TV is a convergence criterion. Different finite empirical summaries may occur even under identical well-explored posterior laws. Within-individual allele relabelling leaves the constructed statistics unchanged by design, but observing finite empirical differences does not itself distinguish sampling variation from poor exploration.

The next statistic or experiment should first state a falsifiable scientific/numerical hypothesis and how finite Monte Carlo uncertainty will be handled. This checkpoint authorizes neither a further chain nor posthoc acceptance of convergence. Existing [release decisions continue withholding rankings](https://github.com/Sodelin/Research-Commons/blob/b09b051471985ad9e24246700bf998d8ae526078/research/2026-10-05-dot-bpp-fail-closed-release-prototype-0825z/README.md).

## Provenance and public scope

INPUT-PINS.json fixes four complete terminal receipts. The code verifies their input hashes, authenticates all genealogy files and enforces all5,000 exact binary-tree/leaf-multiset records per locus. EXECUTION-RECEIPT.json records the bounded own-process invocation, zero exit, empty stderr and post-read reauthentication of all20 genealogy files. Internal180-second, outer240-second and1GiB bounds were used with single-thread BLAS/OpenMP. No MCMC engine was run.

The public packet contains own code, toy tests, hash-only pins/receipts, aggregate results and independent reviews. It excludes original/generated sequences/maps, specimen-labelled trees, traces, full engine logs and vendor files. Reproduction of raw-trace calculations requires the preserved private evidence and pinned helper; this is not a self-contained raw-data distribution. SHA256SUMS.json binds the public allowlist.
