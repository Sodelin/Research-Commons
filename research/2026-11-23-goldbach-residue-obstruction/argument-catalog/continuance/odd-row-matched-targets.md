# Same-target check of the odd modulus-3 row

Finite diagnostic, not a pointwise bound. Compare [the aggregate hand proof](modulus-3-odd-aggregate.md) and the [isolated semiprime obstruction](../2026-11-23-cofactor-cells-1718z/modulus-3-odd-semiprimes.md).

Scan N=200,206,…,23996 (3,967 targets), with alpha=floor(sqrt(N)/2). Retain q=3 and odd h. For every h with 3h<N, check each m=3h+j (j=0,1,2) separately with 3 alpha<m<N. Set w=Lambda(N−m)μ(m)log(m/3). Add w/2 when j=0 and −w/2 otherwise to the full signed discrepancy. Use the same rule for the isolated semiprime discrepancy, restricting h to odd squarefree semiprimes. Integer factorization determines signs, multiplicities, and support; logarithms and sums are binary64. Rank by the isolated discrepancy divided by N (not by the full discrepancy).

| Target N | Isolated semiprime / N | All odd cells / N |
| --- | ---: | ---: |
| 20654 | -0.625409 | -0.081086 |
| 22640 | -0.624912 | -0.012006 |
| 22430 | -0.622648 | -0.009367 |
| 20756 | -0.621210 | -0.075673 |
| 22628 | -0.620415 | -0.065857 |
| 23612 | -0.619861 | -0.041083 |
| 19538 | -0.619107 | -0.064690 |
| 23750 | -0.617642 | 0.019541 |
| 20918 | -0.616928 | -0.064731 |
| 22406 | -0.616667 | -0.042704 |

In this fixed range, regrouping reduces the magnitude of every one of the ten largest normalized semiprime deficits, but nine still have a negative full odd row. At N=9602 the isolated discrepancy is -0.527349N and the full odd row is -0.003570N; the former agrees to six decimals with the pinned checkpoint. The lowest full odd row across the entire range is -0.098086N at N=9896. These are same-target comparisons, not claims about asymptotic frequency or the combined error over all cells and moduli. A negative value is not by itself a breach of the Goldbach positivity budget.
