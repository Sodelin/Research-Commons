# The remaining signed Goldbach rows on five powers of two

This finite replay compares the exact raw rows in the same-target budget at \(N=2^{20},2^{22},2^{24},2^{26},2^{28}\). It keeps the complete center bracket at each endpoint and the existing two disjoint allocations \(0.098N\) and \(0.045N\). The replay exposes a large early outer contribution from fixed small cofactors. The other rows together are small at these targets, with either sign. The four-or-more-prime center has empty support at these sizes. The joint asymptotic lower bound remains open. [Pinned raw decomposition and cutoff](https://github.com/Sodelin/Research-Commons/commit/36624845444790787f442157309e7f9ba6644ad0) · [Pinned full-bracket allocation](https://github.com/Sodelin/Research-Commons/commit/bc99f0b933d00448cb5fa16638a3c8dd6034f346)

## Exact finite support

Put \(H=\sqrt N\), \(L=\log N\), \(Q=N^{1/4}\), \(\alpha=H/L^{K_0}\), \(P=N^{21/40}\), and \(Z_1=\exp(L\sqrt{\log\log L}/\log L)\). On all five fixtures \(\alpha Q<1\) for every \(K_0\ge5\), starting at \(0.0640\) and ending at \(0.7616\) for \(K_0=5\). Thus \(h>\alpha\) in the raw actual rows and \(m>\alpha q\) in the centered low row keep every admissible positive integer cofactor while preserving their strict definitions. The raw center uses \((H/2,H]^2\), the endpoint test \(P^-(n)>Z_1\), and the strict \(d>P\). It has no extra count or mark masks. Write \(C_{\rm rest}\) for the even-endpoint center with at least four prime factors after taking out the already charged \(\mu(qh)=-1,\ P^-(n)\ge N^{19/120}\) slice. The signed residual compared here is
\[
 R(N)= E_{\rm lo}(N)+\sum_{(i,j)\in\mathcal O}A_{ij}(N)
                      +2S_{\rm even,sp}(N)+2C_{\rm rest}(N).
\]
The original sufficient inequality is \(R(2^k)\ge-(0.187-\eta)N\) for a fixed \(\eta>0\) at every sufficiently large \(k\). The term \(S_{\rm even,sp}\) refers to \(\mu(qh)=+1\). The raw \(A_{ij}\) already carry their original ordered weights. The two center terms displayed here keep the original external doubling. [Original same-target allowance](https://github.com/Sodelin/Research-Commons/commit/ccb8a60ee7c7a5a3c4b1c33ecf267b7ce8803ff9)

All table entries are divided by \(N\). The \(A_{ij}\) indices distinguish \((0,H/2]\), \((H/2,H]\), and \((H,\infty)\) for \(q,h\).

| \(k\) | \(A_{00}\) | \(A_{01}\) | \(A_{02}\) | \(A_{10}\) | \(A_{12}\) | \(A_{20}\) | \(A_{21}\) |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 20 | +.017494 | +.002242 | −.021661 | +.010129 | −.013111 | +1.305675 | −.008828 |
| 22 | +.009960 | −.012282 | +.007803 | +.010808 | +.007125 | +1.322423 | −.008396 |
| 24 | −.002861 | +.011497 | −.009293 | +.001137 | −.007592 | +1.305650 | +.006727 |
| 26 | +.005969 | −.008274 | +.004733 | +.004018 | +.005021 | +1.331721 | −.009425 |
| 28 | −.003126 | +.007681 | −.002631 | −.002224 | −.005113 | +1.315123 | +.005288 |

| \(k\) | \(E_{\rm lo}\) | \(2S_{\rm even,sp}\) | \(2C_{\rm rest}\) | Joint \(R\) | \(R-A_{20}\) | \(R-A_{20}(h<64)\) |
|---:|---:|---:|---:|---:|---:|---:|
| 20 | +.019990 | +.002106 | 0 | +1.314036 | +.008361 | +.042479 |
| 22 | −.010781 | +.002052 | 0 | +1.328711 | +.006288 | +.044090 |
| 24 | +.007856 | −.002013 | 0 | +1.311106 | +.005457 | +.026133 |
| 26 | −.001116 | +.002137 | 0 | +1.334783 | +.003063 | +.046856 |
| 28 | −.001958 | −.001509 | 0 | +1.311530 | −.003593 | +.022968 |

The last two columns are subtractions for diagnosis. The joint budget uses \(R\). On these fixtures the separate \(M_0/N\) varies between \(1.316126\) and \(1.320737\). For all five fixtures there is a finite difference between the raw prime row \(A_{11}\) and twice the \(Z_1\)-rough even-endpoint row. It ranges from \(-0.013795N\) to \(+0.013108N\). This is a finite replay of the rows matched by the asymptotic ledger. The \(o(N)\) in that ledger has no numerical enclosure at these sizes. The first three low and outer sums agree to displayed precision with the earlier separate replay. [Earlier replay and cutoff comparison](https://github.com/Sodelin/Research-Commons/commit/313855c25acb1194a991dca7732ea971be1673ab) · [Full joined data](goldbach-signed-replay-joined.csv)

There is a further exact explanation for why these small targets cannot evaluate the asymptotic margin. At \(\alpha<1\), the actual low row and all raw \(A_{ij}\) together include every divisor of each odd squarefree \(m=N-n\). The weight at fixed \(m\), before multiplying by \(\Lambda(N-m)\), is then \(-\sum_{h\mid m}\mu(h)\log h=\Lambda(m)\). The one possible even endpoint \(n=2\) has exact correction \(-\log 2\,\Lambda((N-2)/2)\) when \((N-2)/2\) is squarefree, and contributes zero otherwise. Thus the raw actual sum already recovers the odd squarefree piece of the weighted prime-pair count in this regime. Adding the asymptotic model as if the short cofactor comparison were exact would give an artificial additional main term.

The zero in the higher center column is structural. Every central \(n<3N/4\), so four primes greater than \(Z_1\) require \(4\log Z_1<\log(3N/4)\). For \(k\ge20\), the normalized left side \(4\sqrt{\log\log L}/\log L\) decreases and the normalized right side \(1+\log(3/4)/L\) increases. The logarithmic difference \(\log(3N/4)-4\log Z_1\) is in \((-0.058847,-0.058846)\) at \(k=241\) and \((0.036070,0.036071)\) at \(k=242\), by outward interval evaluation. Thus the first possible exponent from this necessary test is \(242\). Passing the test allows enough product room and does not establish an actual placement. The optional older \(Y_0\)-rough replay has higher endpoints at the five fixtures, on its separate support. [Raw and masked center data](goldbach-center-evaluator-results.jsonl)

## The next signed outer estimate

The terms of \(A_{20}\) with \(h<64\) account for \(1.271557N\) to \(1.288562N\) in these fixtures. The first lane \(h=3\) alone contributes between \(0.327628N\) and \(0.328608N\), approaching its fixed-cofactor coefficient. Every fixed \(h\) eventually leaves the strict moving cutoff. The signed fixed-cofactor model coefficients sum to the singular series, which explains the magnitude of this early positive row. [Fixed-cofactor hand calculation](https://github.com/Sodelin/Research-Commons/commit/97f9728b3529d5beda56c539bd248e759cfa9283)

There is an exact way to diagnose the two transposed outer cells without crediting that finite contribution. For odd squarefree \(m=qh\), exchange \(q,h\) in \(A_{20}\). Both cells now use \(q\le H/2<h\), \(h>H\), \(qh<N\), odd coprime squarefree factors, and \(\Lambda(N-qh)\). In \(A_{02}\), the smaller variable satisfies \(q\ge Q\). In transposed \(A_{20}\), it satisfies \(q>\alpha\). The overlap has exact paired coefficient
\[
 -\mu(h)\bigl(\log h+\mu(qh)\log q\bigr)\Lambda(N-qh).
\]
Only \(n=2\) can contribute an even endpoint with squarefree \(m\), so the odd restriction in this comparison costs at most \(N^{o(1)}\). At the replay sizes the smaller-variable band \(\alpha<q<Q\) is present only in transposed \(A_{20}\). Eventually \(\alpha>Q\) and the asymmetric band instead is \(Q\le q\le\alpha\), present only in \(A_{02}\). This explains why the finite positive row gives no credit for the extra adverse terms that can appear when the cutoff moves.

An independent overlap replay gives the following split, again divided by \(N\). The unmatched contribution changes sides when the cutoffs cross.

| \(k\) | Unmatched \(A_{20}\), \(h<Q\) | Paired \(A_{02}+A_{20}(h\ge Q)\) | Joint residual after the unmatched term |
|---:|---:|---:|---:|
| 20 | +1.304378 | −.020364 | +.009658 |
| 22 | +1.257624 | +.072601 | +.071086 |
| 24 | +1.284973 | +.011383 | +.026133 |
| 26 | +1.305698 | +.030756 | +.029085 |
| 28 | +1.320323 | −.007831 | −.008793 |

At \(2^{28}\) the paired block has totals \(-5.527423N\) when \(\mu(q)=\mu(h)=+1\), \(+5.518576N\) when \(\mu(q)=\mu(h)=-1\), and \(+0.001016N\) on opposite signs. The transpose grouping therefore exposes a large cancellation of two genuine same-target signed contributions. [Replayed overlap and parities](goldbach-raw-paired-cells-replay.csv)

The next target is the fixed-\(N\) signed \(A_{02}\) contribution with \(Q\le q\le\alpha\), jointly with the remaining paired overlap where feasible. This selection follows the exact change of support and the measured cancellation in \(A_{02}\), whose absolute contribution grew from \(6.40N\) to \(14.04N\) while its signed contribution changed sign. On the overlap the odd Möbius parity has a log ratio, while the even parity has \(\log(qh)\). The short-\(h\) part of raw \(A_{20}\) is already charged by the pinned pointwise proof. The new signed estimate must use the long-cofactor weights of \(A_{02}\) or an exact identity pairing them. A progression count for the individual primes leaves the \(\mu(h)\) weight along the fixed equation uncontrolled. [Existing short-cofactor result](https://github.com/Sodelin/Research-Commons/blob/36624845444790787f442157309e7f9ba6644ad0/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-powers-two-margin-and-odd-semiprime-budget.md#a-short-cofactor-part-of-the-raw-outer-rows)

The centered formulation has the same pointwise value up to \(o(N)\), and reduces the lower bound on the unmatched row to a one-sided estimate for \(T_{02}(N)\). [Exact centered target](../goldbach-unmatched-outer-centered.md)

## Reproduction and status

```sh
g++ -O3 -std=c++20 goldbach-raw-cell-replay.cpp -o goldbach-raw-cell-replay
./goldbach-raw-cell-replay 20 22 24 26 28 > goldbach-raw-cell-replay.csv
g++ -O3 -std=c++20 goldbach-low-raw-replay.cpp -o goldbach-low-raw-replay
./goldbach-low-raw-replay 28 > goldbach-low-raw-replay.tsv
g++ -O3 -std=c++20 goldbach-center-evaluator.cpp -o goldbach-center-evaluator.bin
python3 goldbach-center-evaluator-run.py 20 22 24 26 28 > goldbach-center-evaluator-results.jsonl
python3 goldbach-signed-replay-join.py > goldbach-signed-replay-joined.csv
python3 goldbach-raw-cell-crosscheck.py
python3 goldbach-center-evaluator-check.py
g++ -O3 -std=c++20 goldbach-raw-paired-cells-replay.cpp -o goldbach-raw-paired-cells-replay
./goldbach-raw-paired-cells-replay 20 22 24 26 28 > goldbach-raw-paired-cells-replay.csv
```

The largest low replay uses about 2.5 GiB for the sieve and von Mangoldt array. Integer support and factor classifications are checked directly. Real center cutoffs are rounded independently at 100 and 160 decimal digits, and log weights are evaluated numerically. The raw rows cross-check by explicit \(q,h\) loops at \(2^{20},2^{22}\), and the center cross-check enumerates the original admitted divisors at \(2^{20}\). The low row and raw central prime row also agree between the independent evaluators on all five fixtures. These are numerical checks. The fixed-cofactor result and transpose identity are hand arguments. No new Lean verification is claimed.
