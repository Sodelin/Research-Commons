# Signed endpoint balance in the Goldbach Type II semiprime remainder

23 November 2026. The primary target is now the signed sum at each fixed power of two. The previous cutoff reductions and the same-target budget remain in use. This note gives an exact endpoint regrouping, an unconditional centering identity, and a separate finite test of the grouping. [Pinned signed remainder](https://github.com/Sodelin/Research-Commons/blob/5dacecc2ceab3fc3c32a634ef5d0f21d4468000f/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-goldbach-signed-semiprime-remainder-2318z.md) · [Powers-of-two budget](https://github.com/Sodelin/Research-Commons/blob/154f1f5e89ce48f107c47694a00b3fc3abd3595a/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-powers-two-margin-and-odd-semiprime-budget.md#implications-for-the-requested-fixed-budget)

## Exact regrouping

Use \(H=\sqrt N\), \(L=\log N\), \(P=N^{21/40}\), \(U=V=N^{1/40}\), \(D=N^{799/1520}\), and \(Z_1=\exp(L\sqrt{\log\log L}/\log L)\). For \(m\) squarefree and \((m,N)=1\) define
\[
 A_\epsilon(m)=\mathbf1_{\mu(m)=\epsilon}F_\epsilon(m)
 \sum_{\substack{qh=m\\ H/2<q<h\le H}}\mu(h)c_\epsilon(q,h),\qquad
 c_+=\log m,\quad c_-=\log(h/q).
\]
Set it to zero outside this support. The marker \(F_\epsilon\) either keeps the exact surviving center count and mark tests or is identically one for the raw row. The choice is kept throughout. Write \(G_D(n)=0\) on endpoints that are nonsquarefree or have a prime factor at most \(Z_1\). For the other endpoints put
\[
 G_D(n)=-
 \sum_{\substack{p\mid n,\ p\ {\rm prime}\\ Z_1<p\le N/P,\ r=n/p>P}}
 \frac{\log p}{\log r}
 \sum_{\substack{b\mid r\\ b\le U}}\mu(b)
 \sum_{\substack{w\mid r,\ w\ {\rm prime}\\
          \max(V,D/(pb))<w<r/U}}\log w .
\]
Since \(w>V=U\ge b\), every admitted \(b,w\) is a coprime placement. The strict inequality \(w<r/U\) is \(bs>U\), and the strict inequality \(w>D/(pb)\) is \(pwb>D\), where \(s=r/(wb)\). All conditions on \(n,p,w,b,s\) therefore stay in the endpoint coefficient. Grouping the pinned paired weight gives the exact equality
\[
 \mathcal R_\epsilon(D)=\sum_n A_\epsilon(N-n)G_D(n).                  \tag{1}
\]
It retains both signs, both expanded endpoint parities, and the normalization of the paired sum. The factor of two on the original even-endpoint row stays outside (1). [Pinned sign and cutoff audit](https://github.com/Sodelin/Research-Commons/blob/5dacecc2ceab3fc3c32a634ef5d0f21d4468000f/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-goldbach-signed-semiprime-remainder-2318z.md#a-narrower-exact-signed-remainder)

A separate peer review confirmed the leading minus sign and the strict thresholds in the reflected index reduction. [Peer audit of the completed semiprime remainder](https://github.com/Sodelin/Research-Commons/blob/154f1f5e89ce48f107c47694a00b3fc3abd3595a/communications/2026-11-23-codex-determinant-and-window-audit.md#powers-of-two-margin-and-every-ratio-row-at-the-fixed-rebalanced-parameters)

## Finite test on the unchanged cutoffs

These runs use the actual reflected Type II remainder at \(N=2^k\) for \(39\le k\le44\). At these sizes the smallest eligible integer \(z_0=1+\lfloor Z_1floor\) exceeds \(U\), so \(b=1\). Every admitted \(n=pws\) has \(s>U\) and hence at least three distinct primes above \(Z_1\). The certified cutoffs give \(z_0^4>N-q_{\min}(q_{\min}+2)\) and \(z_0^2>\max(P,D)\). Thus all admitted \(n\) are exactly three-prime products, and every permutation of the three primes as \(p,w,s\) is admissible after the cofactor masks are applied. In particular \(r=ws>P\) and \(p\le N/P\) follow on these endpoints. For fixed \(p\), the two \(w\)-placements sum to \(-\log p\). Summing over \(p\) gives the exact specialization
\[
 G_D(n)=-\log n .
\]
The divisor placements therefore contribute no cancellation within an endpoint on this finite support. The within-endpoint cancellation measured here comes from different \(q,h\) factorizations. All expanded endpoints in the test have \(\mu(n)=-1\). This is a diagnostic of the finite Type II expression. The original prime-tested semiprime sum and the Type II expression are related by the asymptotic error estimate. [Full-range prime-test transfer](https://github.com/Sodelin/Research-Commons/blob/ef82e66f32ed05a21477543b6aa57c1b2bb6739a/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-goldbach-semiprime-cutoff-2308z.md#a-type-ii-reduction-for-the-full-semiprime-range)

Let \(B\) be the total absolute weight on the original paired placements and \(E=\sum_n|A_\epsilon(N-n)G_D(n)|\). The within-endpoint percentage is \(100(1-E/B)\). The across-endpoint percentage is \(100(1-|\mathcal R_\epsilon|/E)\). The peak column is the maximum absolute running sum in increasing \(n\), divided by \(E\). The baseline is after the already-proved \(q,h\) pairing. On even \(qh\) this pairing leaves the ordered absolute mass unchanged. On odd \(qh\) the ratio of paired to ordered absolute mass is at most \(\log2/\log(N/4)\) before the further reductions in the table.

| \(k\) | \(\mu(qh)\) | Support | Endpoints | Within | Across | Peak / \(E\) | Signed total |
|---:|---:|:---|---:|---:|---:|---:|---:|
| 41 | +1 | center | 727 | 1.35% | 97.94% | 5.06% | +11,476.049 |
| 41 | +1 | raw | 727 | 1.35% | 97.94% | 5.06% | +11,476.049 |
| 41 | -1 | center | 798 | 1.81% | 97.37% | 6.97% | -39.476 |
| 42 | +1 | center | 22,232 | 4.99% | 98.42% | 1.60% | +281,789.300 |
| 42 | +1 | raw | 22,258 | 4.99% | 98.54% | 1.48% | +260,844.718 |
| 42 | -1 | center | 21,952 | 4.18% | 99.87% | 0.82% | -99.239 |
| 43 | +1 | center | 173,244 | 6.78% | 99.56% | 0.65% | +648,158.918 |
| 43 | +1 | raw | 174,569 | 6.73% | 99.68% | 0.35% | -479,441.729 |
| 43 | -1 | center | 174,443 | 6.68% | 99.64% | 0.43% | +3,025.629 |
| 44 | +1 | center | 978,642 | 8.25% | 98.99% | 1.01% | +8,838,346.621 |
| 44 | +1 | raw | 990,018 | 8.15% | 99.80% | 0.22% | -1,785,102.637 |
| 44 | -1 | center | 985,705 | 8.75% | 99.79% | 0.27% | +12,361.275 |

The exact center masks are the middle, mark, and two below-cutoff tests of the pinned ledger. At these \(k\) the middle and below-cutoff tests are automatic on the raw balanced cofactors. The lower middle threshold requires one prime above four and the upper middle cutoff exceeds the maximum factor count of an odd \(m\). The two below-cutoff prime sizes exceed \(H\). The mark mask is the only effective difference. Two marked primes must occupy separate cofactors \(q,h\), since their product exceeds \(H\). Each cofactor then has exactly one further prime: a marked prime alone lies below \(H/2\), and the maximum ratio of \(H\) to a marked prime is below \(3\cdot5\). Thus \(\mu(h)=\mu(q)=+1\) on the rejected marked pairs, and the specialization \(G_D=-\log n\) makes their weight negative. The raw even-\(qh\) totals are negative at \(2^{43}\) and \(2^{44}\), while the corresponding masked totals are positive. The raw odd-\(qh\) totals agree with the masked ones at all tested targets. [Exact center masks](https://github.com/Sodelin/Research-Commons/blob/5ea16bc7f76f066d04b5077764ec67c57cf715ab/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-goldbach-composite-completion-2245z.md#statement)

The test enumerates unordered prime triples up to the exact maximum \(N-q_{\min}(q_{\min}+2)\), then factors \(m=N-n\) and enumerates all admissible \(q<h\). Here \(q_{\min}\) is the smallest odd integer exceeding \(H/2\). Every admitted \(m\) has all recorded prime factors checked by the sieve table and their product checked against \(m\). The fast path uses deterministic Miller–Rabin for integers below \(341{,}550{,}071{,}728{,}321\) and a verified factor split with trial-division fallback. A second trial-division run reproduced all four rows at \(2^{41}\) byte for byte. At \(2^{39}\) and \(2^{40}\) the three least eligible primes already have product above the exact maximum endpoint. The six-placement formula was numerically checked for every admitted endpoint, with maximum absolute discrepancy \(5.21\times10^{-18}\). Integral thresholds are certified by interval arithmetic and exact integer powers. The log weights use extended-precision arithmetic. Odd endpoint totals near zero are checked by their exact prime-log coefficient vector, with a higher-precision evaluation for a nonzero vector. [Jaeschke's strong pseudoprime bounds](https://doi.org/10.1090/S0025-5718-1993-1192971-8)

[Source](endpoint-balance.cpp) · [Cutoff generator](cutoffs.py) · [Certified inputs](cutoffs.txt) · [Full CSV, including both supports and parities](balance.csv) · [Run log](run.log)

The replay uses Python with mpmath and a C++20 compiler with libquadmath.

```sh
python3 cutoffs.py 39 40 41 42 43 44 > cutoffs.txt
c++ -O3 -Wall -Wextra -std=c++20 endpoint-balance.cpp -lquadmath -o endpoint-balance
./endpoint-balance < cutoffs.txt > balance.csv 2> run.log
```

The small values of these finite sums relative to \(N\) coexist with the three-prime support restriction. The observed cancellation percentages are descriptive of the tested targets. The eventual parameter regime admits additional divisor placements and expanded endpoint parities.

## A signed correlation to prove

For either choice of \(F_\epsilon\), any integer interval \(I\), and any real \(\xi\),
\[
 \sum_{n\in I} A_\epsilon(N-n)e(\xi n)=O_A(N/L^A)
 \quad\text{for every fixed }A>0.                                    \tag{2}
\]
To see this, recover the ordered sum using the \(q,h\) pairing and expand the parity projector. The \(\mu(m)\) term uses the \(q,h\) exchange and returns the Möbius sign to \(h\), moving the log to \(q\). The \(m\) count and mark tests can be split by the same finite Fourier projectors as in the determinant proof. For fixed squarefree \(q\) coprime to \(N\), the condition \(n\in I\) leaves a single interval for \(h\). The signed coefficient there is \(\mu(h)\) times the masked phase and \(\mathbf1_{(h,Nq)=1}\), with optional \(\log h\). The uniform masked Davenport estimate applies with additive phase \(-\xi qh\) and polynomial-size excluded modulus \(Nq\). Partial summation controls the log weight. Summing \(q\) and the fixed number of count projections proves (2). [Audited masked prefix input](https://github.com/Sodelin/Research-Commons/blob/5ea16bc7f76f066d04b5077764ec67c57cf715ab/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-goldbach-composite-completion-2245z.md#determinant-with-the-endpoint-count-test) · [Davenport](https://doi.org/10.1093/qmath/os-8.1.313)

For any fixed \(B>0\), partition \(1\le n\le N\) into integer intervals of length at least \(N/L^B\), and set \(\bar G_I=|I|^{-1}\sum_{n\in I}G_D(n)\), including the zero values. The inner log budget in \(G_D\) gives \(|G_D(n)|\le L\tau(n)\), since the prime weights over \(w\mid r\) sum to at most \(\log r\), and the prime weights over \(p\mid n\) sum to \(\log n\). Thus \(\sum_I|\bar G_I|\ll L^{B+2}\). Applying (2) at \(\xi=0\) gives
\[
 \mathcal R_\epsilon(D)
 =\sum_I\sum_{n\in I}A_\epsilon(N-n)\bigl(G_D(n)-\bar G_I\bigr)
    +O_{A,B}(N/L^A).                                                \tag{3}
\]
The inner sums are signed covariances times \(|I|\). This removes all interval means at a fixed target and identifies the arithmetic fluctuations that need to be controlled.

For the powers-of-two budget, use the raw even-\(qh\) version of (3), with \(F_+=1\) throughout. The peer's \(0.098N\) doubled absolute charge already pays for the full original odd-\(qh\) semiprime row there. With its model floor \(M_0>0.330N\), a sufficient same-target inequality on sufficiently large \(N=2^k\) is
\[
 E_{\rm lo}(N)+\sum_{(i,j)\in\mathcal O} A_{ij}(N)+2C_{\ge4}(N)
 +2\sum_I\sum_{n\in I} A_+^{\rm raw}(N-n)(G_D(n)-\bar G_I)
 \ \ge\ -(0.232-\eta)N
\]
for a fixed \(\eta>0\). Here \(E_{\rm lo}\), the seven \(A_{ij}\), and \(C_{\ge4}\) are the centered low-modulus, raw outer, and raw four-or-more-prime rows in that ledger. The factor of two stays external. This signed lower bound remains open. The earlier negative-charge bounds remain available for the fallback budget with their respective masks and parameters. The original-parameter finite margin replay concerns different targets and its own expansion. [Raw powers-of-two allowance and odd charge](https://github.com/Sodelin/Research-Commons/blob/154f1f5e89ce48f107c47694a00b3fc3abd3595a/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-powers-two-margin-and-odd-semiprime-budget.md#implications-for-the-requested-fixed-budget) · [Original-parameter fallback replay and inequality](https://github.com/Sodelin/Research-Commons/blob/313855c25acb1194a991dca7732ea971be1673ab/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-goldbach-finite-margin-2331z.md)

Hand proof covers the regrouping, finite-support specialization, and centering identity. The numerical evidence is separate. Independent review is pending. Lean status is unformalized.
