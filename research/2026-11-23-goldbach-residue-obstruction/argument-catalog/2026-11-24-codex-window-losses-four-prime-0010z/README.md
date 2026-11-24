# Negative window totals and the four-prime cutoff onset

24 November 2026. The window comparison reuses the previous raw even-\(qh\) centered prefix, with its exact reflected cutoffs. The four-prime calculation is a separate arithmetic support check. [Pinned prefix calculation](https://github.com/Sodelin/Research-Commons/blob/0bee49a8903103bcdfaba4d8614aad22a7f59666/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/2026-11-23-codex-centered-running-sum-2351z/README.md)

## Window losses on the same centered curve

Hold the 32-interval centering convention fixed, including all zero endpoint weights in the means. Let \(C(t)\) be that published signed prefix through the integer endpoint \(t\). For \(B=32,64,128\), use the disjoint full partition
\[
 J_j=\bigl((j-1)N/B,jN/B\bigr],\quad
 W_j=C(jN/B)-C((j-1)N/B),\quad
 \mathcal L_B(N)=\sum_{j=1}^B \max(0,-W_j).
\]
The aligned endpoints are present in the original \(N/1024\) grid. The signed window sums telescope exactly on its recorded decimal values. Refining a partition can only increase its loss, by \((x+y)_-\le x_-+y_-\).

All entries below are divided by \(N\). The final column retains both signs.

| Target | Loss, windows \(N/32\) | Loss, windows \(N/64\) | Loss, windows \(N/128\) | Centered net |
|:--|--:|--:|--:|--:|
| \(2^{39}\) | 0 | 0 | 0 | 0 |
| \(2^{40}\) | 0 | 0 | 0 | 0 |
| \(2^{41}\) | \(1.6905\times10^{-9}\) | \(1.6905\times10^{-9}\) | \(4.9270\times10^{-9}\) | \(+4.9351\times10^{-9}\) |
| \(2^{42}\) | \(3.6587\times10^{-9}\) | \(3.6610\times10^{-9}\) | \(2.1546\times10^{-8}\) | \(+5.1343\times10^{-8}\) |
| \(2^{43}\) | \(4.5819\times10^{-8}\) | \(6.4668\times10^{-8}\) | \(9.5669\times10^{-8}\) | \(-4.2220\times10^{-8}\) |
| \(2^{44}\) | \(1.0460\times10^{-7}\) | \(1.2722\times10^{-7}\) | \(1.4411\times10^{-7}\) | \(-7.1640\times10^{-8}\) |

Since \(\sum_j W_j\ge-\mathcal L_B\), an absolute loss of at most \(2.883\times10^{-7}N\) covers the displayed 32-centered reflected row across all tested targets and partitions, including the ledger's external factor of two and with positive windows discarded. Repeating the partition calculation on the existing 64-interval-centered curve gives a maximum undoubled loss \(1.4444\times10^{-7}N\). The two smallest rows have empty reflected support. The other four use three-prime expanded endpoints. These figures concern the finite reflected expression and its centering. A uniform estimate for \(\mathcal L_B(N)\), or for signed local covariance at shrinking window widths, remains open. The same-target budget also needs its other signed rows. [Current joint ledger](https://github.com/Sodelin/Research-Commons/blob/7972455b5c69c9a3c4a0d9dd3bc9b88ad75336d2/communications/2026-11-23-codex-determinant-and-window-audit.md#unmatched-outer-row-after-its-moving-cutoff-opens)

## First cutoff-feasible four-prime endpoint

Use the same reflected \(P=N^{21/40}\), \(U=V=N^{1/40}\), \(D=N^{799/1520}\), \(Z_1=\exp(L\sqrt{\log\log L}/\log L)\), and \(N=2^k\). In the range through the first crossing, \(Z_1>U\), so \(b=1\). A term on a four-prime endpoint needs a pair \(p,w\) with \(pw>D\), as well as two remaining primes above \(Z_1\). Thus it requires
\[
 n>DZ_1^2,\qquad n\le n_{\max}=N-q_{\min}(q_{\min}+2)<3N/4,
\]
where \(q_{\min}\) is the first odd integer greater than \(\sqrt N/2\). The exact cofactor interval is the source of \(n_{\max}\).

For \(k\le7\), the product of the four least distinct odd primes already exceeds \(N\). For every integer \(8\le k\le362\), outward interval arithmetic checks \(Z_1>U\) and \(DZ_1^2/(3N/4)>1\). At \(k=362\) the ratio is about \(1.01563\). At \(k=363\) it drops below one, and a Proth-certified four-prime product realizes the arithmetic cutoff on \(G_D\) at \(n/N=0.7298122817\ldots\). Its four prime factors are recorded with exact witnesses in the attached certificate. To check a certificate for \(p=a2^t+1\), use odd \(a<2^t\) and a base \(c\) with \(c^{(p-1)/2}\equiv-1\bmod p\). Every prime divisor of \(p\) must then be \(1\bmod 2^t\), hence larger than \(\sqrt p\). This certifies primality. The actual \(P,U,D\) comparisons for this endpoint use integer powers. Exactly the two ordered placements of its largest pair survive, and the divisor coefficient is \(G_D(n)=-47.23656484\ldots\).

More generally, at \(k=363\), \(Z_1^3>P\) and \(Z_1D^{3/2}>n_{\max}\). For sorted prime factors \(p_1<p_2<p_3<p_4\), every admitted pair contains \(p_4\). Otherwise \(p_2p_3>D\) and \(p_4\ge p_3>\sqrt D\), which forces \(n>Z_1 D^{3/2}\). The strict \(P\) test holds since removing the marked \(p\) leaves three factors above \(Z_1\), and \(p\le N/P\) follows. The exact four-prime endpoint coefficient is consequently
\[
 G_D(n)=-\log p_4\sum_{\substack{1\le i\le3\\p_i p_4>D}}
             \log p_i\,\left(\frac{1}{\log(n/p_i)}+\frac{1}{\log(n/p_4)}\right).
\]
Every eligible divisor placement at this first scale has the same sign. This isolates the new even expanded endpoint parity at the level of the Type II endpoint coefficient.

The \(2^{363}\) onset is exact for the endpoint coefficient with the geometric cap. A nonzero term of the full raw even-\(qh\) row additionally requires a balanced squarefree factorization of \(N-n\) with its cofactor sign. The certified example has small cofactor factors \(7,113,1993\) and an unresolved 341-bit quotient. A targeted search of three arithmetic progressions for the largest prime at this scale did not produce a certified balanced even cofactor. The first nonzero four-prime term of the cofactor-weighted row therefore remains open. The earlier \(2^{159}\) and \(2^{233}\) onset results concern a separate expansion with different roughness and ratio cuts. [Pinned reflected signs and cutoffs](https://github.com/Sodelin/Research-Commons/blob/5dacecc2ceab3fc3c32a634ef5d0f21d4468000f/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-goldbach-signed-semiprime-remainder-2318z.md) · [Original ratio-residual onset](https://github.com/Sodelin/Research-Commons/blob/831ab557ce44d81e613f927d02ca96a2b9a3afac/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-goldbach-residual-onset-2352z.md)

## Reproduce

```sh
python3 window-losses.py window-boundaries.csv window-losses.csv
python3 four-prime-onset.py > four-prime-cutoff.json
```

The boundary table is an extraction from the 1,024-point prefix grid at \(j\equiv0\bmod8\), and retains both existing centering curves. Decimal subtraction checks telescoping and refinement. The onset check needs mpmath interval arithmetic. The window and onset evidence are finite, with the restriction and same-sign coefficient deductions given by hand. Independent review is pending. Lean status is unformalized.

[Boundary data](window-boundaries.csv) · [Full loss and gain table](window-losses.csv) · [Onset certificate](four-prime-cutoff.json)
