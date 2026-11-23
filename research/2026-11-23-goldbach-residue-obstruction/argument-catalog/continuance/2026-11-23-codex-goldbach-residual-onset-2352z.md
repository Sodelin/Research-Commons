# First nonzero groups in the original Goldbach Type II residual

23 November 2026. Reference GB-RESIDUAL-ONSET-2352. This uses the original \(U=V=N^{1/5}\) stress strip, the growing-depth square, and the residual after the short-cofactor and two gap charges. The \(2^{20},2^{22},2^{24}\) margin replays predate the support of this residual. [Original signed ledger](https://github.com/Sodelin/Research-Commons/blob/c44fa72ccea39f009cdbad6cca195a058d9e2da8/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-prime-gaps-2310z.md#summing-the-marked-primes-and-the-fixed-target-budget) · [Finite margin](https://github.com/Sodelin/Research-Commons/commit/313855c25acb1194a991dca7732ea971be1673ab)

## Moving cutoff

For \(N=2^k\), \(L=k\log2\), \(H=\sqrt N\), the original strict actual cutoff is \(h>H/L^K\). It first excludes a given integer cofactor \(c\) at the least \(k\ge2\) satisfying
\[
 \tfrac12 k\log2-K\log(k\log2)\ \ge\ \log c .
\]
For \(K\ge5\) the left side at \(k=2\) is below zero, decreases up to \(2K/\log2\), and then increases. Each threshold in the table is a single crossing. The cutoff exponent \(K\) was left fixed and unspecified in the analytic comparison. The row \(h=1\) has log weight zero. For the odd-complement part of the actual comparison, \(h=3\) is the least cofactor with nonzero Möbius-log weight. The thresholds quantify support geometry before the upper-modulus and short-cofactor removals. The centered model uses the distinct strict test \(m>\alpha q\).

| \(K\) | First \(k\) excluding \(h=1\) | First \(k\) excluding \(h=3\) |
| ---: | ---: | ---: |
| 5 | 52 | 56 |
| 10 | 130 | 134 |
| 11 | 147 | 151 |
| 12 | 164 | 168 |
| 15 | 217 | 221 |
| 20 | 310 | 314 |

Every witnessed center placement satisfies \(H/2<q<h\le H\) and \(L^5>2\), so the moving cutoff admits its \(h\) for all \(K\ge5\). If \(k_3(K)\) denotes the \(h=3\) crossing, the first simultaneous scale for exclusion of an odd actual summand and a nonzero residual group has exponent at least \(\max(159,k_3(K))\). The witnesses attain this lower bound for \(5\le K\le11\) and for \(K=12\). The original prefix removes actual summands \(h=3,\ q=(N-n)/3\) at \((k,n)=(56,7),(159,11),(168,157)\), with \(q\) odd, squarefree and coprime to \(3\). The corresponding \(K\) values are \(5,11,12\). Those three additional primality and support checks certify a nonzero actual exclusion at the stated targets. [Original strict prefix and model](https://github.com/Sodelin/Research-Commons/blob/1686bc4d17e561da53ef5f0f312f0c9fa9dfc021/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/2026-11-23-cofactor-cells-1718z/README.md#gb-prefix-residual--missing-estimate)

## Necessary scales and exact support

Keep \(m=qh\) squarefree and odd with \(\mu(m)=-1\) and the original typical count and mark tests. Keep \(n=N-qh=\ell uws\) squarefree and \(Y_0=\exp(L^{.005})\)-rough. Use prime \(N^{1/10}<\ell\le N^{1/8}\), prime \(w>N^{1/5}\), \(\ell w>N^{13/40}\), \(u>N^{1/5}\), \(d=uws>N^{21/40}\), and \(A=L/20\le\log(u/(ws))\le B=L/10\). In each fixed \((q,h,\ell,w)\) group let \(r=d/w=us\) have ordered primes \(p_1,p_2,\ldots\). Retain \(z<p_1\le N^{1/100}\), the short-cofactor exclusion, \(p_2\le N^{f_1(\log p_1/L)}\), and either \(p_2>N^{1/100}\) or \(p_3\le N^{f_2(\log p_2/L)}\). Here \(f_j(t)=\gamma_j(100t)^{1/4}\), with \(\gamma_1=7/160,\ \gamma_2=1/25\). [Original count masks and weights](https://github.com/Sodelin/Research-Commons/blob/290227d6b4b2b5e69e39b241332620885c661ced/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-selberg-ratio-strips-2158z.md) · [Gap and short-cofactor masks](https://github.com/Sodelin/Research-Commons/blob/c44fa72ccea39f009cdbad6cca195a058d9e2da8/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-prime-gaps-2310z.md)

Since \(m\) is odd, \(n,r\) are odd. The intermediate prime \(p_1\) is at least \(3\). Thus \(2^k\ge3^{100}\) and \(k\ge159\). In the two-small-prime branch \(p_2\le N^{1/100}\), squarefreeness implies \(p_2\ge5\), so \(2^k\ge5^{100}\) and \(k\ge233\). The exact integer bit lengths are \(159\) and \(233\). These are hand lower bounds on the first possible target, with no statistical assumptions.

The growing-depth formula is \(z=\exp(\kappa L\sqrt{\log\log L}/\log L)\). In these finite witnesses \(z<Y_0<3\) for every \(0<\kappa<.01\). All endpoint primes exceed both, so the exact Selberg weight is one. Every admitted allocation has \(s/(s,p_1)>1\), so the short-cofactor exclusion does not change the tested groups. The proof's asymptotic hypothesis \(z\ge Y_0\) has its own necessary scale
\[
 \kappa L^{.995}\frac{\sqrt{\log\log L}}{\log L}\ge1 .
\]
For \(k\ge159\) the left side increases with \(k\). Even the upper envelope \(\kappa=.01\) first reaches this at \(k=680\). For illustration, \(\kappa=.001\) reaches it at \(k=8940\). This is the roughness ordering alone. The finite computation checks the arithmetic expression evaluated with its original cutoffs, while the depth estimate concerns its stated asymptotic regime. [Growing-depth hypothesis and choice](https://github.com/Sodelin/Research-Commons/blob/8c3909881dfde768da94b504170a7b61c294ce6e/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-sieve-depth-2257z.md#a-choice-of-growing-depth-and-its-budget)

## Targeted finite verification

A table of smallest factors for \(2^{159}\) already requires about \(2.9\times10^{48}\) bytes at four bytes per entry. The targeted search chooses actual primes \(\ell,w,b\), uses small endpoint primes \(3,5\) or \(3,5,7\), and requires \(n\) to be a multiple of their product with \(\ell wb\). Choose \(q=11\cdot13\cdot17\cdot19\cdot23\cdot Q\) with \(Q\) prime, and solve \(qh\equiv N\) modulo that product for an \(h\) inside the original square. Test \(h\) and the quotient \(a=n/(\ell w b\cdot3\cdot5)\), or \(a=n/(\ell w b\cdot3\cdot5\cdot7)\), for primality. Choose \(b\) so that the ratio is near the relevant edge. The retained witnesses have \(Q,h,a\) prime, count profile \((0,7,0)\), and zero marks. Recursive certificates verify the primes by the factorization of each \(p-1\) and multiplicative orders. Integer powers check the ratio and polynomial cutoffs. Interval arithmetic checks the logarithmic cutoffs.

| \(k\) | Residual branch | Ratio edge | All allocations of \(r\) | Admitted | Complete \(p_1\) pairs | Signed group weight |
| ---: | --- | --- | ---: | ---: | ---: | ---: |
| 159 | \(p_2>N^{1/100}\) | lower | 16 | 3 | 1 | \(-0.784484\) |
| 159 | \(p_2>N^{1/100}\) | upper | 16 | 1 | 0 | \(+0.120650\) |
| 168 | \(p_2>N^{1/100}\) | lower | 16 | 3 | 1 | \(-1.125637\) |
| 233 | \(p_2\le N^{1/100},\ p_3\le N^{f_2}\) | lower | 32 | 7 | 3 | \(-0.239901\) |

The weights are the original group weights before the external factor of two. The finite witness at \(k=233\) has \(\mu(n)=-1\), and the other three have \(\mu(n)=+1\). Both expanded endpoint parities belong to this Type II expression. At \(k=159\) in the lower-edge group the three admitted \(u\)'s are \(3a,5a,15a\). The last two cancel while \(u=3a\) loses its partner \(a\) at the lower edge. At the same \(k\) the upper-edge group admits \(u=a\) and rejects \(3a\) above the upper edge. With \(\mu(h)=-1\), the groups have opposite signs. At \(k=233\), the seven admitted \(u\)'s are \(ag\) for \(g\mid105,\ g>1\). The three complete pairs again leave \(3a\) with negative sign. Thus the first nonzero negative groups occur exactly at the two necessary arithmetic scales. The sampling chooses groups near the edges on purpose.

Exact inputs are given as \((k,\mathrm{edge},q,h,\ell,w,b,a)\), with \(r=3\cdot5\cdot b\cdot a\) for \(k=159,168\), and \(r=3\cdot5\cdot7\cdot b\cdot a\) for \(k=233\).

~~~text
159 lower 535940555633036335071719 710969094086320223648287 61151 58792437043 413527243 15681664908492075232391
159 upper 545290077931866731186437 569558979167207793668909 61151 58792437043 15193259 512818841075326183651391
168 lower 10765366403370017646828907 15811676784251879096466463 114113 239277928529 1439993069 345766582217683808000297
233 lower 72042839621785099898717296354770397 76437229570925056225036068732115421 10327627 6046386117094909 1685145979367 750903462396218712713237283893591
~~~

## Remaining fixed-target estimate

The witnesses rule out an identity forcing every surviving group to vanish. They give neither the signed total over all groups nor the total of their negative parts. The original fallback budget still needs
\[
 2\mathcal D_{\rm res}(N)+\tfrac{53}{1200}N
 \le M_0(N)+E_{\rm other}(N)-\eta N
\]
for fixed \(\eta>0\) at every sufficiently large power of two. A concrete next estimate is a lower bound for the sum of both signed ratio edges on the first remaining branch \(p_2>N^{1/100}\) at fixed \(N\), keeping the prime placements and the original other signed rows in that budget. The least-prime threshold is a hand argument. The support and signs of the four groups are certified finite computation. Lean formalization remains open. [Original budget and normalizations](https://github.com/Sodelin/Research-Commons/commit/c44fa72ccea39f009cdbad6cca195a058d9e2da8)
