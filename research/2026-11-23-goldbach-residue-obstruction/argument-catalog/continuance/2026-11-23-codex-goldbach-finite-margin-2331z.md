# The original Goldbach budget on the three replay targets

23 November 2026. Finite replay and a separate hand comparison. Reference ID GB-ORIGINAL-MARGIN-2331. The replay computes the residual expression \(M_0+E_{\rm other}\) at the same three powers of two used for the original positive Type II strip. All Type II values use the original expansion and its signed weights. [Pinned same-target budget after the gap charges](https://github.com/Sodelin/Research-Commons/blob/c44fa72ccea39f009cdbad6cca195a058d9e2da8/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-prime-gaps-2310z.md#summing-the-marked-primes-and-the-fixed-target-budget)

## The sums evaluated

Put \(H=\sqrt N\), \(L=\log N\), \(Q=N^{1/4}\) and \(P=N^{21/40}\). Use the analytic prefix cutoff \(h>\alpha=H/L^K\), with the seven outer windows restricted by \(q<HL^B\), \(h>H/L^B\). At these targets, \(H Q/L^5<1\) and \(H L^3>N\). Thus every admissible analytic choice with \(K\ge5\), \(B\ge3\) gives exactly the same finite support of the actual rows and the same low-model prefix. Use \(h>H/2\) also as a separate cutoff sensitivity check. The center lies in \((H/2,H]^2\) in both cases. [Moving-prefix comparison and model](https://github.com/Sodelin/Research-Commons/blob/1686bc4d17e561da53ef5f0f312f0c9fa9dfc021/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/2026-11-23-cofactor-cells-1718z/README.md#gb-prefix-residual--missing-estimate)

Let \(E_{\rm low}\) be the exact actual-minus-model row for \(q<Q\). Let \(E_{\rm outer}\) be the seven high-\(q\) actual cells outside the center after detaching admissible high-\(q\) companions of the marked sources. Let \(C_+\) be the even-endpoint signed center on squarefree \(Y_0\)-rough \(n\), the strict \(d>P\), and the original unmarked middle-count and two below-cutoff-count restrictions. Keep the other signed center terms on that support. Let \(S_{\rm band}\) be its actual typical odd-\(qh\) prime-tested subband with \(N^{1/10}<\ell\le N^{1/8}\). Replace that subband by the original Type II terms with \(U=V=N^{1/5}\), \(\ell w>N^{13/40}\), the same square, and the exact ratio test. The square equals one at these finite fixtures, since its original index exponent is below \(1/100\). Denote the Type II subtotal outside the positive stress strip by \(T_{\rm off}\). The replayed expression is

\[
 E_{\rm other}=E_{\rm low}+E_{\rm outer}
                 +2\bigl(C_+-S_{\rm band}+T_{\rm off}\bigr).
\tag{1}
\]

This retains the earlier budget's endpoint-parity normalization. The finite parity difference is recorded in the replay separately. The exact signed Type I and below-base terms were also evaluated, so the arithmetic band identity is checked before using its asymptotically charged representation. [Center and parity budget](https://github.com/Sodelin/Research-Commons/blob/b29f3312eb2ff6c04eaf3e1ce592f63b5f711a74/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/determinant-20-over-19-ledger-reply.md#exact-center-after-both-rough-factor-charges) · [Original square and Type I transfer](https://github.com/Sodelin/Research-Commons/blob/290227d6b4b2b5e69e39b241332620885c661ced/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-selberg-ratio-strips-2158z.md)

## Finite headroom

All entries are divided by \(N\). The last two columns are after subtracting \(53/1200\), including the \(1/600\) short-cofactor allocation. The table uses the midpoint of the singular-series enclosure before rounding.

| Target | \(M_0\) | \(E_{\rm low}\) | \(E_{\rm outer}\) | Other doubled center | \(M_0+E_{\rm other}\) | Room, analytic cutoff | Room, \(H/2\) cutoff |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| \(2^{20}\) | 1.316126 | 0.019990 | 1.291940 | −0.004106 | 2.623951 | 2.579784 | 1.245131 |
| \(2^{22}\) | 1.318466 | −0.010781 | 1.337440 | 0.013047 | 2.658171 | 2.614004 | 1.269796 |
| \(2^{24}\) | 1.320439 | 0.007856 | 1.305263 | −0.011749 | 2.621809 | 2.577643 | 1.273427 |

The large analytic-cutoff figures are pre-asymptotic. Here \(\alpha<1\), so the actual sum admits every positive cofactor. The signed \(q>H,\ h\le H/2\) cell alone contributes \(1.305675N,\ 1.322423N,\ 1.305650N\), respectively. Removing that measured positive cell from the analytic-cutoff diagnostic leaves \(1.274108N,\ 1.291581N,\ 1.271993N\) of headroom. The historical cutoff excludes the cell and still leaves over \(1.24N\) at all three targets. The first table therefore answers the finite margin question, while its change under the cutoff is substantial.

The \(\Lambda\)-weighted sums were evaluated by sieve and exact divisor incidences, with logs evaluated numerically. The singular series is \(2\prod_{p>2}(1-(p-1)^{-2})\), with partial product through \(2^{24}\) and a tail enclosure from \(\sum_{j\ge2^{24}}j^{-2}\le(2^{24}-1)^{-1}\). The cutoffs in the Type II row were tested by integer powers. Real-valued mask edges were checked with 80-digit arithmetic. Direct low-modulus loops cross-checked both cutoff conventions at \(2^{20}\); independent endpoint and center enumerations agreed in the raw center. The original archived strip weights and its raw negative totals also agreed. In all three fixtures \(N^{1/100}<2\), so the intermediate-prime row is empty. These figures measure room in the displayed expression. The analytic errors in the moving-prefix comparison are asymptotic, so the expression need not equal the finite Goldbach count. [Original finite strip support and signed normalization](https://github.com/Sodelin/Research-Commons/blob/38ef35f193f2098942b64baf461128a06278482f/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-negative-ratio-budget-2217z.md#finite-powers-of-two-replay-of-the-new-groups)

## A joint hand budget with the original parameters

The peer auxiliary sieve bounds the absolute paired weight of the original prime-tested band \(S_{\rm band}\) after doubling by \(0.004N\) at sufficiently large powers of two. Its upper constant on \(1/10<\log\ell/L\le1/8\) is at most \(J\Pi\cdot2\log(1694/1619)<0.004\), \(J=3/8-\log2/2\), \(\Pi=\prod_{p>2}(1+1/[p(p-1)])\). The masks that define the tested band only restrict that absolute count, and its larger-prime cutoff is the same \(P\). The numerical constant and the summed completion powers in the auxiliary proof were checked. [Pinned auxiliary sieve on the actual prime-tested band](https://github.com/Sodelin/Research-Commons/blob/36624845444790787f442157309e7f9ba6644ad0/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-powers-two-margin-and-odd-semiprime-budget.md#a-direct-charge-on-the-original-odd-semiprime-row)

Apply this bound through the original equality \(S_{\rm band}=T_{\rm off}+T_{\rm strip}+o(N)\), including the original Type I and below-base charges. It controls the **signed sum of all ratios in this band together**, at the same target and with the original square. Define

\[
 E_{\rm outside\ band}(N)
   =E_{\rm low}(N)+E_{\rm outer}(N)+2(C_+(N)-S_{\rm band}(N)).
\]

The separate square-lane proof gives the original \(M_0(2^k)>0.330N\) eventually, independent of the Type II representation. Therefore a sufficient lower bound for the joint original-band budget is

\[
E_{\rm outside\ band}(2^k)\ge -(0.326-\eta)N
\quad\text{for some fixed }\eta>0
\]

at every sufficiently large power of two. This condition concerns the original other signed rows, including the centered low-modulus row, outer actual interiors and remaining center after taking out only the narrow prime-tested band. The joint narrow-band charge already accounts for its strip and its off-strip rows. Their separate \(53N/1200\) allowance belongs to the earlier inequality. The fixed-target lower bound on \(E_{\rm outside\ band}\) remains open. [Original Type II equality](https://github.com/Sodelin/Research-Commons/commit/290227d6b4b2b5e69e39b241332620885c661ced) · [Separate model lower bound](https://github.com/Sodelin/Research-Commons/commit/d9ac2acb4650d202d5cd84c3604a62655a6c037d)
