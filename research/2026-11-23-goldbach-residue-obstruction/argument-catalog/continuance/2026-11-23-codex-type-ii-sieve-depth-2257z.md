# Sieve-depth decay for the forced-prime Type II edge weight

23 November 2026. Unconditional hand proof at each fixed even target. Reference ID GB-TYPE-II-SIEVE-DEPTH-2257. The parallel forced-prime proof controls the two ratio edges using the same prime in the Selberg square and in the edge width. Its unit tilt gives dependence \(e^{-s}\) at sieve depth \(s\). The larger tilt below keeps the interval-width saving and improves the depth factor to \(\exp(-s\log s-s\log\log s+O(s))\). [Pinned forced-prime edge proof](https://github.com/Sodelin/Research-Commons/blob/afdd68bddac5fb1d4d4c778f59475d454c180c30/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-type-ii-forced-prime-ratio-edges.md)

## Exact support and bound

Write \(L=\log N,\ H=\sqrt N,\ m=qh,\ n=N-m=\ell uwc\), with \(c=v/w\). Keep the paired odd-\(m\) Type II support \(H/2<q<h\le H\), squarefree \(m,n\), \((m,N)=1\), the roughness \(Y_0=\exp(L^{.005})\) on \(n\), and the original \(m\) count and mark mask \(F(m)\). Keep prime \(N^{1/10}<\ell\le N^{1/8}\), \(u>N^{1/5}\), prime \(w>N^{1/5}\), \(v=wc\), and every original sharp cutoff, including \(d=uv>D_0\). Use the positive strip \(L/20\le\log(u/v)\le L/10\). At fixed \(q,h,\ell,w\) define \(r=d/w=uc\) and \(G_{q,h,\ell,w}\) to be the signed sum over the eligible \(u\)'s with its original weight

\[
F(m)W_N(n)\mu(h)\mu(u)\log(h/q)\frac{\log\ell\log w}{\log d}.
\]

Use exactly the pinned optimal Selberg coefficients at \(D=N^\kappa\), where \(\kappa<1/100\) is fixed small enough for that Type I transfer, and prime support at most \(z\), with \(Y_0\le z\le N^{\delta_0}\). Here \(\delta_0>0\) is a fixed small upper bound such that \(s=\log D/\log z\ge s_0\) for a sufficiently large absolute \(s_0\). For a fixed original square take \(z=N^\delta\) in that range and change none of its coefficients. The bound below is uniform also when \(z\) varies in the stated range.

For any selected set \(\mathcal P\) of primes at most \(z\), put

\[
\mathcal D_{\mathcal P}
=\sum_{\substack{q,h,\ell,w\\P^-(r)\in\mathcal P}} (G_{q,h,\ell,w})_- ,
\qquad \Psi(s)=\exp\{-s\log s-s\log\log s+C_1s\}.
\]

There are absolute constants \(C_1,C\) such that

\[
\mathcal D_{\mathcal P}
\le C\,\frac{\varphi(N)L}{(\log z)^3}\,\Psi(s)
       \sum_{p\in\mathcal P}\frac{(1+\log p)^2}{p}
       + O_{A,\kappa}(N/L^A)
\tag{1}
\]

for each fixed \(A\). The statement holds as well for absolute grouped weights and when restricting to either expanded endpoint parity. In particular the sum over all \(p\le z\) is \(O(\varphi(N)(L/\log z)\Psi(s))+O_{A,\kappa}(N/L^A)\). [Pinned square and exact Type II expansion](https://github.com/Sodelin/Research-Commons/blob/290227d6b4b2b5e69e39b241332620885c661ced/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-selberg-ratio-strips-2158z.md)

## The log-product law with a larger tilt

Let \(Z=\log z\) and use the dimension-two Euler law of the pinned square. At each prime \(q\le z\), let \(B_q\) be independent Bernoulli of probability \(g_q=f_q+(1-f_q)/q\), where \(f_q=(q-1)/q^2\) for \(q\nmid N\) and \((2q-1)/q^2\) for \(q\mid N\). Put \(b(q)=g_q/(1-g_q)\). On omitting one marked prime \(p\), write \(T=\sum_{q\le z,\ q\ne p}B_q\log q/Z\). The next two bounds also hold with no omission.

For \(1\le \lambda\le Z\) the moment \(M_\lambda=\mathbb E e^{\lambda T}\) satisfies

\[
\log M_\lambda\le \sum_{q\le z}g_q(q^{\lambda/Z}-1)\ll \frac{e^\lambda}{\lambda}.
\tag{2}
\]

For \(q\le\sqrt z\), convexity bounds \(q^{\lambda/Z}-1\) by \(2(e^{\lambda/2}-1)\log q/Z\). Using \(g_q\ll1/q\) and \(\sum_{q\le\sqrt z}\log q/q\ll Z\) gives \(O(e^{\lambda/2})\). For larger primes divide \((1/2,1]\) in the variable \(\log q/Z\) into intervals of length at most \(1/\lambda\), starting at \(1\). In the \(j\)-th interval from the top, \(q^{\lambda/Z}\le e^{\lambda-j}\), and its prime reciprocal mass is \(O(1/\lambda+1/Z)=O(1/\lambda)\) by Chebyshev and partial summation. Sum the resulting geometric bounds to prove (2). All constants are absolute.

Tilt by the density \(e^{\lambda T}/M_\lambda\), and use \(\mathbb P_\lambda\) for the tilted law. Its odds at \(q\) are the old odds multiplied by \(q^{\lambda/Z}\), in particular at most \(e^\lambda b(q)\). The probabilities of no selected prime above a threshold only decrease. By Mertens and the explicit dimension-two factors, the old probability that no prime above \(e^{2B}\) is selected is \(O((B/Z)^2)\) for \(1/2\le B\le Z\), with an absolute constant even after omitting \(p\). Indeed \(1-g_q\le (1-1/q)^2(1+1/[q(q-1)])\) for every prime, and omitting one prime costs at most eight. For \(2B\ge Z\) the same bound follows by increasing the absolute constant.

Let \(I\) be a log interval of width \(\Delta\le Z\) avoiding zero. Partition by dyadic \(B\) for the largest selected prime, with \(B<\log q\le2B\). Conditional on no prime above \(e^{2B}\), the lower flags are independent. For their log sum \(U\), summing over a selected \(q\) in the bin gives the upper bound

\[
\mathbb E_\lambda
\sum_{\substack{B<\log q\le2B\\U\in I-\log q}}
 \frac{\mathbb P_\lambda(B_q=1)}{\mathbb P_\lambda(B_q=0)}
\ll e^\lambda\frac{1+\Delta}{B}.
\]

For this inequality, the contribution with \(q\) selected is its probability times the probability that the sum of other flags is in \(I-\log q\). Including the configuration with \(q\) unselected in the distribution of \(U\) bounds that product by the displayed odds times the indicated probability. At each value of \(U\) the eligible primes lie in a log interval of width at most \(\Delta\) above \(e^B\). The same prime reciprocal bound applies there. Multiply by \(O((B/Z)^2)\) and sum the dyadic \(B\)'s to obtain

\[
\mathbb P_\lambda(ZT\in I)\ll e^\lambda(1+\Delta)/Z.
\tag{3}
\]

Use \(I=(\log(D/p),\log D]\), so \(T>s-1\) and \(\Delta=\log p\). Choose \(\lambda=\log s+\log\log s\). It lies in \([1,Z]\) for sufficiently large \(N\) uniformly in the stated range, since \(Z\ge L^{.005}\) and \(s\le\kappa L/Z\). Moreover \(e^\lambda/\lambda\le s\). Undo the tilt in (3), using (2) and the lower edge \(T>s-1\), to give

\[
\mathbb P_0(ZT\in I)
\ll \frac{1+\log p}{Z}
       \exp\!\left(O(e^\lambda/\lambda)-s\lambda+2\lambda\right)
\ll \frac{1+\log p}{Z}\Psi(s).
\tag{4}
\]

This bound retains the width of the interval even at the larger tilt. The argument includes no zero-product atom in \(I\).

## Transfer to the exact signed groups

On squarefree indices extend \(b\) multiplicatively, and let \(G_D=\sum_{a\le D}b(a)\) restricted to primes at most \(z\). The pinned diagonal identity gives the model expectation

\[
\mathbb E[WB_p]=g_pG_D^{-2}
              \sum_{\substack{D/p<a\le D\\p\nmid a}}b(a).
\]

The full Euler total \(G_\infty=\prod_{q\le z}(1+b(q))\) normalizes the log law. Equation (2) at \(\lambda=1\) implies \(G_D/G_\infty\ge1-O(e^{-s})\), hence \(G_D\asymp G_\infty\) uniformly at depth \(s\ge s_0\). Mertens and the explicit local factors give

\[
G_D^{-1}\ll\frac{\varphi(N)}{N Z^2};
\]

the primes dividing \(N\) beyond \(z\) have total reciprocal mass \(O(L/z)\), so the totient factor is uniform for \(z\ge Y_0\). Applying (4) to the Euler law omitting \(p\) yields

\[
\mathbb E[WB_p]\ll G_D^{-1}\frac{1+\log p}{pZ}\Psi(s).
\tag{5}
\]

For the exact arithmetic transfer, use the peer's two ratio edges. On trimming \(n<N/L^{B_0}\) at arbitrary log saving, any allocation whose ratio is admitted has \(u>U=N^{1/5}\). Moving the least prime \(p\) leaves the group prefactor fixed, flips \(\mu(u)\), and shifts \(\log(u/v)\) by \(2\log p\) in magnitude. Complete pairs cancel. At fixed \(\ell,p\) and dyadic endpoint band \(j\), the leftover placements occupy \(O(1+\log p)\) dyadic ranges of \(v\), since \(v\) is the smaller factor and \(2\log v=\log(n/\ell)-\log(u/v)\). For the absolute count in these ranges one can retain \(p\mid n\) while enlarging the remaining tests. Sum the positive \(\log w\) weights over \(w\mid v\), bounded by \(\log v\). The rectangle area at band \(j\) is at most \(N4^{-j}\). The pinned CRT and harmonic-average transfer then gives the positive upper main term \(O(NL\sum_{p\in\mathcal P}(1+\log p)\mathbb E[WB_p])\).

For clarity the same transfer is uniform in \(z\). Opening the square uses at most \(D^2\) coefficient pairs of magnitude at most one. At fixed \(M=\ell v\le N^{43/80}\), the marker \(p\mid n\) adds at most one \(p\) to the CRT period \([a,b]\le D^2\). The residue enumeration and coefficient sums therefore cost at most \(D^4pN^{o(1)}\) at each \(M,p\), with \(p\mid v\) needing no extra residue. Summing the rectangle errors costs \(N^{129/160+4\kappa+2\delta_0+o(1)}\). The harmonic floor error is \(O(D^2/X)\) at a dyadic scale \(v\asymp X\ge N^{31/80}/L^{O(1)}\), hence the total after summing markers is \(N^{49/80+2\kappa+\delta_0+o(1)}\). Both exponents are below one at the fixed scales. The endpoint trim is uniform since \(W_N(n)\le\tau(n)^2\). Substituting (5) proves (1), with both original Möbius signs used in the toggle. [Pinned edge transfer with all error counts](https://github.com/Sodelin/Research-Commons/blob/afdd68bddac5fb1d4d4c778f59475d454c180c30/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-type-ii-forced-prime-ratio-edges.md#the-same-square-with-one-forced-prime-and-short-moving-ranges)

## A choice of growing depth and its budget

One may choose \(z\) within the original construction as a function of \(N\), for example

\[
z=\exp\left(\kappa L\frac{\sqrt{\log\log L}}{\log L}\right),
\qquad s=\frac{\log L}{\sqrt{\log\log L}} .
\]

This is a valid equivalent Type II expansion for the full prime-tested band. The Type I proof uses only the uniform coefficient bound \(|\lambda_a|\le1\), the period cap \([a,b]\le D^2\), and the product and endpoint masks. Its reciprocal zero-frequency argument sums the same local choices with a reciprocal prime for each used prime, and the ignored large excluded primes of the \(h\)-prefix are controlled by the polynomial bound for the whole excluded modulus. The Type I conditions therefore hold uniformly as the prime support shrinks at fixed \(D\). The exact square still equals one on every original prime-tested endpoint \(\ell d\), since both primes exceed \(z\). The ratio statement uses this choice of square throughout. [Pinned Type I uniform period budget](https://github.com/Sodelin/Research-Commons/blob/290227d6b4b2b5e69e39b241332620885c661ced/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-selberg-ratio-strips-2158z.md#type-i-with-the-polynomial-periods)

At this depth \(s\log s/\log L\to\infty\), so the entire \(P^-(r)\le z\) slice of the selected ratio interval has absolute grouped weight \(O_{A,\kappa}(N/L^A)\) for every fixed \(A\), with the same bounds for its negative part and each expanded endpoint parity. For the original fixed-depth square, (1) gives the stated depth-dependent charge on its own \(p\le z\) range. For either choice, above \(z\) the square is one on the exact support. The peer's squarefree harmonic bound gives the doubled \(N/40\) cap at powers of two for \(p>N^{1/100}\). The unresolved prime range of this strip is \(z<p\le N^{1/100}\), together with the other signed rows of the fixed-target ledger. In that intermediate range the remaining task is to exploit the opposite signs of the two exact edges, since suppression by the square applies only inside its prime support. [Peer \(N/40\) cap and exact threshold](https://github.com/Sodelin/Research-Commons/blob/bc292106d03065e910b8dc6d2bbca1589313169b/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-type-ii-rough-harmonic-cap.md) · [Same-target budget and signed edges](https://github.com/Sodelin/Research-Commons/blob/56abc20768f148741e0fb57b8c4fe82ec0ebb4a8/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-least-prime-edges-2246z.md#remaining-same-target-inequality)
