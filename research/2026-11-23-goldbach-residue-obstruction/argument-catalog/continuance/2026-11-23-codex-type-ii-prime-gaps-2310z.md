# A fixed-target Type II charge for one or two primes followed by a gap

23 November 2026. Unconditional hand proof at sufficiently large powers of two. Reference ID GB-TYPE-II-PRIME-GAPS-2310. The exact two ratio edges allow a separate bound when one or two marked primes are followed by a gap in the prime sizes of \(d/w\). The bound permits the full cofactor range and retains the prior short-cofactor exclusion. [Pinned exact edge formula and original weights](https://github.com/Sodelin/Research-Commons/blob/56abc20768f148741e0fb57b8c4fe82ec0ebb4a8/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-least-prime-edges-2246z.md) · [Peer short-cofactor selection](https://github.com/Sodelin/Research-Commons/blob/8c869fe0a50e029022e7b52f6d57fbc0a198e0f5/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-type-ii-short-complement-bridge.md#a-window-above-a-varying-sieve-support)

## Statement and exact allocation support

Let \(N=2^k\), \(H=\sqrt N\), \(L=\log N\), \(m=qh\), \(n=N-m=\ell uws\), \(v=ws\), and \(d=uv\). Keep \(H/2<q<h\le H\) in the paired odd-\(m\) sum, squarefree \(m,n\), \((m,N)=1\), the original count and mark mask \(F(m)\), and the original endpoint roughness \(Y_0=\exp(L^{.005})\). Keep prime \(N^{1/10}<\ell\le N^{1/8}\), \(u>N^{1/5}\), prime \(w>N^{1/5}\), the strict \(d>D_0\), and any preceding cut on \(n,\ell,w\). The ratio stays in \([A,B]=[L/20,L/10]\). Use the same \(W_N(n)\) with prime support at most \(z\ge Y_0\).

At each fixed \(q,h,\ell,w\), put \(r=d/w\) and write \(p_1<p_2<\cdots\) for its prime factors, with missing primes assigned \(+\infty\) in gap tests. Put \(\beta=1/100\), \(\gamma_1=7/160\), and \(\gamma_2=1/25\). For \(j=1,2\), define

\[
t_j=\log p_j/L,\qquad f_j(t)=\gamma_j(t/\beta)^{1/4}.
\]

Take the gap after \(j\) primes to mean

\[
 z<p_1,\qquad p_j\le N^\beta,\qquad
 P^-\!\left(r/(p_1\cdots p_j)\right)>N^{f_j(t_j)}.
\tag{1}
\]

For \(j=2\) one may exclude every group that qualifies for \(j=1\). The charges on the two resulting disjoint group selections satisfy

\[
 2\mathcal D_{\mathrm{gap},1}(N)\le N/200,\qquad
 2\mathcal D_{\mathrm{gap},2}(N)\le N/80 .
\tag{2}
\]

Here \(\mathcal D\) sums the negative parts of the exact signed subtotals on the stated support. Both caps hold after the short-cofactor removal. More generally any removal common to the two allocations of \(p_1\) at fixed other prime allocations is allowed. This matters when \(j=2\): changing the placement of \(p_2\) can change whether the short-cofactor test holds, while changing the placement of \(p_1\) cannot.

To see the exact signs, put \(P_j=p_1\cdots p_j\), \(r=P_j ab\), and group placements with fixed \(a\mid r/P_j\) and \(b=r/(P_j a)\). For \(\epsilon_i\in\{0,1\}\), take

\[
 u=a\prod_{i=1}^j p_i^{\epsilon_i},\qquad
 s=b\prod_{i=1}^j p_i^{1-\epsilon_i}.
\]

The sign is \(\mu(h)\mu(a)(-1)^{\sum_i\epsilon_i}\), with the original nonsigning factors \(F(m)W_N(n)\log(h/q)\log\ell\log w/\log d\) fixed across these placements. The short-cofactor condition from the previous proof uses \(s\) after dividing out \(p_1\) if present. That cofactor is \(b\prod_{i=2}^j p_i^{1-\epsilon_i}\), independent of \(\epsilon_1\).

Trim \(n<N/L^{B_0}\) by fixed divisor moments at arbitrary log savings, for sufficiently large fixed \(B_0\). On the remaining support every allocation with admitted ratio has \(u\ge N^{37/80}/L^{B_0/2}>N^{1/5}\), and \(v>N^{1/5}\) follows from \(w\). At fixed \(\epsilon_i\) for \(i\ge2\), the two allocations of \(p_1\) have opposite signs. Their ratios differ by \(2\log p_1\), and they cancel if both are admitted. The surviving allocations have \(\rho\in[A,A+2\log p_1)\) with \(p_1\mid u\), or \(\rho\in(B-2\log p_1,B]\) with \(p_1\mid s\). Here \(\rho=\log(u/v)\), and \(2\beta< (B-A)/L\) ensures both are within the original strip. Thus for \(j=2\) there are two such pairs to count. The bound uses cancellation in each pair, including when the prior removal separates the two pairs.

## The two edge counts with a rough quotient

On (1) all factors of \(n\) exceed \(z\), so the original \(W_N(n)=1\). The factors of \(a,b\) exceed \(Y=N^{f_j(t_j)}\). In this range \(Y>p_j\) and \(Y<N^{1/10}\). On a surviving edge \(M=\ell w bP_j\) satisfies

\[
 M=\ell v\prod_{\epsilon_i=1}p_i\le N^{43/80+j\beta},
 \qquad a=(N-qh)/M.
\tag{3}
\]

The bound for \(\ell v\) follows from \(v^2=n e^{-\rho}/\ell\). At fixed marked primes, \(\ell,b\), and allocation branch, \(2\log w\) equals \(\log n-\rho\) plus a fixed constant. The allowed actual primes \(w>N^{1/5}\) are therefore in a log interval of width at most \(\log p_1+O_{B_0}(\log L)\). Their sum of \((\log w)/w\) is at most \((1+o(1))\log p_1\) uniformly since \(\log p_1\ge L^{.005}\).

When \(p_1\mid u\), the edge has \(b\le v/w\le N^{9/40}\). When \(p_1\mid s\), the edge has \(\rho>B-2\log p_1\) and \(b\le v/(wp_1)\le N^{1/5}\). Any extra \(p_2\) in \(s\) only decreases these upper bounds. For either exponent \(c=9/40,1/5\), the rough reciprocal sum over \(b\le N^c\) is at most

\[
 \prod_{Y<r_0\le N^c,\ r_0\ {\rm prime}}(1-1/r_0)^{-1}
 = (1+o(1))\,\frac{c}{f_j(t_j)}
\]

uniformly in the marked primes. This uses \(Y\to\infty\) uniformly even for the moving lower frontier, and includes \(b=1\).

At fixed \(\ell,w,p_1,\ldots,p_j,b\), use the one-dimensional auxiliary Selberg square of level \(Y\) for the condition \(P^-(a)>Y\). Omit the \(j\) marked primes from the sieve since they divide \(M\). Every other factor of \(M\) exceeds \(Y\). The omission changes the truncated Selberg denominator by only a relative \(O(j/z)\): for each marked prime \(p_i\), its part of that denominator is at most \(b_0(p_i)\) times the full denominator, where \(b_0(p_i)=g_{p_i}/(1-g_{p_i})=O(1/p_i)\). Here the local densities are \(g_2=3/4\) at the prime two and \(g_r=(r-1)/r^2\) at odd primes. The pinned normalization gives \(G(Y)\sim(2/\Pi)\log Y\), \(\Pi=\prod_{r>2}(1+1/[r(r-1)])\). Thus the omitted-prime square has the same reciprocal main coefficient \((1+o(1))\Pi/(2 f_j(t_j)L)\), uniformly.

The fixed-modulus upper count with log weight uses \(q h=N\bmod M\). The ordered log factor has normalized integral \(J=3/8-(\log2)/2\) over \(H/2<q<h\le H\). Use the same upper rectangle grid and completion as in the pinned rough cap. The capped \(M\) is kept during completion. The error at fixed \(M\) is \(Y^4 N^{o(1)}(M^{1/2}+H/M^{1/2})\). Each \(M\) has at most \(d_{j+3}(M)=N^{o(1)}\) representations, including all marked-prime and cofactor choices. With \(Y\le N^{\gamma_j}\), the two summed exponents from (3) are

\[
\begin{array}{c|cc}
j& (3/2)(43/80+j\beta)+4\gamma_j
 & 1/2+(43/80+j\beta)/2+4\gamma_j\\ \hline
1&797/800&759/800\\
2&797/800&751/800 .
\end{array}
\]

The full error with all weights is \(o(N)\). After completion the nonnegative main term uses \(\varphi(M)/M^2\le1/M\). These upper counts enlarge the original masks only after the exact within-pair cancellation. [Pinned auxiliary one-dimensional sieve and completion](https://github.com/Sodelin/Research-Commons/blob/b8d0afa3e5fab3380f662ce172eacad56ea05316/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-rough-negative-cap-2234z.md#sieve-at-the-modulus-ell-ws)

## Summing the marked primes and the fixed-target budget

The actual \(\log d\) is at least \(L-\log\ell-B_0\log L\) after the trim. The prime-\(\ell\) harmonic sum with weight \((\log\ell)/(\ell\log d)\) is bounded by \(I+o(1)\), where \(I=\int_{1/10}^{1/8}dx/(1-x)=\log(36/35)\). The edge \(w\) width produces \(\log p_1\), and the two \(b\) caps sum to \(17/40\) in the numerator of the reciprocal estimate. After the external doubling, the main charge divided by \(N\) is at most

\[
 2^{j-1} J\Pi I\,\frac{17}{40}
 \sum_{z<p_1<\cdots<p_j\le N^\beta}
 \frac{t_1}{p_1\cdots p_j\,f_j(t_j)^2}+o(1).
\tag{4}
\]

For \(j=2\), the inner sum over \(p_1<p_2\) of \(t_1/p_1\) is at most \(t_2+O(1/L)=(1+o(1))t_2\), uniformly because \(p_2>z\). This leaves the same one-prime bound as for \(j=1\). Since \(t/f_j(t)^2=\beta^{1/2}t^{1/2}/\gamma_j^2\), Mertens and partial summation give

\[
 \sum_{z<p\le N^\beta}\frac{t}{p f_j(t)^2}
 \le \frac{\beta^{1/2}}{\gamma_j^2 L^{1/2}}\sum_{p\le N^\beta}\frac{\sqrt{\log p}}p
 =\frac{2\beta}{\gamma_j^2}+o(1).
\]

In the final step \(\sum_{p\le x}\sqrt{\log p}/p=2\sqrt{\log x}+O(1)\) follows by applying partial summation to \(\sum_{p\le x}(\log p)/p=\log x+O(1)\). Hence the bound remains finite uniformly as \(\log z/L\to0\). With \(J<57/2000,\ \Pi<34/25,\ I<1/35\), the rational upper coefficients in (4) are \(131784/26796875<1/200\) and \(16473/1400000<1/80\). The strict slack absorbs the \(o(1)\) terms. If retaining \(\ell w>N^{13/40}\), the factor \((17/40)I\) in (4) can also be replaced by \((51/40)I-1/40\), using the peer's two smaller cofactor caps with the actual \(\ell\). [Pinned base-aware cofactor inequality](https://github.com/Sodelin/Research-Commons/blob/483ffd44dc87b1ca58b1b22c9a721f242699ebfe/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-type-ii-base-aware-rough-cap.md)

For the same-target ledger, choose the growing-depth square of the previous result. It gives \(O_A(N/L^A)\) for \(p_1\le z\) on this strip. The doubled charge for \(p_1>N^\beta\) is at most \(N/40\). On \(z<p_1\le z^2\), the short-cofactor selection with \(p_1\)-free \(s\) equal to \(1\) has doubled charge at most \(N/600\) by the peer estimate at \(C=1,K=2\). Remove that selection first, then the \(j=1\) gap and the \(j=2\) gap in disjoint order. Write \(\mathcal D_{\rm res}\) for the grouped negative mass of the remaining intermediate allocations. Subadditivity of the negative part gives the sufficient inequality

\[
 2\mathcal D_{\rm res}(N)+\frac{53}{1200}N
 \ \le\ M_0(N)+E_{\rm other}(N)-\eta N,\qquad N=2^k,
\tag{5}
\]

for a fixed \(\eta>0\) at all sufficiently large powers of two. The comparison term is \(M_0\), and \(E_{\rm other}\) is the signed sum of the other rows using the same expansion. The negligible low-prime charge is absorbed in the margin. The remaining pairs and the other rows still require this joint fixed-target bound. The peer's whole-strip \(71N/1000\) charge belongs to another equivalent expansion, with its other rows evaluated at that expansion's square and cutoffs. The later full-range semiprime reduction trims the larger-prime cutoff and leaves a signed interior as well. [Growing-depth choice](https://github.com/Sodelin/Research-Commons/blob/8c3909881dfde768da94b504170a7b61c294ce6e/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-sieve-depth-2257z.md) · [Peer base-aware and alternate caps](https://github.com/Sodelin/Research-Commons/commit/483ffd44dc87b1ca58b1b22c9a721f242699ebfe) · [Full-range semiprime reduction](https://github.com/Sodelin/Research-Commons/blob/ef82e66f32ed05a21477543b6aa57c1b2bb6739a/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-goldbach-semiprime-cutoff-2308z.md#a-type-ii-reduction-for-the-full-semiprime-range) · [Exact signed budget](https://github.com/Sodelin/Research-Commons/blob/38ef35f193f2098942b64baf461128a06278482f/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-negative-ratio-budget-2217z.md#fit-to-the-fixed-target-budget)

## Evidence

This is a hand proof on the stated support. The two rational constants and both completion exponents were checked with exact arithmetic. A separate finite calculation checked the signs and the strict ratio edges in 2,403 rational log-placement cases after removing the short-cofactor pairs. It checks the allocation algebra at and between all tested boundaries.
