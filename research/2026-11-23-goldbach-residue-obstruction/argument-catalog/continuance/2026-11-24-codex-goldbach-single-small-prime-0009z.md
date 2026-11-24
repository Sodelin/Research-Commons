# A fixed-target bound for the residual with one prime at most \(N^{1/100}\)

24 November 2026. Reference GB-ONE-SMALL-PRIME-0009. This hand proof uses the original positive Type II strip, Selberg square, and residual after the short-cofactor and two gap charges. It gives a bound at each sufficiently large \(N=2^k\). [Original support and \(53N/1200\) budget](https://github.com/Sodelin/Research-Commons/blob/c44fa72ccea39f009cdbad6cca195a058d9e2da8/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-prime-gaps-2310z.md)

## Statement and exact support

Write \(\beta=1/100,\ L=\log N,\ H=\sqrt N,\ A=L/20,\ B=L/10\). Retain \(H/2<q<h\le H\), \(m=qh\) odd and squarefree with \(\mu(m)=-1\), its original count and mark mask \(F(m)\), and the original moving cutoff. Keep \(n=N-m=\ell uws\) squarefree and \(Y_0=\exp(L^{.005})\)-rough. Keep actual primes \(N^{1/10}<\ell\le N^{1/8}\), \(w>N^{1/5}\), the strict base cutoff \(\ell w>N^{13/40}\), \(u>N^{1/5}\), and \(d=uws>N^{21/40}\). The ratio \(\rho=\log(u/(ws))\) remains in \([A,B]\).

In each fixed \((q,h,\ell,w)\) group write \(r=d/w\), \(p=P^-(r)\) and \(P\) for the second prime of \(r\). The selection here is exactly
\[
 z<p\le N^\beta<P\le N^{f(t)},\qquad
 t=\log p/L,\qquad f(t)=\tfrac7{160}(t/\beta)^{1/4},
\]
after the original short-cofactor exclusion. These are the residual groups that miss the first gap cut and have \(P>N^\beta\). They are disjoint from the second gap charge and the remaining branch \(P\le N^\beta\). With \(\mathcal D_1\) equal to the sum of the negative parts of the exact selected groups in this branch, the conclusion is
\[
 2\mathcal D_1(N)\le N/72 .
\tag{1}
\]
The same bound holds for the sum of their absolute grouped weights after doubling. In particular the original signed contribution from this branch is bounded below by \(-N/72\) after doubling.

The inequality \(f(t)>\beta\) forces \(t>t_*=\beta((8/35)^4)=1024/37515625\). All factors of \(r/p\) exceed \(Y=N^\beta\). Since \(\log z=o(L)\) for the growing-depth choice, \(p>z^2\) eventually in this branch. The endpoint square \(W_N(n)\) equals one on the exact support. The proof keeps both expanded endpoint parities. [Growing-depth square and original Type II expansion](https://github.com/Sodelin/Research-Commons/blob/8c3909881dfde768da94b504170a7b61c294ce6e/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-sieve-depth-2257z.md#a-choice-of-growing-depth-and-its-budget)

## Exact cancellation before the estimate

Trim \(n<N/L^C\) at arbitrary logarithmic savings by fixed divisor moments, with \(C\) fixed sufficiently large. Here the integer endpoints \(n\) determine \(m\), and each expanded weight and its multiplicity are bounded by fixed powers of \(\tau(n)\tau(N-n)\) and \(L\). Cauchy–Schwarz gives the saving after increasing \(C\). On the remaining support \(u\ge N^{37/80}/L^{C/2}>N^{1/5}\) whenever its ratio is admitted.

For fixed \(ab=r/p\), set \(X=\log(a/(wb))\). The two placements of \(p\) give \(u=pa,\ s=b\) or \(u=a,\ s=pb\). Their signs are \(-\mu(h)\mu(a)\) and \(+\mu(h)\mu(a)\), with the same positive weight \(\log(h/q)\log\ell\log w/\log d\). The short-cofactor test is common to both. The complete pairs cancel and the exact surviving indicator is
\[
 \mu(h)\mu(a)
 \left(\mathbf1_{(B-\log p,B+\log p]}(X)
             -\mathbf1_{[A-\log p,A+\log p)}(X)\right).
\tag{2}
\]
The lower edge has \(p\) in \(u\) and \(A\le\rho<A+2\log p\). The upper edge has \(p\) in \(s\) and \(B-2\log p<\rho\le B\). All enlargements below are applied to the nonnegative upper bound after (2). [Pinned first-prime edge proof](https://github.com/Sodelin/Research-Commons/blob/56abc20768f148741e0fb57b8c4fe82ec0ebb4a8/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-least-prime-edges-2246z.md)

## The auxiliary square at level \(Y^3\)

Put \(M=\ell wpb\), so \(a=(N-qh)/M\). On either surviving edge \(M\le N^{43/80+\beta}\), using \(\ell v\le N^{43/80}\) and at most one extra factor \(p\), where \(v=ws\). For the \(Y\)-rough \(a\) use an auxiliary upper Selberg square with indices at most \(D=Y^3\) and primes at most \(Y\), omitting \(2\) and \(p\). This is an upper count on the surviving edges and uses the original \(W_N(n)=1\). Each other prime of \(M\) exceeds \(Y\).

For a squarefree least common multiple \(e\) of two auxiliary indices, \(e\mid a\) is the unit congruence \(qh\equiv N\bmod Me\). Count it directly at the full odd modulus \(Me\), continuing to require odd \(q,h\). In a rectangle of side lengths at most \(H\) its main term is the area times \(\varphi(Me)/(4(Me)^2)\) and its error is
\[
 (Me)^{1/2+o(1)}+H(Me)^{-1/2+o(1)} .
\]
Indeed completing the two odd progressions gives Kloosterman sums with the same unit modulus. The two nonzero Fourier indices give the first bound by the Fourier interval norm over multiples of each divisor of the modulus. A single zero index contributes the second bound. Rounding the count of odd integers to half the interval length is covered by the same error. Approximate the positive ordered \(\log(h/q)\) weight from above by a grid of spacing \(H/L\). Its integral divided by \(N\) is \(J+o(1)\), \(J=3/8-\log2/2\). The grid has only logarithmically many rectangles per side. [Pinned rectangular completion at an odd composite modulus](https://github.com/Sodelin/Research-Commons/blob/36624845444790787f442157309e7f9ba6644ad0/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-powers-two-margin-and-odd-semiprime-budget.md#a-direct-charge-on-the-original-odd-semiprime-row)

The optimal Selberg coefficients have magnitude at most one. Across \(d_1,d_2\le D\), the sums of \([d_1,d_2]^{1/2}\) and \([d_1,d_2]^{-1/2}\) are \(O(D^3)\) and \(O(D)\), respectively. For the latter use \(d_1=gj,\ d_2=gk\) and sum \(g^{-1/2}(jk)^{-1/2}\) over \(j,k\le D/g\). Thus the error at fixed \(M\) is \(N^{o(1)}(D^3\sqrt M+HD/\sqrt M)\). The choices of \(\ell,w,p,b\) per \(M\) are \(N^{o(1)}\). Summing over \(M\le N^{43/80+\beta}\) gives powers
\[
 \tfrac32(43/80+\beta)+9\beta=729/800,\qquad
 \tfrac12+\tfrac12(43/80+\beta)+3\beta=643/800.
\]
These cover all grids, log weights and arithmetic divisor choices with room below one.

The local density at an allowed odd prime \(j\) is \(g(j)=(j-1)/j^2\), since \(j\nmid M\). Write \(b_0(j)=g(j)/(1-g(j))\) and extend \(b_0\) multiplicatively to odd squarefree integers. The all-odd harmonic denominator has
\[
 \sum_{d\le X} b_0(d)=C_0\log X+O(1),\qquad
 C_0=(2\Pi)^{-1},\qquad \Pi=\prod_{j>2,\ j\ {\rm prime}}\left(1+\frac1{j(j-1)}\right).
\]
The statement follows by convolution with \(1/d\). The local factors of the remaining kernel are \(1+(b_0(j)-1/j)j^{-s}-b_0(j)j^{-1}j^{-2s}\) at odd primes in its Dirichlet series and \(1-2^{-1}2^{-s}\) at 2. Their absolute log moment converges, and the product at \(s=0\) is \(C_0\). At \(D=Y^3\) exact inclusion–exclusion for primes greater than \(Y\) uses at most two such primes. By the prime harmonic sum on the scaled exponents \([1,3]\) the restricted denominator is
\[
 C_0\log Y\left(\Phi_3+o(1)\right),\qquad
 \Phi_3=5-3\log3+
 \frac12\int_{\substack{x,y\ge1\\x+y\le3}}
                        \frac{3-x-y}{xy}\,dx\,dy.
\]
Here the one-prime term is \(\int_1^3(3-x)\,dx/x=3\log3-2\). Coprimality corrections change the sum by \(O(\log Y\sum_{j>Y}j^{-2})\). The two-prime diagonal has the same negligible order. Bounding \(xy\le (x+y)^2/4\) in the double integral gives \(\Phi_3\ge1+10\log(3/2)-3\log3>7/4\). Omitting \(p\) changes the denominator by a relative \(O(1/p)\), uniformly because \(p>N^{t_*}\). The optimal auxiliary quadratic form is the reciprocal of this denominator. This makes the nonnegative main count for \(\log(h/q)\) at each \(M\) at most
\[
 N(J+o(1))\frac{\varphi(M)}{4M^2}
        \frac{2\Pi+o(1)}{(7/4)\beta L}.
\tag{3}
\]
The \(1/4\) is the odd progression density. The usual optimal-square construction follows by diagonalizing at squarefree divisors. [Pinned Selberg diagonal identity and coefficient bound](https://github.com/Sodelin/Research-Commons/blob/290227d6b4b2b5e69e39b241332620885c661ced/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-selberg-ratio-strips-2158z.md#the-weight-and-its-elementary-quadratic-identity)

## Summing the main term and the same-target budget

Fix \(x=\log\ell/L\). The base cutoff forces \(\log w/L>13/40-x\). Since \(v^2=n e^{-\rho}/\ell\), the two edges respectively have
\[
 b\le N^{3/20+x/2},\qquad b\le N^{1/8+x/2}.
\]
For the second, the increase \(2\log p\) in the allowed ratio width offsets the factor \(p\mid s\). At fixed \(\ell,p,b\) and edge, \(2\log w=\log n-\log\ell-\rho-2\log b-2\log p\cdot\mathbf1_{p\mid s}\). The possible \(w\)'s therefore lie in a log interval of width at most \(\log p+O(\log L)\). Their \(\sum_w(\log w)/w\) is at most \((1+o(1))\log p\), uniformly since \(t>t_*\). On the trimmed support \(\log d\ge (1-x)L-O(\log L)\).

For squarefree \(Y\)-rough \(b\le N^c\), the sum of \(1/b\) is \(\mathcal H(c/\beta)+o(1)\), with \(\mathcal H(u)\le(4/7)(u+1)\) for \(u\ge1\). The fixed positive exponent \(\beta\) and the compact range of \(c(x)\) give uniformity. Using (3), \(\varphi(M)/M^2\le1/M\), the two cofactor bounds, and the external factor of two gives
\[
 \frac{2\mathcal D_1}{N}\ \le\
 J\Pi\,\frac{16}{49}\,
 \frac{\beta-t_*}{\beta^2}
 \int_{1/10}^{1/8}\frac{11/40+x+2\beta}{1-x}\,dx+o(1).
\]
In this expression \(\sum_{N^{t_*}<p\le N^\beta}(\log p)/(Lp)=\beta-t_*+o(1)\). The \(\ell\)-sum uses the same prime harmonic measure. The integral is \((259/200)\log(36/35)-1/40\). The elementary enclosures \(J<57/2000,\ \Pi<13/10\) and \(\log(36/35)\le 2v+2v^3/(3(1-v^2))\) for \(v=1/71\) give the rational upper coefficient \(7231730130339/522067437500000<1/72\). For \(\Pi\), multiply the exact Euler factors through 499 and bound the tail by \(499/498\), using \(\sum_{j>499}1/(j(j-1))=1/499\) over all integers. This proves (1), with strict slack for the fixed-target errors. [Rough-factor harmonic bound](https://github.com/Sodelin/Research-Commons/blob/bc292106d03065e910b8dc6d2bbca1589313169b/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-type-ii-rough-harmonic-cap.md#the-harmonic-mass-of-a-rough-factor)

Write \(\mathcal D_{\ge2}\) for the remaining groups with \(p_2\le N^{1/100}\), still after the two gap cuts. The original budget can now use the sufficient inequality
\[
 2\mathcal D_{\ge2}(N)+\frac{209N}{3600}
     \le M_0(N)+E_{\rm other}(N)-\eta N
\]
for some fixed \(\eta>0\) at all sufficiently large powers of two. The new coefficient is \(53/1200+1/72\). The original other signed rows still need their joint lower estimate, and the \(N/72\) loss is a linear charge.

## Why the second-prime switch can reinforce a surviving sign

At fixed placements of all primes beyond \(p,P\), the \(X\) in (2) with \(P\) in \(u\) exceeds that with \(P\) in \(s\) by \(2\log P>2\log p\). Both surviving placements therefore require the first baseline to be in the lower edge interval and the second in the upper edge interval. The necessary range is \(N^{1/40}/p<P\le pN^{1/40}\), with the left inequality strict from the sides of (2). Then both \(P\) and \(p\) change sides, so the two surviving allocations carry the same Möbius sign and equal weights. The second switch alone supplies no extra cancellation.

A finite group at \(N=2^{159}\) has \(q=532699295177559327436333,\ h=840650282696807071695527,\ \ell=61151,\ w=58792437043\), and
\[
 r=3\cdot17\cdot12687302693074505426149\cdot121625671 .
\]
Its accepted \(u\)'s are exactly \(3a,17a\), \(a=12687302693074505426149\) prime. One lies on each surviving edge and both have negative sign, for a grouped weight of approximately \(-2.538293\) before doubling. Recursive prime certificates and all 16 allocations were checked. The half-open band and its signs were also checked on 1,461 rational placements at and between ratio boundaries. The \(N/72\) inequality is a hand proof with exact rational checks. Independent review is pending and Lean formalization remains open.

The next signed estimate concerns the branch \(p_2\le N^{1/100}<p_3\le N^{f_2(\log p_2/L)}\), with the original short-cofactor selection and both earlier gap exclusions retained. The combined fixed-target lower bound remains open.
