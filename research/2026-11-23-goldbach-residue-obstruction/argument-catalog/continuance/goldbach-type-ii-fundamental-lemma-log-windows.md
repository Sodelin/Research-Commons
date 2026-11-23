# A two-sided sieve for rough Type I masks and wider Type II windows

This is a hand deduction at each even target \(N\). Keep the exact typical semiprime band and count masks of the pinned Vaughan reduction. Thus \(H=\sqrt N\), \(L=\log N\), \(q,h\in(H/2,H]\) are ordered, \(m=qh\) is squarefree with \((m,N)=1\), \(n=N-m=\ell d\), \(\ell\) is prime in \((N^{1/10},N^{1/8}]\), and \(d>D_0=H^{20/19-\delta_0}\) for fixed \(0<\delta_0<1/19\) is the original strict cutoff. Keep the original projector \(F(m)\) and the allowed endpoint cutoff. Take \(U=N^{u_0},V=N^{v_0}\) with \(u_0,v_0>0\), \(u_0+v_0<61/152\), and choose fixed \(\omega\in(1/2,10/19)\) with \(N^{1/8}UV<P=N^\omega\). Put \(z=Y_*=\exp(L/f)\) with \(f=f(N)\to\infty\) and \(f\le\log L\). [Pinned signed Vaughan reduction](https://github.com/Sodelin/Research-Commons/blob/8e0260adeb1507379110f428ad925065c64fae51/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-semiprime-type-i-2121z.md).

Keep \(n\) squarefree and \(z\)-rough before replacing the prime test on \(d\) by \(\Lambda(d)/\log d\). Both endpoint conditions hold on the prime-tested support for large \(N\), and squarefreeness excludes any proper prime powers in the replacement. Apply Vaughan's identity with those masks retained. The Type I sums on this support are \(o(N)\). Consequently the original prime-tested sum is, up to \(o(N)\), its ordered Type II term with the same \(n\) masks and exact weight
\[
 qh+\ell uv=N,\qquad
 \tfrac12 F(m)\mu(h)\mu(u)B_V(v)\log(h/q)\frac{\log\ell}{\log(uv)}.
\tag{1}
\]
In particular \(u,v\) are \(z\)-rough. This equivalence is obtained by proving Type I cancellation on the retained support.

## Two-sided substitution in Type I

The pinned small-endpoint trim permits \(n\ge N/L^B\) with error \(O_A(N/L^A)\) for sufficiently large fixed \(B\). In each Type I term, keep roughness and drop squarefreeness by charging the \(O(N/z)\) endpoints divisible by \(p^2\) for some \(p>z\). Fixed divisor moments absorb both errors. Group \(n=rs\) as in the pinned proof, with \(r=\ell u\) in the first term and \(r=\ell u w\) in the second. Then \(r\le P\), \((r,N)=1\), and roughness is the conjunction of the separate masks on \(r,s\). Keep the \(r\) mask in its arithmetic coefficient.

Use the two-sided fundamental lemma at level \(D_{\rm I}=N^\rho\), with small fixed \(\rho>0\) chosen below. It gives weights \(\lambda_b^\pm\) supported on squarefree \(b\le D_{\rm I}\) with prime factors at most \(z\), of magnitude at most one, such that \(\Lambda^-(s)\le\mathbf1_{s\ z\text{-rough}}\le\Lambda^+(s)\), where \(\Lambda^\pm(s)=\sum_{b\mid s}\lambda_b^\pm\). At fixed \(r\), since \(r\) is \(z\)-rough, the divisibility test \(b\mid s=(N-qh)/r\) is disjoint from the base modulus. Its bad density is \(g(p)=(p-1)/p^2\) for \(p\nmid N\) and \(g(p)=(2p-1)/p^2\) for \(p\mid N\). They satisfy the sieve dimension condition uniformly. In fact \(g(p)\le\min(2/p,3/4)\), and Mertens' estimate bounds \(\prod_{w\le p\le z}(1-g(p))^{-1}\) by \((\log z/\log w)^2(1+C/\log w)\) for \(2\le w\le z\) and an absolute \(C\). At depth \(t_I=\rho f\), the two sieve main terms differ by \(O(V(z)e^{-c\rho f\log f})\), where \(V(z)=\prod_{p\le z}(1-g(p))\ll1/\log z\) and \(c>0\) is fixed. [Two-sided fundamental lemma, Theorem 3.6(a)](https://ford126.web.illinois.edu/sieve2023.pdf).

The error of substituting \(\Lambda^+(s)\) for the roughness indicator is bounded in absolute value by the nonnegative difference \(\Lambda^+(s)-\Lambda^-(s)\) times the absolute coefficient. Drop the \(q,h\) masks in this positive upper bound. For fixed \(r,b\), the CRT count on the full \(q,h\) rectangle has main term \(H^2\varphi(r)/(4r^2)\prod_{p\mid b}g(p)\). The bad residue pairs modulo \(b\) number at most \(2^{\omega(b)}b\). On each pair use the fixed-rectangle unit hyperbola modulo \(r\), giving error \(O(r^{1/2+o(1)}(1+H/r))\), including rounding. The sum over \(b\le D_{\rm I}\) costs \(N^{2\rho+o(1)}\). This count and error also cover the possible endpoint \(qh=N\) by deleting that single pair. [Pinned fixed-modulus count](https://github.com/Sodelin/Research-Commons/blob/909738e51f1ea4abe94c119276375481f85abc56/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-type-ii-balanced-two-prime-sieve.md) · [Fixed-rectangle completion, equation (10)](https://arxiv.org/pdf/1103.2879).

The effective nonnegative coefficient \(C_i(r)\) for this error satisfies \(\sum_r C_i(r)/r\ll L f\) in each Type I term. For the first term, use \(\log s/\log d\le1\), leaving \(\log\ell\) and the reciprocal weights of \(\ell,u\). For the second use \(\log d\gg L\), leaving \(\log\ell\,\Lambda(w)/L\). At each fixed \(\ell,u\), summing \(\Lambda(w)/w\) over the allowed rough \(w\le V\) costs \(O(L)\) by the Chebyshev bound; restricting \(w\) further can only decrease it. In both terms \(\sum_{\ell}\log\ell/\ell\ll L\) and the reciprocal mass of rough \(u\le N\) is \(O(L/\log z)=O(f)\). Each individual \(C_i(r)\) is polylogarithmic, since at most five eligible primes \(\ell\) divide \(r\) and \(\sum_{w\mid r/\ell}\Lambda(w)=\log(r/\ell)\). It follows that the total Type I substitution error is
\[
 O\!\left(N f^2 e^{-c\rho f\log f}
          +N^{3\omega/2+2\rho+o(1)}\right)=o(N)
\tag{2}
\]
when \(\rho\) is small enough. This bound uses the original Type I weights before separating \(1/\log d\) by the pinned integral.

## Determinant with polynomial sieve periods

For the signed upper-weight approximation, separate the logarithmic denominator by the same integral and smooth the usual rectangle edges. These changes have the pinned errors, since \(|\Lambda^+(s)|\le\tau(s)\). The period for the existing \(q\) masks is \(a=N^{o(1)}\), with \(N^{o(1)}\) choices and coefficients. A sieve period \(b\mid s\) is now at most \(N^\rho\), with coefficient of magnitude at most one. For fixed periods the determinant is \((ah)q'+(br)s'=N\). The exact conditions \((h,N)=(r,N)=1\) force \((h,b)=(a,r)=(h,r)=1\) on solutions. Thus \(g=(ah,br)=(a,b)\mid N\), and the reduced progression is a single residue class. Its zero frequency carries \(g/(ab)=1/[a,b]\). Summing the absolute mask coefficients with this denominator is polylogarithmic, since each nonempty local pattern pays at least \(1/p\) and the local coefficients and number of patterns are bounded. The \(h\)-prefix cancellation is unchanged, with coprimality parameter \(rNb\) of polynomial size and the same residual divisibility restriction. [Pinned two-period masks and zero mode](https://github.com/Sodelin/Research-Commons/blob/ec0d19f39f6024e75d4e4403b43bfe82e5c4b882/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/determinant-asymmetric-range.md).

Write \(R,S\) for the dyadic scales of \(r,s\). On retained boxes \(RS\gg N/L^B\), all geometry and smooth derivative losses here are polylogarithmic. For \(R\le H\), the sparse norms cost \((HR)^{1/2}\) up to logs. In Bettin–Chandee Corollary 1 the two arithmetic scales are \(aH/g,bR/g\). Dropping denominator powers of \(g\), this gives
\[
 (HR)^{17/20}(H+R)^{1/4}(ab)^{7/20}\max(a,b)^{1/4}
 \le H^{39/20}b^{3/5}N^{o(1)}.
\]
Summing the \(b\)'s gives the exponent \(39/40+(8/5)\rho\) in \(N\). For \(R\ge H\), use the pinned grouped Poisson frequencies in Theorem 1. Their scale is \(A_0=abR/(gH)\). At that scale the factor from the Poisson amplitude and the mode norm is \(A_0^{-1/2}\). With the same sparse norms, the two terms give
\[
 HR^{19/20}(ab)^{1/5}\max(a,b)^{1/4}g^{-4/5},
 \qquad H^{7/8}R(ab)^{3/8}\max(a,b)^{1/8}g^{-7/8}.
\]
The dyadic mode tails decay by the pinned integrations by parts. Summing these bounds over \(b\) gives exponents
\[
 \tfrac12+\tfrac{19}{20}\omega+\tfrac{29}{20}\rho,
 \qquad
 \tfrac7{16}+\omega+\tfrac32\rho.
\]
These exponents have an arbitrarily small extra fixed loss from the analytic estimates. Choose \(\rho>0\) so that all three displayed exponents and \(3\omega/2+2\rho\) in (2) are strictly below one, then take that extra loss smaller than the resulting fixed slack. This is possible since \(\omega<10/19\). The two signed Type I approximations are therefore negligible, and (2) proves the stated Type I claim for the exact rough masks. [Bettin–Chandee, Theorem 1 and Corollary 1](https://arxiv.org/pdf/1502.00769v1) · [Pinned grouped-frequency and period factors](https://github.com/Sodelin/Research-Commons/blob/9a77141e26f67c56ec8c61102ce6516f5ed24f12/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/determinant-joint-frequency-cutoff.md).

## Full prime band with ratio intervals of width \(o(L)\)

In (1), keep the entire prime \(\ell\) band. For each \(\ell\) and each dyadic endpoint band \(N2^{-j-1}<n\le N2^{-j}\), permit an arbitrary interval in \(\log(u/v)\) of width at most \(\Delta=o(L)\). Use the pinned endpoint rectangle of area \(O(N4^{-j})\). The smaller factor \(x=\min(u,v)\) has an allowed log interval of width \(O(1+\Delta)\) since \(\log(uv)\) varies by at most \(\log2\) in that cell. At fixed \(\ell,x\), the larger factor is fixed by \(qh\) and can be sieved for \(z\)-roughness at modulus \(M=\ell x\le\sqrt{N\ell}\le N^{9/16}\). [Pinned dyadic endpoint and ratio boxes](https://github.com/Sodelin/Research-Commons/blob/81656bc6da1e055db375a2ab4659e05b310b37a1/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-type-ii-rough-log-boxes.md).

Here use a separate upper sieve level \(D_{\rm II}=N^\eta\) with fixed \(\eta<5/64\), also smaller than half a fixed lower exponent for \(x\). The same fundamental lemma gives a main count \(O(N4^{-j}/(M\log z))\) at fixed modulus and cell and a total absolute lattice error \(N^{27/32+2\eta+o(1)}\) after weights and summing moduli and bands. The one-dimensional sieve for rough \(x\) on each polynomial dyadic scale has floor error \(O(N^\eta)\), absorbed in the scale divided by \(\log z\). Thus the reciprocal mass of the eligible \(x\)'s is at most \(O((1+\Delta)/\log z)\). The exact weight in (1) has magnitude \(O(\log\ell)\), and \(\sum_{\ell\ \mathrm{prime}}\log\ell/\ell\ll L\). Summing the geometric area weights gives the absolute main bound
\[
 O\!\left(\frac{NL(1+\Delta)}{(\log z)^2}\right)
 =O\!\left(N f^2\frac{1+\Delta}{L}\right).
\]
For a prescribed width bound \(\Delta=o(L)\), choose \(f=\min\{\log L,(L/(1+\Delta))^{1/4}\}\). It tends to infinity, the main bound is \(o(N)\), and the Type I error (2) is \(o(N)\). The proof controls the stated window in this equivalent retained-rough expansion. It does not bound the unrestricted signed Type II sum or justify summing a partition into windows of total width comparable to \(L\).

For a stricter error budget one can fix \(f=(\log L)/\sqrt{\log\log L}\) for sufficiently large \(N\). Then \(\rho f\log f\) exceeds any fixed multiple of \(\log L\) eventually, so (2), and hence the exact Type I reduction, are \(O_A(N/L^A)\) for every fixed \(A\). At that choice the same absolute Type II bound gives \(o(N)\) for widths \(\Delta=o(L\log\log L/(\log L)^2)\). The adaptive choice above gives the wider \(o(L)\) range with an \(o(N)\) error in the Type I reduction. Both versions preserve the original fixed target and algebraic signs. No numerical or Lean check is used.
