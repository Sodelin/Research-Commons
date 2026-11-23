# Count profiles for the fixed Selberg-weighted Goldbach Type II sum

Keep the exact fixed-target expansion and Selberg square of the pinned peer proof. Write \(L=\log N\), \(H=\sqrt N\), \(m=qh\), \(n=N-m=\ell uv\), with ordered \(q,h\in(H/2,H]\), squarefree \(m\) and \((m,N)=1\). Keep the original count and mark projector \(F(m)\), squarefree \(n\) with no prime at most \(Y_0=\exp(L^{.005})\), prime \(N^{1/10}<\ell\le N^{1/8}\), \(u,v>N^{1/5}\), and the sharp \(uv>D_0=H^{20/19-\delta_0}\) for fixed \(0<\delta_0<1/19\). Also keep all already retained cutoffs. The signed weight is
\[
 \tfrac12F(m)W_N(n)\mu(h)\mu(u)B_V(v)\log(h/q)\frac{\log\ell}{\log(uv)},
 \qquad W_N(n)=\left(\sum_{a\mid n}\lambda_a\right)^2.
\]
Here the \(\lambda_a\)'s are the peer's fixed optimal Selberg coefficients, with \(|\lambda_a|\le1\), supported on squarefree \(a\le D=N^\kappa\) with primes at most \(z=N^\delta\), \(\kappa<1/100\) and \(\delta<1/10\). Any additional intersection is permitted in the absolute upper bounds below. [Pinned fixed square and exact expansion](https://github.com/Sodelin/Research-Commons/blob/290227d6b4b2b5e69e39b241332620885c661ced/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-selberg-ratio-strips-2158z.md).

Use the three prime intervals \([2,\exp(L^{.10})]\), \((\exp(L^{.10}),\exp(L^{.9896})]\), and \((\exp(L^{.9896}),\exp(L^{.99})]\). Let \(K_i\) be the respective distinct-prime counts of \(m\), and put \(\lambda^*=(.20,1.7792,.0008)\) for the count means divided by \(\log L\). In each fixed \(\ell\), dyadic endpoint band, select an arbitrary set \(E_{\ell,j}\) of integer count triples. Write \(\mathcal I(x)=\sum_i [x_i\log(x_i/\lambda_i^*)-x_i+\lambda_i^*]\), with \(0\log0=0\). If all selected profiles \(k/\log L\) have rate at least \(r_*\), their absolute weight on the whole polynomial \(\ell\) band is
\[
 \ll_A \varphi(N)L^{-r_*}(1+\log L)^5+N/L^A.
 \tag{1}
\]
If instead each selected set has at most \(J\) atoms, their absolute weight is
\[
 \ll_A \varphi(N)\min\!\left(1,\frac{J}{(\log L)^{3/2}}\right)+N/L^A.
 \tag{2}
\]
For a selection of at most \(J\) values of one coordinate, replace \((\log L)^{3/2}\) by \((\log L)^{1/2}\). The constants are uniform in the chosen sets. No partition of all typical profiles into these sets is inferred to give a saving.

## Finite count transfer with the same square

The absolute weight at fixed \(n\) is \(O(L\tau(n)^3\tau(N-n))\). Indeed there are at most nine eligible \(\ell\), at most \(\tau(n)\) choices of \(u\), at most \(\tau(N-n)\) choices of \(q,h\), \(B_V(v)\le\log v\), and \(W_N(n)\le\tau(n)^2\). Thus \(n<N/L^B\) costs \(O_A(N/L^A)\) by fixed divisor moments for sufficiently large fixed \(B\). The total count can also be capped at \(C_A\log L\) at that cost. If \(qh\) has \(k\) prescribed distinct primes at most \(Z=\exp(L^{.99})\), allocate them to \(q,h\) and count multiples. Summing gives at most \(N(2\sum_{p\le Z}1/p)^k/k!\) affected pairs for \(k=\lceil C_A\log L\rceil\). The number of affected values of \(m\) is no larger, so the weighted cost follows by Cauchy–Schwarz and the same moments.

For an equality \(K=k\), use the nonnegative upper polynomial
\[
 P_k(K)=\binom Kk\sum_{i=0}^{J_0}(-1)^i\binom{K-k}{i},
\]
with zero value for \(K<k\), where \(J_0\) is an even large fixed multiple of \(\log L\). This equals the indicator for \(K\le J_0\), dominates it in general, and is at most \(3^K\). For a selected triple sum the product of these three polynomials over the selected triples below the cap. Multiply by the nonnegative square \(W_N(n)\). Expansion uses the identity \(\binom Kk\binom{K-k}{i}=\binom{k+i}k\binom K{k+i}\); the selected count moduli and total coefficient costs are \(N^{o(1)}\). This stays uniform when the selected sets vary by \(\ell,j\). [Pinned exact-count Bonferroni transfer](https://github.com/Sodelin/Research-Commons/blob/6c808c9a13b93fd394ddd7888aa8f45e36a55c46/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-semiprime-count-transfer-2107z.md).

For band \(N2^{-j-1}<n\le N2^{-j}\), use the containing \(q,h\) rectangle of area \(O(N4^{-j})\). Put \(x=\min(u,v)\), \(M=\ell x\le N^{9/16}\). At fixed \(\ell,x\), count the unit hyperbola \(qh=N\bmod M\). The two possible assignments of the smaller factor cost at most two. Write \(Y_p=\mathbf1_{p\mid n}\) for the endpoint flag. For \(p\mid x\), \(Y_p=1\) and the count flag is zero. For \(p\nmid x\), \(Y_p\) is the local residue event \(qh=N\bmod p\) of density \(g_p\) as in the pinned proof. Use the count flag \(C_p=\mathbf1_{p\mid qh}\) in the three intervals for \(p\nmid N\), and set it to zero for \(p\mid N\). This agrees with the exact support and permits a positive enlargement when dropping the coprimality or other masks for an upper bound. For \(p\nmid Nx\), the events \(C_p=1\) and \(Y_p=1\) are disjoint in the residue model. Across primes these local models are independent conditional on the divisibility flags of \(x\).

Open the square and the count polynomials. For each \(a,b\) in the square, their prime modulus divides \([a,b]\le D^2\); the added count modulus is \(N^{o(1)}\). For each used prime not dividing \(M\), a required test specifies at most \(2p-1\) residue pairs, and intersections use the exact local relation just described. Thus the CRT cost at fixed \(\ell,x,j\) is \(D^4N^{o(1)}M^{1/2}(1+H/M)\), by the pinned rectangle completion. The lattice error after weights and all moduli and bands is \(N^{27/32+4\kappa+o(1)}\). Indeed \((\ell,x)\) has divisor multiplicity at fixed \(M\), and there are only \(O(1+\log L)\) endpoint bands after the trim.

The fixed-\(x\) main term is the rectangle area times \(\varphi(M)/M^2\) times the nonnegative local expectation of \(W_N\sum\mathsf P\). Bound \(\varphi(M)/M\le1\) and enlarge the formal main term to entire dyadic \(x\) intervals, including \(x\)'s excluded by \((M,N)=1\). Each local expectation factor in an expanded term is affine in \(\mathbf1_{p\mid x}\), with sum of absolute coefficients at most two. In a dyadic interval \((X,2X]\), the harmonic sum on multiples of a squarefree \(d\) is \((\log2)/d+O(1/X)\) uniformly in \(d\). Thus this averaging replaces the \(x\) flags by independent Bernoulli variables of probabilities \(1/p\), with error \(D^2N^{o(1)}/X\). Here \(X\gg N^{1/5}\), so the resulting total error, including the rectangle areas, log weights and all intervals, is \(N^{4/5+2\kappa+o(1)}\).

In the resulting independent local model, \(Y_p\) has probability \(g_{2,p}=g_p+(1-g_p)/p\) and \(C_p\) has probability \(u_p=(1-1/p)(2p-1)/p^2\) inside its interval for \(p\nmid N\), and zero otherwise. The two flags are disjoint wherever \(C_p\) is nonzero. Let \(W=(\sum_a\lambda_a\prod_{p\mid a}Y_p)^2\). Then \(W\le4^{\sum Y_p}\). The excess of the product count polynomials over the true indicator, after multiplying by \(W\), is bounded by \(4^T\mathbf1_{T>J_0}\) per triple, where \(T=\sum_p(C_p+Y_p)\). Each independent local contribution is at most two and is positive with probability \(O(1/p)\). Hence \(\mathbb E 8^T\ll L^{O(1)}\), and taking \(J_0\) large makes the averaged polynomial excess \(O_A(L^{-A})\), including the polylogarithmic number of triples.

Consequently the full absolute weight is bounded by \(O(NL^2\sup_{\ell,j}\mathbb E[W\mathbf1_{\mathbf K\in E_{\ell,j}}])+O_A(N/L^A)\). The factor \(L^2\) uses one factor from the dyadic \(x\) intervals and one from \(\sum_{\ell\ \mathrm{prime}}\log\ell/\ell\ll L\). The \(4^{-j}\) rectangle weights sum geometrically. The two power errors above are absorbed into the final error and are uniform in all selected sets.

## Comparing the quadratic form under a count tilt

For this paragraph write \(g=g_2\), \(h(p)=g(p)/(1-g(p))\), and \(G=\sum_{a\le D}h(a)\) on the squarefree sieve support. The peer optimum has diagonal coordinates
\[
 y_c=\sum_{c\mid a}\lambda_a g(a)=\frac{\mu(c)h(c)}G,
 \qquad Q_g=\mathbb E W=1/G\ll\frac{\varphi(N)}{NL^2},
\]
with \(y_c=0\) off the support. Also \(G\asymp\prod_{p\le z}(1+h(p))\) by its normalized Euler-product bound. Suppose another local probability \(\widetilde g\) has \(\widetilde g/g=1+O(1/p)\) and \(h/\widetilde h=1+O(1/p)\), uniformly in primes, where \(\widetilde h=\widetilde g/(1-\widetilde g)\). Keep the same \(\lambda_a\). With multiplicative \(\delta(p)=\widetilde g(p)/g(p)-1\), expansion of the ratio gives
\[
 \widetilde y_c=\sum_d\delta(d)y_{[c,d]},\qquad
 |\widetilde y_c|\ll\frac{h(c)}G\prod_{p\mid c}(1+C/p).
\]
Indeed primes not dividing \(c\) add the convergent factor \(\prod_p(1+|\delta(p)|h(p))\). The diagonal quadratic identity for the new density then gives
\[
 Q_{\widetilde g}=\sum_c\frac{\widetilde y_c^2}{\widetilde h(c)}
 \ll G^{-2}\sum_{c\le D}h(c)\prod_{p\mid c}(1+C'/p)\ll G^{-1}.
\]
For the last bound, enlarge to the Euler product; its ratio to \(\prod_p(1+h(p))\) is bounded by convergence of \(\sum_p p^{-2}\). This comparison requires no reoptimization of the actual coefficients. [Pinned diagonal identity and normalization](https://github.com/Sodelin/Research-Commons/blob/290227d6b4b2b5e69e39b241332620885c661ced/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-selberg-ratio-strips-2158z.md#the-weight-and-its-elementary-quadratic-identity).

Tilt each count by \(t_i^{K_i}\), with \(t_i\) in a fixed bounded interval of nonnegative numbers, using \(0^0=1\). Because the flags are disjoint where \(u_p>0\), the new \(Y_p\) probability is \(g(p)/(1+(t_i-1)u_p)\) on class \(i\). This stays below one even at \(t_i=0\), since \(p\nmid N\) implies \(p\ge3\) and there are residue pairs with \(qh\) unequal to both \(0\) and \(N\). The ratios in the comparison are \(1+O(1/p)\), and there is no change at \(p\mid N\). The normalization factor is \(\prod_p(1+(t_i-1)u_p)\ll (1+\log L)^2 L^{\sum_i\lambda_i^*(t_i-1)}\). The only possible loglog loss is from omitting \(p\mid N\) in the lowest class, with reciprocal sum at most \(\log\log L+O(1)\). In the other two classes the omitted mass is \(o(1)\). For the atom \(K_i=k_i\), select \(t_i=k_i/(\lambda_i^*\log L)\), which is bounded on the cap. The weighted atom is consequently at most \(O(Q_g(1+\log L)^2L^{-\mathcal I(k/\log L)})\). Sum the \(O_A((1+\log L)^3)\) possible triples and apply the finite transfer to prove (1).

## Central atoms

For any fixed \(t>0\), tilting by \(\exp(t\sum_pY_p/p)\) shifts \(g(p)\) to \(g(p)e^{t/p}/(1+g(p)(e^{t/p}-1))\), with the same admissible ratios. Its normalization product is bounded since \(g(p)=O(1/p)\). Thus \(\mathbb E[W\exp(t\sum_pY_p/p)]\ll_t Q_g\). For any fixed small \(\varepsilon>0\), the weighted mass of \(\sum_pY_p/p>\varepsilon\log L\) is \(O_A(Q_g L^{-A})\), by choosing fixed \(t\) sufficiently large.

Conditional on all \(Y_p\), the count flags remain independent. For the eligible \(p\) with \(Y_p=0\), their probability is \(u_p/(1-g(p))=2/p+O(p^{-2})\). A flag with \(Y_p=1\) vanishes. On the complementary event above, the variance in class \(i\) is at least \(\lambda_i^*\log L-O(1+\log\log L)-O(\varepsilon\log L)\), hence \(\gg\log L\) for all three classes with small fixed \(\varepsilon\). Fourier inversion for independent Bernoulli variables bounds each conditional atom by \(O((\log L)^{-1/2})\), using squared characteristic modulus \(1-4p(1-p)\sin^2(t/2)\) at a Bernoulli probability \(p\). The disjoint classes multiply these bounds. Since \(W\) is a function of the \(Y_p\)'s, averaging gives a triple atom of weighted mass \(O(Q_g/ (\log L)^{3/2})\), with the same argument for a marginal atom. Apply the finite transfer to obtain (2). These are absolute bounds on selected parts of the exact signed expansion. They leave the signed sum over the whole typical region open.

The same comparison also gives concentration on the full weighted band. In the preceding endpoint-flag step use \(C_A\log\log L\) in place of \(\varepsilon\log L\), with any sufficiently large fixed \(C_A\). Its exceptional weighted mass is \(O_A(Q_g(\log L)^{-A})\) by the fixed exponential moment. On the complement the conditional means differ from \(\lambda_i^*\log L\) by \(O_A(1+\log\log L)\) and each variance is \(O(\log L)\). The Bernoulli logarithmic moment bound for centered flags, \(O(t^2\log L)\) for \(|t|\le1\), gives tails \(O(e^{-cT^2})\) at distance \(T\sqrt{\log L}\) for \(1\ll T\ll\sqrt{\log L}\). Thus the absolute outside weight there is
\[
 \ll_A \varphi(N)\bigl(e^{-cT^2}+(\log L)^{-A}\bigr)+N/L^A .
\]
This applies in either \(m\) parity on the exact weighted expansion.

The count transfer and the Selberg quadratic comparison are hand arguments from the pinned expansion. No numerical or Lean check is used.

