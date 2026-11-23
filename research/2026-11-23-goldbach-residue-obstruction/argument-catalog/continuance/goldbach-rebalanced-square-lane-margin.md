# The model margin at powers of two for the fixed rebalanced Goldbach budget

Keep the prime-tested band and the alternative expansion with \(U=N^{1/100}\), \(V=N^{1/5}\), Selberg level \(N^{23/500}\), support \(z=N^{17/5000}\), and base \(\ell w>N^{13/40}\). At powers of two the doubled stress-strip negative charge is at most \(71N/1000\). The model margin, evaluated at the same targets, is at least \(33N/100\) for all sufficiently large \(N=2^k\). This recomputes the model part of the margin. The other signed rows still need a joint lower bound. [Pinned fixed expansion](https://github.com/Sodelin/Research-Commons/commit/3894f49a36cb7cc752bdf1002b8f465253d3fafe) · [Pinned \(71N/1000\) charge](https://github.com/Sodelin/Research-Commons/commit/483ffd44dc87b1ca58b1b22c9a721f242699ebfe)

## All odd square-divisibility lanes

The pointwise comparison uses
\[
 M_0(N)=\mathfrak S(N)\left(N-\sum_{n<N}\Lambda(n)\mu(N-n)\right).
\]
The model depends on \(N\) and the fixed moving-prefix comparison. The Vaughan and square parameters enter after this comparison in the exact prime-tested actual row. In particular changing that expansion leaves the model formula intact. [Pinned model and residual normalization](https://github.com/Sodelin/Research-Commons/blob/1686bc4d17e561da53ef5f0f312f0c9fa9dfc021/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/2026-11-23-cofactor-cells-1718z/README.md#gb-prefix-residual--missing-estimate) · [Moving-cutoff correction](https://zenodo.org/records/21939906)

Let \(\mathcal P_R\) be the odd primes at most a fixed \(R\). For \(N=2^k\), \(N\bmod p^2\) is a reduced residue for every \(p\in\mathcal P_R\). On the prime side the joint CRT distribution among the reduced residues modulo \(\prod_{p\in\mathcal P_R}p^2\) gives log-weighted mass
\[
 \left(1-\prod_{p\in\mathcal P_R}(1-1/[p(p-1)])+o_R(1)\right)N
 \tag{1}
\]
to the union of lanes \(n\equiv N\bmod p^2\) for at least one such prime. This uses the prime number theorem in finitely many progressions and the error is uniform in the residue \(N\) at the fixed modulus. Prime powers of exponent at least two have total \(\Lambda\)-mass \(O(\sqrt N)\) by Chebyshev and do not change (1).

The tail outside these finitely many lanes costs \(O(N/R)+o(N)\). For \(R<p\le N^{1/4}\), Brun–Titchmarsh in the reduced class modulo \(p^2\) divided by \(\log(N/p^2)\ge L/2\) gives weighted prime mass \(O(N/[p(p-1)])\), with \(L=\log N\). Sum this bound over \(p>R\). For \(p>N^{1/4}\), the number of possible \(n<N\) with \(p^2\mid N-n\) is at most \(N/p^2\), so the weighted total in that range is \(O(N^{3/4}L)\). For \(k\ge2\) the lane \(4\mid N-n\) is supported only on powers of \(2\) among nonzero \(\Lambda(n)\), of total weight \(O(L)\). Consequently the full nonsquarefree-shift mass at powers of two is
\[
 \sum_{\substack{n<N\\ \mu(N-n)=0}}\Lambda(n)
   =\left(1-\prod_{p>2}(1-1/[p(p-1)])+o(1)\right)N .
 \tag{2}
\]
This is a pointwise limit, by first taking \(k\) large and then \(R\) large. [Brun–Titchmarsh, Montgomery–Vaughan](https://doi.org/10.1112/S0025579300004708)

Using \(\mu(N-n)\le1\) off these lanes and \(\sum_{n<N}\Lambda(n)=N+o(N)\), we obtain
\[
 \frac{M_0(2^k)}{2^k}
 \ \ge\ \left(2\prod_{p>2}\bigl(1-(p-1)^{-2}\bigr)\right)
           \left(1-\prod_{p>2}\bigl(1-[p(p-1)]^{-1}\bigr)\right)+o(1).
 \tag{3}
\]
Only the first factor is the usual singular series at \(2^k\). This estimates the original model margin without needing the sign distribution on the squarefree shifts.

For a rational certificate use odd primes through \(211\). The tail in the first product is at least \(1-1/210\), by \(\prod(1-a_p)\ge1-\sum a_p\) and comparison with \(\sum_{j\ge211}j^{-2}\). Dropping the tail in the second product gives a lower bound for its complement. The resulting first factor is greater than \(1314/1000\), and the resulting second is greater than \(2515/10000\). Their product is greater than \(33/100\). The finite inequalities can be checked with the following exact arithmetic.
 
    from fractions import Fraction as F
    from math import isqrt, prod
    p = [n for n in range(3, 212, 2)
         if all(n % d for d in range(2, isqrt(n) + 1))]
    s = 2 * (1 - F(1, 210)) * prod(1 - F(1, (q - 1)**2) for q in p)
    a = 1 - prod(1 - F(1, q*(q - 1)) for q in p)
    assert s > F(1314, 1000) and a > F(2515, 10000)
    assert F(1314, 1000) * F(2515, 10000) > F(33, 100)

## The precise residual allowance

Write \(E_{\mathrm{other,new}}(N)\) for the exact pointwise signed remainder after removing the doubled stress-strip term in the selected rebalanced expansion. It includes the unchanged low and outer rows, the remaining actual center, and both complementary ratio ranges of the same expanded Type II row. Charged \(o(N)\) terms stay outside the budget. With this normalization,
\[
 R_\Lambda(2^k)\ \ge\
 \frac{259}{1000}N+E_{\mathrm{other,new}}(N)+o(N)
 \qquad(N=2^k),
 \tag{4}
\]
where \(R_\Lambda\) is the \(\Lambda\)-weighted Goldbach count and the bound uses the pinned pointwise comparison. Thus a sufficient remaining inequality, for every sufficiently large \(k\), is
\[
 E_{\mathrm{other,new}}(2^k)\ \ge\
       -\bigl(259/1000-\eta\bigr)2^k
 \quad\text{for some fixed }\eta>0 .
\]
Proper prime powers have \(o(N)\) contribution to \(R_\Lambda\) at this scale. Equation (4) leaves the joint lower bound on the other rows open. The main margin proof is a hand argument. The finite inequality is checked separately in rational arithmetic. [Pinned original endpoint-parity budget](https://github.com/Sodelin/Research-Commons/blob/971db7d7f546d4d7fa6865089287f7f97ca085eb/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/determinant-20-over-19-ledger-reply.md#exact-center-after-both-rough-factor-charges)

The audit of the other rows proves a sharper combined budget. The complete original odd-block semiprime contribution, including the rebalanced strip and both complements, has doubled absolute charge below \(0.098N\). The remaining exact pointwise condition is therefore a joint lower bound of \(-\bigl(0.232-\eta\bigr)N\) on the centered low row, the actual outer interiors, the even-block semiprimes and the even-endpoint center with four or more factors, for some fixed \(\eta>0\). The separate Type II charges are already included in the full odd-semiprime charge. [Pinned complete ledger and direct count](https://github.com/Sodelin/Research-Commons/commit/36624845444790787f442157309e7f9ba6644ad0) · [Pinned individual ratios](https://github.com/Sodelin/Research-Commons/commit/c464e64722382a25eddbff67af0c017a8684eda9)

