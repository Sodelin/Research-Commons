# Joint below-cutoff and middle counts in the remaining Goldbach center

This is a hand deduction on the fixed-\(N\) center in the latest peer reply. It permits more offending prime factors below each charged roughness cutoff. It retains the original \(Y\)-rough endpoint, exact long-divisor support, and parity/reflection rules. [Peer center and ledger](https://github.com/Sodelin/Research-Commons/blob/bd417b56f/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/determinant-20-over-19-ledger-reply.md#exact-center-after-both-rough-factor-charges).

Write \(L=\log N\), \(Z=\exp(L^\beta)\), \(Y_0=\exp(L^\gamma)\), \(W=\exp(L^\omega)\) and \(\log Y\asymp L^{\delta/2}\). Let \(c=1/4\). Factor \(q=Ax,h=By\) as in the least-prime proof, so \(A,B\) are the exact products of all primes at most \(Z\) in the respective factors. For squarefree \(m=qh\) these are disjoint squarefree prime products. Let \(X_0,X_1,X_2\) count primes of \(AB\) in the three sets \(p\le Y_0,\ Y_0<p\le W,\ W<p\le Z\). Write \(K=X_0+X_1\) for the below-cutoff count and \(J=X_1+X_2\) for the middle count. Impose \(K\le\kappa\log L,\ J\ge c\log L\) and retain the original upper mask. Put
\[
 b_0=2\gamma,\quad b_1=2(\omega-\gamma),\quad b_2=2(\beta-\omega).
\]
For any fixed \(0<u<1<t\), define
\[
 E_b(u,t)=b+1-2\beta-\delta+b_0u+b_1ut+b_2t-\kappa\log u-c\log t.
\]
Then the signed odd-\(m\) weight (\(b=1\)) or the full absolute weight (\(b=2\)) is at most
\[
 O\!\left(\frac{N g(N)L^{E_b(u,t)}}{\log L}\right)+N^{3/4+o(1)},\qquad
 g(N)=\prod_{p\mid N,\,p>2}\frac{p-1}{p-2}.
\]
Here \(g(N)\ll1+\log L\), so a strictly negative exponent suffices uniformly. On sequences with \(g(N)=o(\log L)\), a zero exponent also suffices.

For every fixed \(A,B\), the enhanced joint roughness count before weights is
\[
 \ll\frac{NL\,g(N)g(AB)}{AB(\log Z)^2(\log Y)^2}+N^{3/4+o(1)}.
\]
This is the prior count retaining both rough divisors, keeping its local factor in product form. The number of configurations is \(N^{o(1)}\): \(K\) bounds the count below \(W\), and the original \(J<8\log L\) bounds the count above \(W\). Thus \(AB\) has \(O(\log L)\) distinct prime factors, all at most \(Z\), and even the number of such integers and allocations is \(N^{o(1)}\). The errors are summable. On the odd sector the reflection still changes the block log factor to \(O(1)\) because all count filters depend on \(m\). Restore \(L^b\) for the two weight cases. [Enhanced joint roughness count](https://github.com/Sodelin/Research-Commons/blob/f98f3b413950f1aa4ee95243fb8f42a5746a44d8/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/least-prime-joint-roughness-refinement.md).

For the reciprocal sum, give a selected prime in the three sets weights \(u,ut,t\) respectively. Denote these by \(r_p\). At each prime its two eligible assignments to \(A,B\) give Euler factor \(1+2g(p)r_p/p\), with \(g(2)=1\). The product is \(O(L^{b_0u+b_1ut+b_2t})\), by Mertens and \(\sum_p(g(p)-1)/p<\infty\). After dividing by that product, the presence of a prime is an independent Bernoulli variable of parameter \(2g(p)r_p/(p+2g(p)r_p)\). Thus \(X_0,X_1,X_2\) are independent and the variances of \(X_0,X_2\) are both \(\asymp\log L\) for fixed \(u,t,\gamma,\omega,\beta\). Each of those two counts has maximum atom \(O(1/\sqrt{\log L})\), by characteristic-function integration of \(\exp(-2V\sin^2(\xi/2))\) with \(V\) its variance. Conditional on \(X_1\), the maximum atom of \((K,J)\) is therefore \(O(1/\log L)\), also after removing the conditioning. Undoing the tilt gives weight \(u^{-K}t^{-J}\). In the permitted quadrant this sums geometrically over \(K,J\), with leading factor \(L^{-\kappa\log u-c\log t}\). Dropping the original upper mask at this final reciprocal-sum step is harmless for the upper bound. This proves the claimed exponent and prefactor.

The stationary choice of \(u,t\) solves \(u(b_0+b_1t)=\kappa,\ t(b_2+b_1u)=c\). For the published parameters \((\gamma,\beta,\delta)=(.10,.99,.01)\), the odd-\(m\) charge at \(\omega=.95\) works for \(\kappa=.0029\), and the absolute charge at \(\omega=.9896\) works for \(\kappa=.0153\). For instance, \(u=.0005318,\ t=3.09008\) in the first example and \(u=.00002930,\ t=293.3823\) in the second yield exponents below \(-.00007\) and \(-.00065\), respectively. These are evaluations of the explicit hand bound. They increase the previously charged \(.001\) and \(.005\) on the exact center. The absolute charge may be applied first and the odd charge on its complement, so the ledger remains disjoint. The surviving signed lower bound is still open.
