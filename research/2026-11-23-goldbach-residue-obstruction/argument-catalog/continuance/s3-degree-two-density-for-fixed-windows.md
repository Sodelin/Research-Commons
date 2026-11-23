# Degree-two zero density for fixed logarithmic windows

Let \(L=L(s,\rho)\), where \(\rho\) is the usual irreducible two-dimensional representation of the \(S_3\) closure of a non-Galois cubic field. For every fixed \(b>1/2\) there is \(c_b>0\) such that
\[
 \#\{\rho_L=\beta+i\gamma:\ \beta\ge b,\ |\gamma|\le T\}
 \ll_{L,b} T^{1-c_b}.
\tag{1}
\]
Zeros are counted with multiplicity. In particular \(\sum_{\beta>b}(1+|\gamma|)^{-1}<\infty\). The bound is in the height aspect of one fixed \(L\). It gives the reciprocal sparsity hypothesis of the positive-measure convolution proof, so any off-line case for this Artin factor is detected on every sufficiently late interval of some fixed logarithmic length, independently of attainment of the rightmost abscissa. That length is allowed to depend on the particular detected zero and spectrum. This is a hand proof. It gives no arithmetic upper bound for the original observable.

## Analytic inputs and weights

Artin induction gives \(L\) as an entire primitive finite-order Hecke \(L\)-function of the quadratic subfield. Its self-dual completion is
\[
 \mathcal M(s)L(s),\qquad
 \mathcal M(s)=Q^{s/2}\Gamma_{\mathbb R}(s+\mu_1)\Gamma_{\mathbb R}(s+\mu_2),
 \qquad \mu_1,\mu_2\in\{0,1\}.
\]
The completed functional equation is \(\mathcal M(s)L(s)=\epsilon_L\mathcal M(1-s)L(1-s)\) with \(|\epsilon_L|=1\). Euler parameters have modulus at most \(1\), including at ramified primes. If \(a(n)\) and \(m(n)\) are the coefficients of \(L\) and \(1/L\), respectively, then \(|a(n)|,|m(n)|\ll_\varepsilon n^\varepsilon\). This follows from each local factor having at most two parameters. The completed function has order one, and its zero count with \(|\Im\rho_L-t|\le1\) is \(O_L(\log(3+|t|))\). [Artin's induction formalism](https://doi.org/10.1007/BF02941010) · [Classical Hecke analytic theory](https://sites.math.rutgers.edu/~alexk/2023S572/Tate1950.pdf) · [Local zero counts, Iwaniec–Kowalski Proposition 5.7](https://doi.org/10.1090/coll/053)

Fix \(\sigma_1>1/2\) and \(0<r<\min(1/8,(\sigma_1-1/2)/4)\), and let \(\sigma_1\le\sigma\le1+r\) and \(T\le t\le2T\). The exact smooth approximate functional equation is
\[
 L(s)=\sum_{n\ge1}a(n)n^{-s}V_s(n)
      +\epsilon_L\frac{\mathcal M(1-s)}{\mathcal M(s)}
              \sum_{n\ge1}a(n)n^{s-1} V_{1-s}(n),\qquad
 V_w(y)=\frac{1}{2\pi i}\int_{(3)}
       \frac{\mathcal M(w+z)}{\mathcal M(w)}
       e^{z^2}y^{-z}\frac{dz}{z}.
\]
To get the identity, shift from \(3\) to \(-3\) in the integral for the completed \(L(s+z)\) divided by \(\mathcal M(s)\). The completed function is entire, so only \(z=0\) is crossed. Apply the functional equation on the new line and replace \(z\) by \(-z\). Absolute convergence on both right lines yields the two sums. Stirling's formula gives \(|\mathcal M(1-s)/\mathcal M(s)|\ll_L T^{1-2\sigma}\).

On \(y\asymp Y\), write \(\mathcal V_w(Y)\) for \(\sup |V_w(y)|+\int_Y^{2Y}|V_w'(y)|\,dy\). Stirling on any fixed line \(z=c+iv\) used below gives a bound \(O_{L,c}((T/y)^c)\) for the integral and for its logarithmic \(y\)-derivative. The Gaussian in \(v\) absorbs the polynomial and exponential factors from the gamma quotient. More explicitly, for \(|v|\le T/2\) the quotient is bounded by \(O_{L,c}(T^c e^{C|v|}(1+|v|)^C)\). For \(|v|>T/2\) the denominator costs at most \(\exp(O_L(T))\) times powers of \(T\), and the Gaussian dominates. All these numerator gamma arguments have fixed positive real part on the selected real integration lines, uniformly in the real parts of \(w\). Contour deformation for the weight past \(z=0\) is done only for \(w=s\).

For the first weight use \(c=-1/4\) when \(y\le T\), crossing the residue \(1\) at \(z=0\), and use \(c=A>0\) when \(y>T\). This gives
\[
 V_s(y)=1+O_L((y/T)^{1/4})\quad(y\le T),\qquad
 \mathcal V_s(Y)\ll_{L,A}(1+Y/T)^{-A}.
\]
For the dual weight use \(c=2r\) when \(y\le T\), and \(c=A\) when \(y>T\). The line \(2r\) stays to the right of all numerator gamma poles because \(\Re(1-s)\ge-r\). Thus for each \(A\ge1\)
\[
 \mathcal V_{1-s}(Y)\ll_{L,r,A}
 \begin{cases}
 (T/Y)^{2r},&Y\le T,\\
 (Y/T)^{-A},&Y>T.
 \end{cases}
\]
This permits disks near zeros with \(\beta\) arbitrarily close to \(1\).

## Approximation in mean square

For \(Y\ge1\), the squared \(L^2([T,2T])\) norm of the maximal partial sum of \(\sum_{Y<n\le 2Y} c_n n^{-it}\) is at most
\[
 O\!\left((T+Y)\log^2(2Y)\sum_{Y<n\le2Y}|c_n|^2\right).
\tag{2}
\]
Indeed any initial segment decomposes into at most \(O(\log(2Y))\) dyadic segments. Cauchy–Schwarz bounds it by summing the squares of all segment sums. Montgomery–Vaughan bounds the integral of each segment square by \(O((T+Y)\sum|c_n|^2)\) on that segment. At each scale a coefficient is counted once. Partial summation in \(n\) inserts a weight of dyadic size and total variation \(\mathcal V_w(Y)\), multiplying the \(L^2\) norm by that quantity without differentiating in \(t\). [Montgomery–Vaughan mean-value theorem, Corollary 2](https://doi.org/10.1112/jlms/s2-8.1.73)

Set \(N=T^{1/10}\) and \(A_N(s)=\sum_{n\le N}a(n)n^{-s}\). In the first sum of the approximate functional equation, the terms \(n\le N\) change pointwise by \(O(T^{-1/4}N^{5/4-\sigma+\varepsilon})\) on replacing \(V_s\) by \(1\). For the terms \(n>N\), apply (2) on dyadic intervals and sum the resulting \(L^2\) norms. The squared norm is
\[
 \ll_{L,\sigma_1,\varepsilon}
 T^{1+\varepsilon}N^{1-2\sigma}+T^{2-2\sigma+\varepsilon}.
\]
For \(Y\le T\) the block squared bound before summing is
\((T+Y)Y^{1-2\sigma+\varepsilon}\), and for \(Y>T\) it also has arbitrary power decay in \(Y/T\). The sum of square roots has the same powers up to logarithms, absorbed into \(T^\varepsilon\).

For the dual sum, before multiplication by the gamma ratio, (2) gives squared mean at most \(O_{L,\sigma_1,\varepsilon}(T^{2\sigma+\varepsilon})\). For \(Y\le T\) the block squared bound is \(O((T+Y)Y^{2\sigma-1+\varepsilon}(T/Y)^{4r})\). It is largest near \(Y=T\) because \(2\sigma-1-4r>0\). The terms at \(Y>T\) decay by choosing \(A\) large. The singleton \(n=1\) has squared mean \(O(T^{1+4r})\), at most \(O(T^{2\sigma})\) by the same inequality. Multiplication by the gamma ratio changes the squared mean to \(O(T^{2-2\sigma+\varepsilon})\). Choose \(\varepsilon\) small in terms of \(\sigma_1-1/2\). All bounds together give some \(a_0>0\) such that
\[
 \int_T^{2T}|L(\sigma+it)-A_N(\sigma+it)|^2dt
 \ll_{L,\sigma_1}T^{1-a_0},
\tag{3}
\]
uniformly on \(\sigma_1\le\sigma\le1+r\).

Let \(M_X(s)=\sum_{n\le X}m(n)n^{-s}\), with \(X=T^\eta\) and \(0<\eta<\min(1/10,a_0/8)\). On this strip \(|M_X(s)|\ll_L X^2\). Hence (3) also holds with \(M_X(L-A_N)\) in place of \(L-A_N\) and \(a_0/2\) in place of \(a_0\). In \(A_NM_X-1\) all coefficients through \(X\) vanish by Dirichlet inversion, all later coefficients are \(O_{L,\varepsilon}(n^\varepsilon)\), and the length \(NX\) is below \(T\). The mean-value theorem gives
\[
 \int_T^{2T}|A_N(\sigma+it)M_X(\sigma+it)-1|^2dt
 \ll_{L,\varepsilon}T X^{1-2\sigma+\varepsilon}.
\]
Combining the two bounds yields
\[
 \int_T^{2T}|L(\sigma+it)M_X(\sigma+it)-1|^2dt
 \ll_{L,\sigma_1} T^{1-a_1}
\tag{4}
\]
for some \(a_1>0\). The argument and the same polynomial \(M_X\) work on \(T/2\le t\le3T\) because all preceding bounds use \(t\asymp T\) and an integration interval of length \(O(T)\).

## Zero count and consequence

Given \(b>1/2\), choose \(1/2<\sigma_1<b\) and also require \(r<b-\sigma_1\). At every zero \(\rho_L=\beta+i\gamma\) with \(\beta\ge b\) and \(T\le\gamma\le2T\), the holomorphic function \(LM_X-1\) has value \(-1\). The submean inequality for its squared modulus on the disk of radius \(r\) gives disk integral at least \(\pi r^2\). Every point of the enclosing rectangle belongs to \(O_L(\log T)\) disks by the local zero count, counting multiplicities. Integrate (4) in \(\sigma\) on \([\sigma_1,1+r]\) and add the disk inequalities to prove a zero count \(O_{L,b}(T^{1-a_1}\log T)\) on that height block. Sum dyadic blocks and reflect to negative heights using the real coefficients of the Artin \(L\)-function. This proves (1), for example with \(c_b=a_1/2\).

If \(\beta_*>1/2\), choose any zero at a real part \(\beta_0>1/2\) and maximize its real part at its given ordinate. By (1), all zeros with \(\beta>\beta_0\) have summable reciprocal ordinates. The finite positive support needed for the infinite convolution in the window proof follows. A sparse sequence of fixed-length critical-scale upper windows can therefore exclude off-line zeros provided the tested lengths eventually exceed the particular spectral length. An arbitrarily slowly diverging tested length suffices for the implication.

More precisely, at square-root weight, the positive-part integral on each interval \([U,V]\) with \(V\to\infty\) and \(V-U\to\infty\) would have log equal to \((\beta_*-1/2)V+o(V)\) in the off-line case. For each fixed target zero with \(\Re\rho_L=\beta_0>1/2\), put the fixed-support filter in the terminal interval \([V-L_0,V]\) and obtain the lower rate \(\beta_0-1/2\). Then take \(\beta_0\) to \(\beta_*\) after taking the limit over windows, and use the original envelope for the upper rate. If GRH holds, the square-root upper integral is \(O(V-U)\) by the explicit formula. The proof gives no field-discriminant uniformity for the needed fixed length, which depends also on the selected zero, its residue, and its neighboring ordinates. No new Lean verification or numerical zero check is used. [Pinned positive-filter proof and criterion](https://github.com/Sodelin/Research-Commons/commit/7a2d2c5d790118523c794119cc9d69237c787fd2)
