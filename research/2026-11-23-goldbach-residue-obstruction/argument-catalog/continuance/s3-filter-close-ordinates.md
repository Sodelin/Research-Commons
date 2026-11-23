# Fixed windows without pairwise ordinate separation

Let \(F\) be the original normalized smoothed observable for the standard Artin factor of an \(S_3\) cubic field of conductor \(Q\). Fix \(1/2<b<1\) and a zero \(\rho_0=\beta_0+i\gamma_0\) with \(\beta_0\ge b\). Put
\[
 D_0=\sum_{\substack{\Re\rho\ge\beta_0\\0<|\Im\rho|<1}}\frac1{|\Im\rho|}.
\]
For any fixed \(\theta<\beta_0\), every sufficiently late interval \([U,U+L]\) with
\[
 L\ge C_b(1+\log^2(3Q)+D_0)
\]
has
\[
 \int_U^{U+L}F(e^u)_+e^{-\theta u}\,du
 \gg_{\rho_0,F}e^{(\beta_0-\theta)U}.
\tag{1}
\]
For \(|F|\) in place of \(F_+\), the sufficient length is \(C_b(1+\log^2(3Q))\). These support bounds are independent of the height of the selected zero and its separation from neighboring ordinates. The amplitude and onset remain spectral. Any chosen zero at \(\beta_0\ge b\) works, including one with other zeros to its right at the same ordinate.

The analytic input is the absolutely summable smoothed explicit formula
\[
 e^{-\beta_0 u}F(e^u)
 =\sum_\rho c_\rho e^{(\rho-\beta_0)u}+o(1)
\]
with distinct completed zeros, nonzero residues \(c_\rho\) and positive \(c_\rho\) at real zeros of real part at least \(\beta_0\). The \(o(1)\) above refers to the elementary terms. The conductor-uniform density bound gives
\[
 \sum_{\Re\rho\ge\beta_0}(1+|\Im\rho|)^{-1}\ll_b\log^2(3Q).
\]
Zeros with \(\Re\rho<\beta_0\) also give \(o(1)\) as \(u\to\infty\) by dominated convergence in the absolute series. [Hybrid density proof](https://github.com/Sodelin/Research-Commons/commit/227b0c3a9431c7799bc2e850a85f043c69c3cdbd)

## Cancel the distant ordinates with a positive measure

For any \(z=a+it\) with \(t\ne0\), the probability supported at \(0,d_t\) with \(d_t=\pi/|t|\) and weights proportional to \(e^{ad_t},1\) has bilateral transform zero at \(z\). Form a positive convolution \(\nu\) of these factors as follows.

- For the one-sided conclusion, use all exponents \(z=\rho-\beta_0\) with \(\Re\rho\ge\beta_0\) and \(\Im\rho\ne0\). For \(|\Im\rho|\ge1\), the sum of support diameters is \(O_b(\log^2(3Q))\), and the remaining diameters sum to \(\pi D_0\).
- For both conclusions, use exponents \(z=\rho-\beta_0-i\gamma_0\) with \(\Re\rho\ge\beta_0\) and \(|\Im\rho|>2|\gamma_0|+3\). In this range \(1/|\Im\rho-\gamma_0|\ll (1+|\Im\rho|)^{-1}\), so the sum of diameters is \(O_b(\log^2(3Q))\).

Because the diameters sum, the countable convolution exists with compact support, as the law of the sum of independent bounded two-point variables. Its transform vanishes at every prescribed exponent. Let \(\mu\) be \(\nu\) convolved with uniform probability on \([0,1]\). Then \(\mu\) is nonnegative, has density at most \(1\), and satisfies the stated support bounds. In the one-sided case the base average of \(e^{-\beta_0(U+v)}F(e^{U+v})\) with respect to \(\mu(dv)\) is at least \(-o(1)\). Every retained high-real-part term has \(\Im\rho=0\) and positive coefficient.

## Separate the finite cluster inside a unit interval

The remaining modulated exponents
\[
 Z=\{\rho-\beta_0-i\gamma_0:\ \Re\rho\ge\beta_0,\ |\Im\rho|\le2|\gamma_0|+3\}
\]
form a finite set containing \(0\). There exists bounded complex \(\varphi\) on \([0,1]\) such that
\[
 \int_0^1\varphi(v)e^{zv}\,dv=\mathbf 1_{\{z=0\}}\qquad (z\in Z).
\tag{2}
\]
To see this, the functions \(e^{zv}\) for distinct \(z\in Z\) are linearly independent on \([0,1]\) by the derivative Vandermonde at \(0\). Their Gram matrix is positive definite, so solve (2) with \(\varphi\) in the span of their conjugates. The norm \(\|\varphi\|_\infty\) may depend on separation, while the support remains \([0,1]\).

Set \(\eta=\nu*(\varphi(v)\,dv)\). It is a complex measure with \(|\eta|\le\|\varphi\|_\infty\mu\). Its transform is the product of the two transforms and equals \(1\) at \(z=0\). For \(f_U(v)=e^{-\beta_0(U+v)}F(e^{U+v})\), every high-real-part nontarget term disappears in the modulated moment,
\[
 \int f_U(v)e^{-i\gamma_0 v}\,d\eta(v)
 =c_{\rho_0}e^{i\gamma_0U}+o(1).
\]
Terms below \(\beta_0\) again tend to zero by absolute residue summability and \(v\ge0\). Thus \(\int |f_U|\,d\mu\gg_{\rho_0,F}1\) at every sufficiently late \(U\). For the one-sided conclusion, combine this with \(\int f_U\,d\mu\ge-o(1)\) using \(2(f_U)_+=|f_U|+f_U\). The density cap gives (1) on the enclosing interval, and likewise the absolute-value variant.

The arithmetic hypothesis for the absolute variant is stronger because it controls both signs of the original observable. For the one-sided variant, the dependence on \(D_0\) comes from modes with small nonzero ordinate. The elementary function \(e^{\beta u}\cos(\gamma u)\) has positive-part integral zero on arbitrarily late intervals of any prescribed length less than \(\pi/|\gamma|\), despite simple off-line Laplace poles. Thus a one-sided length bound that is uniform for abstract pole data cannot ignore these slow modes. This example concerns abstract Laplace pole data.

## Quantitative signal with no pairwise gap in its onset

There is also a uniform version with a polynomial loss in \(U\). Fix \(b<\beta_0\) with \(b>1/2\), and write \(R=3+|\gamma_0|\). Replace \(\Re\rho\ge\beta_0\) by \(\Re\rho\ge b\) in the construction, including in \(D_0\). Keep the same length bounds. Let \(M=\lceil C R\log(QR)\rceil\) with a large absolute constant, so the finite modulated cluster contains at most \(M\) distinct nodes. Then for every sufficiently large \(U\) and fixed \(\theta<\beta_0\), the absolute lower window, and the corresponding one-sided window with its \(D_0\)-dependent length, are at least
\[
 c_{B,b,M}\,\frac{e^{(\beta_0-\theta)U}}{R^2\log(QR)\,U^M}.
\tag{3}
\]
For the absolute window an onset can be chosen in terms of \(Q,R,B,b,\beta_0-b\), with no spectral separation parameter. The one-sided onset can also depend on \(D_0\).

To make the uniformity explicit, use the original undamped observable for the tempered \(S_3\) Artin factor. Its residues are \(c_\rho=m_\rho g_B(\rho)\), where \(m_\rho\) is the multiplicity and
\[
 g_B(s)=-\frac{1-e^{(s-1)B}}{4s(s-1)}
       =\frac{1}{4s}\int_0^B e^{(s-1)t}\,dt .
\]
The cubic character is nonreal, so the Hecke zero-free region for its cyclic extension has no exceptional zero for this factor. It gives \(1-\beta\gg1/\log(Q(3+|\gamma|))\) and, by the functional equation, \(\beta\gg1/\log(Q(3+|\gamma|))\). The norm factor in the cited zero-free region is comparable to \(Q\) because the base has degree two and the two nontrivial characters have the same conductor. It follows from the original quotient that \(|g_B(\rho_0)|\gg_B (R^2\log(QR))^{-1}\); its integral form has derivative \(O_{B,b}(1)\) for \(b\le\Re s\le1\). For \(|\gamma|\ge1\) the quotient gives \(|g_B(\rho)|\ll_B|\gamma|^{-2}\), and for \(|\gamma|<1\) its integral form gives \(O_B(\log(3Q))\) by the left zero-free region. Thus the local Hecke count gives \(\sum_\rho |c_\rho|\ll_B\log^2(3Q)\). [Thorner–Zaman, Lemma 2.5 and Theorem 3.1](https://msp.org/ant/2019/13-5/ant-v13-n5-s.pdf)

The elementary remainder in the undamped explicit formula is \(O_B(1+u+\log^2(3Q))\) at \(x=e^u\). Indeed on shifting smoothed Perron to \(\Re s=-1/2\), the functional equation gives a logarithmic-derivative bound \(O(\log(Q(3+|t|)))\), and only the kernel point \(s=0\) collides with a trivial zero. The residue there contributes \(O_B(1+u+|L'/L(1)|+\log Q)\) by the same functional equation. To bound \(L'/L(1)\), compare its Hadamard expansion at \(1\) and \(2\). The tail \(|\gamma|>1\) is \(O(\log(3Q))\) by the local count and the \(O(|\gamma|^{-2})\) difference of fractions. The low zeros are \(O(\log(3Q))\) in number and individually contribute \(O(\log(3Q))\) by the right zero-free region. The horizontal contours can tend to infinity through heights at distance \(\gg1/\log(Q(3+|t|))\) from zeros using the local count. The resulting squared-logarithm bound on the logarithmic derivative on those edges is absorbed by the quadratic Perron denominator. [Thorner–Zaman, Lemmas 2.5–2.6](https://msp.org/ant/2019/13-5/ant-v13-n5-s.pdf)

To avoid a norm bound from a nearly singular Gram matrix, construct the signed test afresh at each \(U\). Fix \(q=100M\) and let \(r_k=q^{-k}/U\) for \(0\le k\le M\). In the finite set \(Z=\{\rho-\rho_0:\ \Re\rho\ge b,\ |\Im\rho|\le2|\gamma_0|+3\}\), some annulus \((r_{k+1},r_k]\), \(0\le k<M\), contains no modulus of a nonzero node. The cluster \(\mathcal C\) of nodes with \(|z|\le r_{k+1}\) contains \(0\). Every outside finite node has \(|z|>r_k\ge q^{-M}/U\). Set
\[
 P(z)=\prod_{w\in Z\setminus\mathcal C}(1-z/w),\qquad
 \varphi=P(-\partial_v)\chi,
\]
where \(\chi\) is a fixed smooth bump supported in \((0,1)\) with integral \(1\). Integration by parts gives \(\widehat\varphi(z)=P(z)\widehat\chi(z)\) for the bilateral transform. The test kills every outside finite node exactly, with
\[
 \|\varphi\|_\infty\le C_M U^M,\qquad
 |P(z)-1|\le (1+q^{-1})^M-1<0.02\quad(z\in\mathcal C).
\]
For \(z=\rho-\rho_0\) in the cluster, \(|z|U\le q^{-1}\), so \(e^{zU}\) stays within \(0.02\) of \(1\). The factors \(\widehat\nu(z)\) and \(\widehat\chi(z)\) tend uniformly to \(1\) with bounds depending only on \(M,U,L\). Also \(g_B(\rho)/g_B(\rho_0)=1+O_{B,b}(R^2\log(QR)|z|)\). Thus the cluster contributes \(e^{i\gamma_0 U}g_B(\rho_0)\sum_{\mathcal C}m_\rho\) with relative error at most \(1/4\) when \(U\) exceeds a threshold in these parameters.

The omitted \(\Re\rho<b\) terms and the elementary error in the modulated moment are bounded in absolute value by
\[
 C_M U^M\,O_B\!\left(
 \log^2(3Q)e^{-(\beta_0-b)U}
 +(1+U+L+\log^2(3Q))e^{-\beta_0U}\right).
\]
They are eventually smaller than a fixed fraction of \(|g_B(\rho_0)|\), with onset depending on the stated parameters. Divide the modulated moment by the total-variation comparison \(\|\varphi\|_\infty\mu\) to prove the absolute bound in (3). In the one-sided case the same omitted terms bound the negative part of the base mean without the \(C_MU^M\) factor. Their exponential decay is smaller than the polynomial lower bound, so \(2(f_U)_+=|f_U|+f_U\) proves (3) as well.


There is also a variant with arbitrary fixed log length \(\ell>0\) and the original upper sign. Suppose, for every \(\epsilon>0\), arbitrarily late intervals \([M,2M]\) of starting points have the bound \(\int_u^{u+\ell}F(e^v)_+e^{-v/2}\,dv\le e^{\epsilon u}\) for all starts \(u\) outside a set of measure \(o(M)\). If an off-line zero existed, choose its finite detector length \(L\) from (1) and an integer \(k\) with \(k\ell\ge L\). For each of the finitely many shifts \(j\ell\), \(0\le j<k\), the bad set for \(u+j\ell\) still has measure \(o(M)\). Some \(u\in[M,2M-k\ell]\) therefore has all \(k\) short windows good. Summing their positive-part integrals gives an upper bound \(k e^{\epsilon(u+k\ell)}\) on \([u,u+k\ell]\), contradicting (1) at \(\theta=1/2\) for \(\epsilon<\beta_0-1/2\). This criterion trades the unknown spectral length for an almost-all placement hypothesis.

The filter construction and placement comparison are hand proofs. An arithmetic upper window for the original observable remains open.
