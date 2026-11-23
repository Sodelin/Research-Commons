# Conductor-uniform height density and a filter length for \(S_3\)

Let \(L(s)=L(s,\rho)\) for the standard two-dimensional Artin representation attached to an \(S_3\) cubic field. Write \(Q\) for its arithmetic conductor, the absolute discriminant of the cubic field. Equivalently \(L(s)=L_K(s,\chi)\), where \(K\) is the quadratic resolvent and \(\chi\) is either primitive cubic character of the cyclic cubic closure over \(K\), so \(Q=|D_K|N\mathfrak f_\chi\).

Fix \(1/2<b<1\). For every \(A>(1-b)/(2b-1)\) there is \(c=c(b,A)>0\) such that
\[
 N_\rho(b,T):=\#\{\beta+i\gamma:L(\beta+i\gamma)=0,\ \beta\ge b,\ |\gamma|\le T\}
 \ll_{b,A} T^{1-c}\qquad (T\ge\max(2,Q^A)).
\tag{1}
\]
The constant is uniform in the cubic field, and zeros are counted with multiplicity. In particular
\[
 \sum_{\beta\ge b}\frac1{1+|\gamma|}\ll_b \log^2(3Q).
\tag{2}
\]

## Uniform mollification estimate

The degree-two completed Hecke function is entire of order one, with conductor \(Q\) and two \(\Gamma_{\mathbb R}\) shifts in \(\{0,1\}\). At all finite primes the Artin parameters have modulus at most \(1\). Thus the rational Dirichlet coefficients \(a(n)\) of \(L\) and \(m(n)\) of \(1/L\) both satisfy \(|a(n)|,|m(n)|\le d(n)\), uniformly in \(Q\). The conductor-uniform local zero count with \(|\gamma-t|\le1\) is \(O(\log(Q(3+|t|)))\). [Thorner–Zaman, §2 and Lemma 2.5](https://msp.org/ant/2019/13-5/ant-v13-n5-s.pdf) · [Artin induction](https://doi.org/10.1007/BF02941010)

Choose \(1/2<\sigma_0<b\), a fixed positive disk radius \(r<\min(b-\sigma_0,(\sigma_0-1/2)/4,1/8)\), and consider \(\sigma_0\le\sigma\le1+r\) and \(T/2\le |t|\le3T\). In the Gaussian approximate functional equation put \(K_T=\sqrt Q\,T\). The first dyadic weight and its variation are \(O((1+Y/K_T)^{-C})\) for every fixed \(C\), and the first weight differs from \(1\) by \(O((Y/K_T)^{1/4})\) for \(Y\le K_T\). The dual weight and its variation are \(O((K_T/Y)^{2r})\) for \(Y\le K_T\), and \(O((Y/K_T)^{-C})\) above \(K_T\). The absolute gamma-and-conductor ratio is \(O(K_T^{1-2\sigma})\). Indeed the conductor is exactly the factor \(Q^{z/2}\) in each Gaussian weight integral and \(Q^{(1-2\sigma)/2}\) in the ratio, and the argument using Stirling is uniform over the finite set of shifts. This is the same contour calculation as for fixed conductor. The dual line \(2r\) keeps the numerator gamma arguments in the right half-plane on the stated strip. [Fixed-conductor contour and mean-square proof](https://github.com/Sodelin/Research-Commons/commit/304b341ad0a4a99eb16055613bfafceb7c476850)

For \(P=T^{1/10}\), let \(A_P(s)=\sum_{n\le P}a(n)n^{-s}\). The first weight replacement on \(n\le P\) costs pointwise \(O(K_T^{-1/4}P^{5/4-\sigma_0}\log(3P))\). The first tail \(n>P\), by Montgomery–Vaughan and dyadic maximal partial summation, has squared mean
\[
 \ll_b (\log(3QT))^C
   \bigl(TP^{1-2\sigma_0}+K_T^{2-2\sigma_0}\bigr).
\]
Here a block \(Y\le K_T\) contributes at most \( (T+Y)Y^{1-2\sigma_0}\) times logarithms. The sums after square roots are largest near \(P\) for the \(T\) term and near \(K_T\) for the \(Y\) term. The arbitrary negative powers bound the blocks above \(K_T\). For the dual sum before the gamma ratio, the squared mean is \(O_b((\log(3QT))^C(T+K_T)K_T^{2\sigma-1})\), since \(2\sigma-1>4r\), also covering the singleton \(n=1\) of size \(O(TK_T^{4r})\). Its normalized squared mean is \(O_b((\log(3QT))^C K_T^{2-2\sigma_0})\), using \(K_T\ge T\). The logarithms come from the maximal inequality and the divisor-square bound \(\sum_{n\le Y}d(n)^2\ll Y\log^3(3Y)\). [Montgomery–Vaughan, Corollary 2](https://doi.org/10.1112/jlms/s2-8.1.73)

Let \(M_X(s)=\sum_{n\le X}m(n)n^{-s}\) with \(X=T^\eta\), where \(\eta>0\) is small in terms of \(b,\sigma_0\). The pointwise cost of multiplying by \(M_X\) is at most \(O(X^2)\). The coefficients of \(A_PM_X-1\) vanish through \(X\) and have modulus at most \(d_4(n)\), with support below \(T\). Thus its squared mean is \(O_b(TX^{1-2\sigma_0}(\log(3T))^C)\). The bound on \(d_4^2\) follows from \(d_k(p^j)^2\le d_{k^2}(p^j)\) by mapping each pair of compositions of \(j\) to a nonnegative integer matrix with those row and column sums. The small-\(n\) approximation error has a uniform power saving even after multiplication by \(M_X\). Taking \(\eta<(2\sigma_0-1)/80\) and shrinking if needed therefore gives
\[
 \int_{T/2\le|t|\le3T}|L(\sigma+it)M_X(\sigma+it)-1|^2\,dt
 \ll_b (\log(3QT))^C
   \left(T^{1-c_0}+Q^{1-\sigma_0}T^{2(1-\sigma_0)+4\eta}\right)
\tag{3}
\]
for some \(c_0>0\), uniformly in the strip and in \(Q\).

At every zero in \(T\le|\gamma|\le2T\), \(\beta\ge b\), the mollified deviation equals \(-1\). Within each radius \(r\) disk its squared modulus integrates to at least \(\pi r^2\). Every point lies in at most \(O(\log(3QT))\) such disks, by the local zero count. Equation (3), integration across the strip, and dyadic summation give the same bound for \(N_\rho(b,T)\) with one extra logarithmic factor. The finitely low ordinates cost \(O(\log(3Q))\) and fit that bound. For the given \(A\), choose \(\sigma_0<b\) sufficiently near \(b\) that
\[
 2(1-\sigma_0)+(1-\sigma_0)/A<1,
\]
then choose \(\eta\) sufficiently small to preserve the strict inequality with \(4\eta\) added. At \(T\ge Q^A\) the conductor term in (3) has a power saving and the logarithms are absorbed into part of the saving. This proves (1). To prove (2), take \(A=(1-b)/(2b-1)+1\), use the local count up to height \(Q^A\), and sum the tail dyadically using (1).

## Fixed interval support

Fix an off-line zero \(\beta_0+i\gamma_0\) with \(\beta_0\ge b\) and maximize \(\beta_0\) among zeros at ordinate \(\gamma_0\). Define \(\Delta\) as the minimum of \(1\) and the nonzero distances from ordinates of zeros with \(\beta\ge\beta_0\) to \(0\) or \(\gamma_0\) lying below \(1\). This is positive by the local zero count. The positive convolution can be supported in \([0,\mathcal L]\), where
\[
 \mathcal L \ll_b 1+\log^2(3Q)
 +\log(Q(3+|\gamma_0|))\bigl(\log(3+|\gamma_0|)+\Delta^{-1}\bigr).
\tag{4}
\]
The length follows from an asymptotic construction and the formula retains its explicit spectral separation dependence.

For each relevant zero \(\rho\) with \(\beta\ge\beta_0\), use a positive two-point factor for every nonzero base frequency \(t=\Im\rho\) and every nonzero modulated frequency \(t=\Im\rho-\gamma_0\). Put \(d_t=\pi/|t|\) and let the weights at \(0,d_t\) be proportional to \(e^{(\beta-\beta_0)d_t},1\). The bilateral transform at \(\beta-\beta_0+it\) vanishes exactly. The support cost is the sum of the \(d_t\). Outside \(|\gamma|\le2|\gamma_0|+3\), both reciprocals are \(O((1+|\gamma|)^{-1})\) and (2) applies. Inside, the local zero count and the harmonic sum around \(0\) or \(\gamma_0\) give the logarithmic term in (4) for distances at least \(1\). The distances below \(1\) cost at most \(O(\log(Q(3+|\gamma_0|))/\Delta)\). Convolve all such factors, and a uniform probability on \([0,1]\) for density at most \(1\). The countable convolution exists because the individual support lengths sum.

In the normalized explicit formula, all zeros with \(\beta<\beta_0\) contribute \(o(1)\) after division by \(e^{\beta_0 u}\), uniformly on a bounded interval beginning at \(u=U\to\infty\). This is dominated convergence in the absolutely summable smoothed residue expansion, with no assumption of a gap below \(\beta_0\). The base mean against the convolution now retains only nonnegative real-pole terms, up to \(o(1)\). The modulated mean retains the chosen term with its nonzero residue, up to \(o(1)\). The identity \(f_+=(|f|+f)/2\) and the triangle inequality for the modulated mean give the fixed-length positive-part lower window. If \(\gamma_0=0\), the base mean alone contains the positive selected term. The support proof has used no uniform lower bound on the residue.

The density bound and the reciprocal sum are conductor-uniform. In (4) the spectral separation term is retained, and the actual onset of detection still depends on convergence below the selected abscissa. The argument requires an arithmetic upper window to exclude the detected zero. These are hand arguments.
