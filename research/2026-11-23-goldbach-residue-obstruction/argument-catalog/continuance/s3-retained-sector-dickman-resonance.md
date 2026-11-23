# Top-zero contributions in the retained \(S_3\) sectors

This is a conditional spectral calculation for the original signed product-supported correlation. Let \(L=L(s,\rho)\) be a fixed standard \(S_3\) Artin factor. Assume its rightmost completed-zero abscissa \(\beta>1/2\) is attained at a nonempty finite set \(Z_\beta\), and that every other completed zero has real part at most \(\beta-g\) for some fixed \(g>0\). Write \(m_\zeta\) for the multiplicity of a distinct zero \(\zeta\in Z_\beta\). The gap is an extra hypothesis. The calculation neither asserts an off-line zero nor requires the top zeros to be real.

Fix \(1/3<u<1/2\) and \(1-2u<v<u\), with \(U=\lfloor x^u\rfloor\), \(V=x^v\). Write
\[
 C(x)=-\frac14\sum_n\Lambda_L(n)K_B(n/x),
 \qquad H_B(s)=\int_0^\infty K_B(t)t^{s-1}\,dt.
\]
Under the verified quadratic Dirichlet input, the high-prime extraction and square removal give the pure squarefree sector
\[
 \mathcal P(x)=\frac14\sum_{p>U}\Lambda_L(p)
  \sum_{\substack{D>1\ {\rm squarefree}\\q\mid D\ \Rightarrow\ q>V}}
       \Bigl(\prod_{q\mid D}a(q)\Bigr)K_B(pD/x)
\]
and the residual sector on the unchanged companion support
\[
 \mathcal S(x)=-\frac14
        \sum_{\substack{p>U,\ h>U\\P^+(h)\le V}}
         \Lambda_L(p)\beta_U(h)K_B(ph/x).
\]
All variables are supported by \(K_B\) at product at most \(e^Bx\). The preceding polynomial Vaughan and extraction errors have an exponent strictly below \(\beta\), so \(C(x)=\mathcal P(x)+\mathcal S(x)+O(x^{\beta-c})\) for some \(c>0\). [Extraction and determinant-square removal](https://github.com/Sodelin/Research-Commons/commit/c163fceb15615c18fd57dee62056fb04c58442ca) · [Polynomial Vaughan comparison](https://github.com/Sodelin/Research-Commons/commit/89d1c3233e8cdcdbac25dab42c512b1768d9cefd)

Put \(w=(1-u)/v\). For \(k\ge1\) define
\[
 J_k(w)=
 \int_{\substack{y_i\ge1\\ y_1+\cdots+y_k\le w}}
        \frac{dy_1\cdots dy_k}{y_1\cdots y_k},\qquad
 J_0(w)=1\quad(w\ge0),\qquad
 D_m(w)=\sum_{k\ge0}\frac{(-m)^k}{k!}J_k(w).
\]
The sum is finite. Then
\[
 \begin{aligned}
 \mathcal P(x)
 &=\frac14\sum_{\zeta\in Z_\beta}
    m_\zeta\bigl(1-D_{m_\zeta}(w)\bigr)
    H_B(\zeta)x^\zeta+O(x^\beta/\log x),\\
 \mathcal S(x)
 &=\frac14\sum_{\zeta\in Z_\beta}
    m_\zeta D_{m_\zeta}(w)
    H_B(\zeta)x^\zeta+O(x^\beta/\log x).
 \end{aligned}
\tag{1}
\]
For simple top zeros, \(D_1(w)\) is the ordinary Dickman function and \(0<D_1(w)<1\) because \(w>1\). Thus the pure-prime and the low-smooth sectors each carry a nonzero fixed fraction of the original positive off-line signal under this spectral hypothesis. Narrowing the smooth support makes its fraction smaller without changing its exponent.

## Prime measure prediction under the gap

The exact prime-supported logarithmic series is \(-L'/L-Z\), where \(Z\) is the absolutely convergent higher-power series on \(\Re s>1/2\). Choose \(\sigma_1\) strictly between \(\max(1/2,\beta-g)\) and \(\beta\). Truncated Perron at a half-integer, with height of order \(T^2\), shifts to \(\sigma_1\). The local logarithmic derivative is logarithmically bounded on that line by its fixed separation from both sets of zeros. The same bound holds on the high horizontal edges, since the finitely many top zeros are then far away and the other zeros lie strictly to the left. Each top zero contributes \(-m_\zeta T^\zeta/\zeta\). Endpoint errors from replacing the half-integer and the logarithmic factors are absorbed into a fixed power gap. Thus for some \(c_0>0\),
\[
 \Theta_a(T):=\sum_{p\le T}a(p)\log p
   =-\sum_{\zeta\in Z_\beta}\frac{m_\zeta}{\zeta}T^\zeta
    +O(T^{\beta-c_0}).
\tag{2}
\]
Here \(\Lambda_L(p)=a(p)\log p\), including at ramified primes. [Truncated Perron, Montgomery–Vaughan Theorem 5.2](https://doi.org/10.1017/CBO9780511618314) · [Local logarithmic derivative, Iwaniec–Kowalski Proposition 5.7](https://doi.org/10.1090/coll/053)

The model logarithmic prime measure has density \(-\sum_\zeta m_\zeta t^{\zeta-1}\,dt\). The model counting measure has the same density divided by \(\log t\). Both cumulative errors are \(O(T^{\beta-c_0})\) by (2) and partial summation, after reducing \(c_0\) if needed. This remains true relative to a lower endpoint \(P\in[2,T]\), since the subtraction at \(P\) costs at most the same bound.

## Exact cutoffs and errors for tuples

For each fixed \(k\), order the \(k\) distinct selected primes and divide their contribution by \(k!\). Repeated primes in the unrestricted ordered sum can be removed with a strict power gap below \(x^\beta\). Indeed the difference of the elementary symmetric coefficient from the unrestricted coefficient is a finite polynomial in the power sums
\(\sum_{q>V}a(q)^j q^{-js}\), with every monomial containing one factor with \(j\ge2\). Its support has norm \(>V^2\) and it is bounded absolutely by \(O(V^{1-2\sigma})\) for \(\Re s=\sigma>1/2\). Truncate the whole remaining signed cofactor at norm \(e^Bx/V^2\). It has a Perron prefix bound from its analytic product of prime series on the zero-free half-plane to the right of \(\beta\). Shift the smoothed integral to just above \(1/2\), as in the squared-prime comparison, obtaining
\[
 O_\varepsilon(x^{1/2+(1-2v)(\beta-1/2)+\varepsilon}).
\]
This is smaller than \(x^\beta\). The outer prime \(p\) is still permitted to coincide with one selected prime, as in the original retained sum. [Selected-prime power-sum contour](https://github.com/Sodelin/Research-Commons/commit/c163fceb15615c18fd57dee62056fb04c58442ca)

In the unrestricted tuple, replace one prime measure at a time by its model. Group all other variables into one signed multiplicative cofactor measure. Its cumulative function at \(y\le e^Bx\) is bounded by \(O_\varepsilon(x^\varepsilon y^{\beta+\varepsilon})\), uniformly for this fixed number of factors. For raw prime factors this follows by a single truncated Perron argument for products of the cutoff prime series, each subpower strictly to the right of \(\beta\). For each already replaced model factor, use
\(\int_P^\infty t^{-\beta-\varepsilon}|dM(t)|\ll_\varepsilon1\),
valid for both model measures and \(P\ge2\). The same bound holds for a cofactor of only model factors by starting with the atom at \(1\). The cutoff factors \(U^\varepsilon,V^\varepsilon\) are absorbed into \(x^\varepsilon\).

Set \(X=\log x\) and \(k_B(z)=K_B(e^z)\). On log coordinates \(r,s\), integration by parts in both the error-factor variable and the grouped cofactor variable brings their cumulative functions against the finite measure \(k_B''(r+s-X)\,dr\,ds\). More explicitly, \(k_B''\) is the distributional measure
\[
 e^{-z}\mathbf1_{(0,B)}(z)\,dz-\delta_0+e^{-B}\delta_B .
\]
Relative cumulative functions vanish outside their exact lower support and no upper boundary term remains. This identity also follows by smoothing \(k_B\) and taking a limit. Jumps in cumulative functions intersect the lines \(r+s=X\) and \(r+s=X+B\) only in a set of line measure zero. The error-factor lower bound is \(r\ge\min(u,v)X\). On every line of the support of the displayed measure its cumulative function costs \(O(e^{(\beta-c_0)r})\), while the cofactor costs \(O_\varepsilon(x^\varepsilon e^{(\beta+\varepsilon)s})\). The line length is \(O_B(X)\). This saves a fixed power after taking \(\varepsilon\) small. Thus no extra derivatives of the original kernel are required to control errors in tuples of any fixed length.

## The same top ordinate in all prime variables

After replacement, the model tuple for an outer top zero \(\zeta_0=\beta+i\gamma_0\) and selected top zeros \(\zeta_i=\beta+i\gamma_i\) uses log variables \(r_0>uX,\ r_i>vX\), with differential weight
\[
 (-1)^{k+1}m_{\zeta_0}\prod_i m_{\zeta_i}\,
 e^{\zeta_0 r_0}\prod_{i=1}^k\frac{e^{\zeta_i r_i}}{r_i}\,
 k_B\left(r_0+\cdots+r_k-X\right)dr_0\cdots dr_k .
\]
Put \(z=r_0+\cdots+r_k-X\). If any selected \(\gamma_i\ne\gamma_0\), integrate first in \(r_i\) on its exact interval
\([vX,(1-u)X+z-\sum_{\ell\ne i}r_\ell]\).
The oscillatory integral \(\int e^{i(\gamma_i-\gamma_0)r_i}dr_i/r_i\) is \(O(1/(|\gamma_i-\gamma_0|vX))\) by integration by parts. The other log integrals are bounded because all lower limits are proportional to \(X\). Integrating \(z\) costs \(O(x^\beta)\), so the mixed tuples are \(O(x^\beta/X)\).

If all \(\zeta_i=\zeta_0=\zeta\), the inner integral equals
\[
 J_k\left(\frac{1-u+z/X}{v}\right).
\]
It differs from \(J_k(w)\) by \(O(|z|/X)\) for bounded \(|z|/X\), because the simplex integral is locally Lipschitz and all coordinates are at least \(1\). The remaining negative \(z\) tail is exponentially small by \(e^{\beta z}\). Since
\(\int_{-\infty}^B e^{\zeta z}k_B(z)dz=H_B(\zeta)\),
the \(k\)-tuple sector has same-ordinate term
\[
 \frac{(-1)^{k+1}m_\zeta^{k+1}}{4k!}
   H_B(\zeta)x^\zeta J_k(w).
\]
All \(k\) on the support are uniformly bounded. Summing proves the first line of (1). In the smoothed explicit formula for \(C\), the coefficient at \(\zeta\) is \(m_\zeta H_B(\zeta)/4\), and the spectral gap gives a fixed power saving for the remaining zeros. This proves the second line.

For simple zeros the positivity of \(D_1(w)\) can be proved directly. Differentiating the simplex integral gives \(wJ_k'(w)=kJ_{k-1}(w-1)\) almost everywhere, by multiplying the boundary integral by \(w=\sum_i y_i\) and using symmetry. Thus \(wD_1'(w)=-D_1(w-1)\) for \(w>1\), with \(D_1=1\) on \([0,1]\). Equivalently \(wD_1(w)=\int_{w-1}^w D_1(t)\,dt\). A first positive-height zero is impossible by this integral identity, and the derivative is strictly negative for \(w>1\). Both shares in (1) are consequently strictly positive for \(w>1\).

The finite exponential sum at the top line has nonnegative constant coefficient and a nonzero frequency coefficient, or a positive constant coefficient if the only top zero is real. Averaging over a long enough fixed log interval separates these finitely many frequencies and gives fixed positive-part mass after normalization by \(x^\beta\). The error in (1) then tends to zero uniformly on such late intervals. This makes the obstruction precise for the original upper sign under the stated spectral hypothesis.

When \(2v>1-u\), only \(k=1\) contributes, so \(1-D_m(w)=m\log w\). In that range the exact fully centered double-prime and low-smooth terms have the same leading coefficients by the strict-gap Dirichlet centering comparison. These are conditional hand arguments. They do not establish the spectral gap or a square-root bound for the signed arithmetic target.
