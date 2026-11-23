# A squarefree-core cutoff for the original Artin upper window

For the fixed standard two-dimensional Artin representation of an \(S_3\) closure, the large inverse-coefficient remainder of the original undamped dilation allows one more removal. Write the inverse variable as \(m=ab^2\), with squarefree coprime \(a,b\). All terms with \(a\le x^{1/3}\) cost \(O_{L,B,\epsilon}(x^{1/2+\epsilon})\) unconditionally. Using only RH for the Riemann zeta function, the same bound holds through \(a\le x^{3/7}\). In particular the two bounds remove a portion of the range \(m>\sqrt x\). They leave the original \(K_B\), exact reference and upper sign in place. [Pinned original dilation and short inverse-variable proof](https://github.com/Sodelin/Research-Commons/commit/ee0116a4311b3556c361afdacf16d622024c246a)

## The exact inverse split

Write \(L(s)=\sum_n\lambda(n)n^{-s}\), \(L(s)^{-1}=\sum_m\mu_L(m)m^{-s}\). The coefficient of \(p^{-2s}\) in the local inverse is the determinant of the unramified representation and is zero at any ramified prime. Indeed the standard representation is faithful, so nontrivial inertia has a space of invariants of dimension at most one. The determinant character is the sign of \(S_3\), corresponding to the nonprincipal quadratic character of the resolvent field. Let \(\eta\) be that character with the factors at all rational primes ramified in the closure omitted. It is a fixed, possibly imprimitive, nonprincipal quadratic character. Since each local inverse has degree at most two, every nonzero term is of the form
\[
 \mu_L(ab^2)=\mu(a)\lambda(a)\eta(b)
 \qquad(a,b\ \text{squarefree},\ (a,b)=1).
 \tag{1}
\]
This identity includes all ramified assignments. Also \(|\lambda(n)|\le d_2(n)\) by the unit-disc Euler roots. [Artin induction and local factors](https://doi.org/10.1007/BF02941010) · [Completed degree-two data used in the proof](https://github.com/Sodelin/Research-Commons/commit/304b341ad0a4a99eb16055613bfafceb7c476850)

At a fixed \(a\), the series in \(b\) is
\[
 D_a(s)=\sum_{(b,a)=1}\frac{\mu^2(b)\eta(b)}{b^{2s}}
       =\frac{L(2s,\eta)}{L(4s,\eta^2)}
            \prod_{p\mid a}(1+\eta(p)p^{-2s})^{-1}.
 \tag{2}
\]
The equality follows in \(\Re s>1/2\) by multiplying the local factors. The last product is \(O_{\sigma,\epsilon}(a^\epsilon)\) uniformly on \(\Re s\ge\sigma>0\). For large enough \(p\), each inverse factor is at most \(p^\epsilon\), and the finitely many smaller primes give a fixed constant. Since \(\eta^2\) is principal, \(L(4s,\eta^2)=\zeta(4s)\prod_{p\mid{\rm mod}(\eta)}(1-p^{-4s})\). These finitely many factors and their inverses are bounded in every fixed \(\Re s\ge\sigma>0\).

For \(K_B\) of the pinned dilation, its Mellin multiplier is
\[
 H_B(s)=\frac{e^{(s-1)B}-1}{s(s-1)}.
\]
The original centered \(C_{0,B}(x)\) is \(-1/4\) times the sum of \(\mu_L(m)\lambda(n)\log n\,K_B(mn/x)\). Thus the portion with \(a\le A\), before the factor \(-1/4\), is exactly
\[
 \sum_{a\le A}\mu(a)\lambda(a)\,
    \frac1{2\pi i}\int_{(2)}
       -L'(s)D_a(s)(x/a)^s H_B(s)\,ds .
 \tag{3}
\]
On the right line all series are absolutely convergent. The equality preserves the compact support \(mn\le e^Bx\) after inversion.

## Unconditional cutoff

Fix \(1/4<\sigma<1/2\). The denominator in (2) is invertible with absolute Euler convergence on \(\Re s\ge\sigma\). The numerator is entire since \(\eta\) is nonprincipal. For the degree-two \(L\), Phragmén–Lindelöf and Cauchy's formula bound \(L'(\sigma+it)\ll_{L,\epsilon}(3+|t|)^{1-\sigma+\epsilon}\). The degree-one convexity bound gives \(L(2\sigma+2it,\eta)\ll_{\eta,\epsilon}(3+|t|)^{1/2-\sigma+\epsilon}\). The product with \(H_B\), whose decay is \(O_B((3+|t|)^{-2})\) at large height on the fixed strip, is absolutely integrable on the line, since \(3/2-2\sigma<1\). The same pointwise bounds with the nonnegative parts of the convexity exponents justify moving the horizontal pieces to infinity. There is no pole in the strip because \(H_B\) is regular at \(1\) and the only possible denominator poles from zeros are to its left. Therefore (3) is
\[
 O_{L,\sigma,\epsilon}\bigl(x^\sigma A^{1-\sigma+\epsilon}\bigr).
 \tag{4}
\]
The vertical bound is uniform for \(B>0\) after the contour shift, since the numerator of \(H_B\) is then at most \(2\) in modulus. Taking \(\sigma\) just above \(1/4\) proves the stated \(A\le x^{1/3}\) bound.

## Cutoff from Riemann zeta RH

Under RH, \(1/\zeta(s)\ll_{\delta,\epsilon}(3+|\Im s|)^\epsilon\) uniformly for \(\Re s\ge1/2+\delta\), with \(1/\zeta\) extended by zero at \(1\). One direct derivation uses a holomorphic log of \((s-1)\zeta(s)/(s+1)\) on \(\Re s>1/2\). The Euler branch on \(\Re s=2\) is bounded. Borel–Carathéodory on concentric disks centered at \(2+it\), using polynomial growth of \(\zeta\), bounds that log by \(O_\delta(\log(3+|t|))\) on a line \(\sigma_0\) strictly between \(1/2\) and \(1/2+\delta\). Apply three-lines to the log multiplied by \(e^{(s-it_0)^2}\) on \([\sigma_0,2]\). The two boundary bounds are \(O_\delta(\log(3+|t_0|))\) and \(O(1)\) respectively. This gives an \(o_\delta(\log(3+|t_0|))\) bound uniformly on \(\Re s\ge1/2+\delta\) in the strip. The absolutely convergent Euler product handles the rest. This use of RH concerns only \(\zeta\), the declaration `riemannHypothesis : RiemannHypothesis` in the verified Dirichlet scope. [Verified RH statement](https://math.mit.edu/~drew/grh/#what-was-verified)

Fix now \(1/8<\sigma<1/4\). On or to the right of \(\sigma\), (2) is holomorphic under this zeta RH and its reciprocal denominator is \(O_{\sigma,\epsilon}((3+|t|)^\epsilon)\). The pointwise convexity exponents used above total at most \(3/2-2\sigma+\epsilon<2\) throughout the horizontal shift, so the horizontal integrals still vanish. Vertical convergence now follows from mean squares. In the fixed half-plane strictly to the right of \(1/2\), the dyadic second moments of \(L\) and \(L'\) are \(O_{L,\epsilon}(T^{1+\epsilon})\). For \(L\), use the smooth approximate functional equation and Dirichlet-polynomial mean square in the pinned degree-two proof, equation (3) there and the square summability of its short polynomial. This is uniform on any fixed compact real substrip of \(1/2<\Re s\le1\). For \(L'\), apply Cauchy's formula on a fixed small circle remaining inside that half-plane and integrate the resulting bound, allowing a fixed enlargement at the height endpoints. For the Dirichlet \(L\)-function the same approximate-functional-equation mean-square argument has shorter length \(T^{1/2}\) and bounded coefficients. The finitely many factors lost under imprimitive induction are bounded on the fixed lines in use. [Pinned degree-two mean square](https://github.com/Sodelin/Research-Commons/commit/304b341ad0a4a99eb16055613bfafceb7c476850) · [Montgomery–Vaughan, Corollary 2](https://doi.org/10.1112/jlms/s2-8.1.73)

Apply the functional equations to the two factors on the shifted line. The squared degree-two ratio is \(O(T^{2-4\sigma})\), and its logarithmic derivative is \(O(\log T)\) by Stirling. The squared degree-one ratio at \(2\sigma+2it\) is \(O(T^{1-4\sigma})\). Differentiating the degree-two functional equation gives
\[
 \int_T^{2T}|L'(\sigma+it)|^2dt\ll T^{3-4\sigma+\epsilon},
 \qquad
 \int_T^{2T}|L(2\sigma+2it,\eta)|^2dt\ll T^{2-4\sigma+\epsilon}.
\]
Thus Cauchy–Schwarz with the reciprocal bound and the \(T^{-2}\) multiplier bounds the dyadic absolute integral in (3) by
\[
 O_{\sigma,\epsilon}\bigl(a^\epsilon(x/a)^\sigma
                      T^{1/2-4\sigma+2\epsilon}\bigr).
\]
This is summable for each fixed \(\sigma>1/8\) by taking a small enough \(\epsilon\). It proves (4) at these new lines. Taking \(\sigma\) just above \(1/8\) proves the \(A\le x^{3/7}\) cutoff.

The overlap with \(m\le\sqrt x\) costs \(O(x^{1/2+\epsilon})\) on its own by the pinned short inverse-variable argument. That estimate uses absolute bounds in the outer \(m\) sum and permits restricting it to \(a\le A\). Hence the signed sum with \(m>\sqrt x\) and \(a>A\) is an equivalent target for the one-sided upper-window criterion, at either stated cutoff. One can impose fixed \(A\le Y^{1/3}\) or \(A\le Y^{3/7}\) and fixed short inverse cutoff \(\lfloor\sqrt Y\rfloor\) throughout a window starting at \(Y\). The cutoff above \(1/3\) uses zeta RH, while both conclusions leave the remaining \(S_3\) signed sum open. These are hand proofs, with no numerical tests or new Lean verification.

## The principal determinant case for \(\Delta\)

For the unitary standard factor \(L_\Delta(s)\) of Ramanujan's cusp form, the inverse quadratic coefficient at every prime equals \(1\), so \(\eta\) in (2) is principal and \(D_a\) has a potential simple pole at \(1/2\) from \(\zeta(2s)\). The completed degree-two function \(G(s)L_\Delta(s)\) has root number \(+1\) and \((G L_\Delta)'(1/2)=0\). Here \(G\) is the standard archimedean factor including the conductor and is regular and nonzero at \(1/2\). Set \(c=(G'/G)(1/2)\). Then
\[
 (-L_\Delta'-cL_\Delta)(1/2)=0,\qquad
 \Lambda_\Delta=\mu_\Delta *\bigl((\log n-c)\lambda_\Delta(n)\bigr)+c\mathbf1_{\{1\}}.
\]
The extra term in the original dilation is \(O(1)\). The modified derivative multiplier cancels the pole of \(\zeta(2s)\) for every \(a\). The degree-two convexity and mean-square arguments apply to both summands of this multiplier. Away from its pole, the degree-one estimates for \(\zeta(2s)\) on the shifted lines are the same as the ones used above. The dyadic mean square to the right of \(1/2\) is \(O(T^{1+\epsilon})\) on a fixed line there, by the classical Dirichlet-polynomial approximation or the degree-one approximate functional equation with the elementary pole residues. Those residues in the Gaussian formula at \(t\asymp T\) are exponentially small. This proves the same \(x^{1/3}\) and RH-based \(x^{3/7}\) cutoffs for the modified inverse decomposition of the original \(\Delta\) observable. The shift uses only the central functional equation, including when the central value vanishes. [Pinned \(\Delta\) window and its standard factor](https://github.com/Sodelin/Research-Commons/blob/1e5d50b6571a6333d3d2382f82345a1f22a1ee16/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/positive-automorphic-window-delta.md)
