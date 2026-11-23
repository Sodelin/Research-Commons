# Positive symmetric-power windows at ramified primes and over totally real fields

Let \(F\) be totally real, \(d=[F:\mathbb Q]\), and \(\pi\) the unitary representation of a non-CM holomorphic Hilbert newform with even weights \(k_v\ge2\) and trivial central character. Write \(\mathfrak n\) for its finite conductor. For an integer \(M\ge1\) set
\[
 L_0=\zeta_F,\qquad L_j=L(s,\operatorname{Sym}^j\pi),\qquad
 P_M=L_M\prod_{j=0}^{M-1}L_j^2,\qquad D_M=(M+1)^2 .
\]
The same finite-family one-sided window used for level-one \(\Delta\) applies with \(\zeta_F\) as reference, including every ramified Euler factor. The new facts are local positivity at all primes and an explicit conductor bound. The window estimate is a separate open input. [Level-one proof](https://github.com/Sodelin/Research-Commons/blob/65a0b8f1d33646f8bbbbc6638d6754996211f31b/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/positive-window-finite-symmetric-powers.md)

## Full local parameters and prime-power weights

Newton–Thorne's Hilbert modular Theorem A supplies cuspidality and the full symmetric-power local parameter at every place. Blasius's Theorem 1 gives temperedness of the unitary \(\pi\) at every finite place. Use geometric Frobenius and write \(q_{\mathfrak p}=\mathrm N\mathfrak p\). For each \(\mathfrak p\) and \(\ell\ge1\), write \(b_M(\mathfrak p,\ell)\) for the coefficient of \(\log q_{\mathfrak p}\ q_{\mathfrak p}^{-\ell s}\) in \(-P_M'/P_M\) from that local factor. We prove \(0\le b_M(\mathfrak p,\ell)\le D_M\). [Newton–Thorne, Theorem A](https://doi.org/10.4007/annals.2026.203.1.4) · [Blasius, Theorem 1](https://doi.org/10.1007/978-3-8348-0352-8_2)

If monodromy is zero, realize the bounded Weil representation \(\rho\) in \(\mathrm{SU}(2)\) by choosing an invariant inner product and using determinant one. The projector onto inertia invariants is the Haar average over the inertia image. Thus the trace of \(\rho(\mathrm{Frob})^\ell\) in each symmetric power on its inertia invariants is the Haar average of the characters evaluated at \(\rho(\mathrm{Frob})^\ell i\), with \(i\) in the inertia image. For any matrix in \(\mathrm{SU}(2)\) with eigenvalues \(z,z^{-1}\), its \(j\)-th symmetric-power character is \(\chi_j(z)=\sum_{a=0}^j z^{j-2a}\) and
\[
 \chi_M(z)+2\sum_{j<M}\chi_j(z)=\left|\sum_{a=0}^M z^a\right|^2.
\]
The identity follows since the coefficient of \(z^a\) on each side is \(M+1-|a|\) for \(|a|\le M\) and zero otherwise. The required log coefficient is therefore an average of values between \(0\) and \(D_M\), even with nontrivial inertia.

If monodromy is nonzero, a tempered two-dimensional parameter has the form \(\chi\otimes\operatorname{Sp}_2\) for a unitary Weil character \(\chi\), with \(\chi^2=1\) by the determinant. Its \(j\)-th symmetric power is \(\chi^j\otimes\operatorname{Sp}_{j+1}\). The monodromy kernel is one-dimensional, Frobenius acts there by \(\chi(\mathrm{Frob})^j q_{\mathfrak p}^{-j/2}\), and the line contributes only when \(\chi^j\) is unramified. If \(\chi\) is ramified, the odd \(j\) terms vanish and the even \(j\) terms are nonnegative. If \(\chi\) is unramified, put \(t=(\chi(\mathrm{Frob})q_{\mathfrak p}^{-1/2})^\ell\). Then
\[
 b_M(\mathfrak p,\ell)=t^M+2\sum_{j=0}^{M-1}t^j
   =\frac{2-(1+t)t^M}{1-t}>0,\qquad -1<t<1.
\]
In both monodromic cases the cap \(2M+1\le D_M\) follows by summing the absolute term bounds. [Explicit special-representation factors, Cogdell–Michel, §3](https://people.math.osu.edu/cogdell.1/moments-www.pdf)

Group the terms at each integer \(n=q_{\mathfrak p}^{\ell}\) to obtain ordinary Dirichlet-series coefficients. The caps persist under addition:
\[
 0\le\Lambda_{P_M}(n)\le D_M\Lambda_F(n),\qquad
 0\le\Lambda_F(n)\le d\Lambda(n),
\]
where \(\Lambda_F\) is the logarithmic-derivative coefficient of \(\zeta_F\). For the last inequality at \(p^a\), each \(\mathfrak p\mid p\) with residue degree dividing \(a\) contributes \(f_{\mathfrak p}\log p\) and \(\sum_{\mathfrak p\mid p}f_{\mathfrak p}\le d\).

## Finite and archimedean conductors

For zero monodromy, any ramification subgroup with nontrivial image has no fixed vector in the original two-dimensional determinant-one unitary representation. A nonidentity element of \(\mathrm{SU}(2)\) has neither eigenvalue equal to \(1\). In the Artin conductor formula over the ramification groups, the codimension of fixed vectors in the \(j\)-th symmetric power is at most \(j+1\) wherever the original codimension is \(2\), and is zero wherever the original codimension is zero. Thus \(a(\operatorname{Sym}^j)\le (j+1)a(\pi)/2\). With nonzero monodromy and ramified \(\chi\), \(a(\pi)=2a(\chi)\), and the symmetric power has conductor exponent \(j\) for even \(j\) and \((j+1)a(\chi)\) for odd \(j\). The same bound follows. With nonzero monodromy and unramified \(\chi\), \(a(\pi)=1\) and \(a(\operatorname{Sym}^j)=j\) exactly.

The ramified-character and zero-monodromy estimates sum to at most \((D_M-2)a(\pi)/2\le M^2a(\pi)\). The unramified special case sums exactly to \(M^2\). Consequently
\[
 \mathfrak q(P_M)\mid\mathfrak n^{M^2}
\]
and equality holds for squarefree \(\mathfrak n\), since conductor exponent one with trivial determinant occurs only in the unramified special case. The absolute finite factor in the completed \(P_M\) is \(|\operatorname{disc}F|^{D_M}\mathrm N\mathfrak q(P_M)\). Its \(dD_M\) real gamma shifts lie in \([0,M(k_{\max}-1)/2+1]\), where \(k_{\max}=\max_v k_v\). Indeed positive angular weights give complex gamma factors in conjugate pairs and the middle line for the even symmetric powers has shift \(0\) or \(1\). With \(Q(t)=|\operatorname{disc}F|^{D_M}\mathrm N\mathfrak q(P_M)\prod_\mu(3+|\mu+it|)\), this gives
\[
 \log Q(t)\le D_M\log|\operatorname{disc}F|+M^2\log\mathrm N\mathfrak n
   +dD_M\log(4+|t|+M(k_{\max}-1)/2).
\]

For \(F=\mathbb Q\), the weight-two newform of level \(11\) has \(a_{11}=1\), so its first ramified test uses \(t=11^{-\ell/2}\) and conductor \(11^{M^2}\) for \(P_M\). The coefficient \(a_{11}\) also follows from the eta product \(q\prod_{n\ge1}(1-q^n)^2(1-q^{11n})^2\), using Euler's pentagonal identity at degree \(10\). Its local conductor exponent one and trivial central character exclude a nontrivial quadratic self-twist: at any prime where that character ramifies, twisting a local unramified or unramified-special representation would give conductor exponent at least two. [Level 11 form and local data](https://www.lmfdb.org/ModularForm/GL2/Q/holomorphic/11/2/a/a/)

## Exact window and verification status

Fix \(B,\kappa>0\). Put \(S_A(x)=\sum_n\Lambda_A(n)(x/n-1)_+\), \(T_vH(x)=e^{-v}H(e^vx)\), \(w_B(v)=2(B-v)/B^2\) for \(0\le v\le B\), and \(c_F=\operatorname{FP}_{s=1}(\zeta_F'/\zeta_F)(s)\). Define the centered count
\[
 C(x)=\int_0^B w_B(v)
      \left[T_v S_{\zeta_F}(x)+\frac{S_{P_M}(x)-T_v S_{P_M}(x)}{D_M}\right]dv
      -x\left(\log x-1-c_F+\frac{(1-2/D_M)B}{3}\right).
\]
The expression inside the integral is a nonnegative count by the coefficient cap. The only pole of \(P_M\) in \(\Re s>0\) is its order-two pole at \(1\). The cuspidal factors have completed functional equations, and Jacquet–Shalika gives their nonvanishing on \(\Re s=1\). Dedekind zeta has the corresponding classical boundary nonvanishing. The gamma factors have no poles or zeros in the open strip. The displayed center cancels the singular terms at \(1\) of the count's Laplace transform, as in the level-one proof. At any strip zero \(z\) its residue is
\[
 -\frac{ Z_B(z)m_{\zeta_F}(z)+(1-Z_B(z))m_{P_M}(z)/D_M}{z(z-1)},\qquad
 Z_B(z)=\int_0^B w_B(v)e^{(z-1)v}dv.
\]
The earlier triangular-kernel proof gives \(0<\Re Z_B(z)<1\). All zeros survive, and real zeros have positive real residue. The growth and measurability hypotheses follow directly from the cap and the continuity of the finite smoothed count. [Classical cuspidal analytic theory](https://doi.org/10.1007/BFb0070263) · [Jacquet–Shalika boundary theorem](https://doi.org/10.1007/BF01390166) · [Pinned kernel and residue argument](https://github.com/Sodelin/Research-Commons/blob/65a0b8f1d33646f8bbbbc6638d6754996211f31b/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/positive-window-finite-symmetric-powers.md)

For every \(0<\epsilon<1/2\) and \(\eta>0\), suppose there are arbitrarily large \(Y\) with
\[
 \int_Y^{Y^{1+\kappa}} C(x)_+x^{-1/2-\epsilon}\,\frac{dx}{x}\le Y^\eta .
\]
The pinned generic Landau theorem bounds every pole by \(1/2+\epsilon\), after substituting \(u=\log x\). Letting \(\epsilon\downarrow0\) and using each functional equation proves the critical-line statement simultaneously for \(\zeta_F,L_1,\dots,L_M\). This direction assumes no RH for the base field. [Pinned Lean declaration](https://github.com/Deicyde/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauWindow.lean#L83-L84)

For the converse alone, assume those critical-line statements. The paired Hadamard calculation from the level-one proof uses the cap at \(\Re s=2\) and a gamma derivative bound, with an added \(\tfrac12\log\bigl(|\operatorname{disc}F|^{D_M}\mathrm N\mathfrak q(P_M)\bigr)\) contribution from the finite conductor. The conductor bound above also majorizes the archimedean logarithms. On the shifted line \(1/2+\epsilon+it\), each zero fraction is separated by \(\epsilon\), and the difference from the fraction at \(2+it\) is \(O_\epsilon((1+(t-\Im z)^2)^{-1})\). Smoothed Perron with kernel \(1/[s(s-1)]\) gives, uniformly for \(x\ge2\),
\[
 |C(x)|\ll_{\epsilon,B}
 x^{1/2+\epsilon}\left[
 \log|\operatorname{disc}F|+\frac{M^2}{D_M}\log \mathrm N\mathfrak n
    +d\log(4+M k_{\max})\right].
\]
The pole residue gives the displayed center and the bound proves the window for each fixed family. Using the finite factor \(|\operatorname{disc}F|\) for \(\zeta_F\) in the same argument gives the stated reference bound. This gives conditional growth with explicit degree, level and discriminant dependence. It gives no uniform onset for the forward window.

The local calculations and the window application are hand proofs. The generic Landau implication is Lean-verified at the cited pin. The Hilbert arithmetic instances and their forward window are unverified in Lean, and the forward estimate itself remains open. No numerical zero tests are used. These individual prime-ideal counts supply no estimate on Goldbach's signed fixed-target correlation.
