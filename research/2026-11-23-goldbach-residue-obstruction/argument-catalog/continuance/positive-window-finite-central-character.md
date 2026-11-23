# A positive symmetric-power window with finite central character

Let \(F\) be totally real. Let \(\pi\) be the unitary representation of a non-CM holomorphic Hilbert newform of weights \(k_v\ge2\) of the same parity, with finite central character \(\omega\) of order \(h\) and conductor ideal \(\mathfrak n\) of \(\pi\). Let \(K/F\) be the cyclic class field cut out by \(\omega\), so \([K:F]=h\). For each fixed \(M\ge1\), put \(D=(M+1)^2\), \(b_M=1\), \(b_j=2\) for \(0\le j<M\), and
\[
 Q_M(s)=\prod_{j=0}^M\prod_{a=0}^{h-1}
             L_F(s,\operatorname{Sym}^j\pi\otimes\omega^a)^{b_j}.
\]
Here \(\operatorname{Sym}^0\pi=1\). This is an integer-power product, including \(\zeta_K^2\) from \(j=0\), with degree \(hD\) over \(F\). At every integer \(n\),
\[
 0\le\Lambda_{Q_M}(n)\le D\Lambda_K(n),
\]
where the coefficients are those of negative logarithmic derivatives and \(\Lambda_K\) refers to \(\zeta_K\). In particular the comparison constant is \(D\) relative to \(\zeta_K\), independent of \(h\). There is a single sparse-window criterion for \(\zeta_K\) and every factor in the product.

## The local positivity proof

Newton–Thorne supplies the cuspidal symmetric powers of \(\pi\) with the full local Langlands parameter at every place. Blasius gives temperedness at all finite places in the stated weight range. At a finite \(v\) of \(F\), let \(\rho_v\) be the two-dimensional Weil–Deligne parameter of \(\pi_v\), and use the full parameter, including monodromy. Its determinant is \(\omega_v\). For each \(w\mid v\) of \(K\), the restriction \(\rho_w=\rho_v|_{W_{K_w}}\) is tempered and has trivial determinant. [Newton–Thorne, Theorem A](https://doi.org/10.4007/annals.2026.203.1.4) · [Blasius, Theorem 1](https://doi.org/10.1007/978-3-8348-0352-8_2)

By local Artin induction, for each \(j\),
\[
 \prod_{a=0}^{h-1} L_v(s,\operatorname{Sym}^j\rho_v\otimes\omega_v^a)
  =\prod_{w\mid v} L_w(s,\operatorname{Sym}^j\rho_w).
\]
Indeed \(\bigoplus_a\omega_v^a\) is the permutation parameter on the cosets of the global cyclic extension, restricted to the local Weil group. Its orbits are the primes \(w\mid v\), with representations \(\operatorname{Ind}_{W_{K_w}}^{W_{F_v}}1\). The tensor-induction identity commutes with monodromy, and local \(L\)-factors are invariant under induction when the geometric Frobenius and the residue-field norm are used at each field. The formula only uses restrictions of local parameters and the known cuspidal lifts over \(F\). It requires no global base-change hypothesis. [Local factors and induction, Tate's Corvallis article](https://ncatlab.org/nlab/files/TateNumberTheory.pdf)

On the \(K_w\) side, the full-level determinant-one calculation applies. With zero monodromy, average the character identity \(\chi_M+2\sum_{j<M}\chi_j=|\sum_{j=0}^M z^j|^2\) over the inertia image in \(\mathrm{SU}(2)\). With nonzero monodromy, write the parameter as a quadratic character times the special two-dimensional representation. At a prime power, the contribution divided by \(\log\mathrm Nw\) is either \(t^M+2\sum_{j<M}t^j=(2-(1+t)t^M)/(1-t)>0\) for \(|t|<1\), or the sum of its surviving even-degree terms for a ramified quadratic twist. Both cases lie in \([0,D]\). Summing over prime powers of \(K\) having a given rational norm proves the cap, including the ramified factors. In particular \(\Lambda_K(p^\ell)\le[K:\mathbb Q]\log p\). [Pinned determinant-one local calculation](https://github.com/Sodelin/Research-Commons/blob/2f189fb75e17c5754dfd95c079f88aae4af40c4f/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/positive-window-ramified-hilbert-symmetric-powers.md)

## Analytic and conductor data

The \(j\ge1\) factors are entire after completion, have functional equations, and are nonzero on \(\Re s=1\) by Jacquet–Shalika. They are closed under taking duals, since \((j,a)\mapsto(j,-j-a\bmod h)\) gives the contragredient. The \(j=0\) product is \(\zeta_K^2\) by abelian factorization, and its only pole in \(\Re s>0\) is the double pole at \(1\). The Euler products have no zeros in \(\Re s>1\), and all the completed factors have archimedean factors regular and nonzero in the open strip. [Godement–Jacquet](https://doi.org/10.1007/BFb0070263) · [Jacquet–Shalika](https://doi.org/10.1007/BF01390166)

Write \(A_M\) for the absolute finite conductor factor in the completion of \(Q_M\). The following bound uses only the original level, the cyclic discriminant and the degree:
\[
 \log A_M\le D\log|\operatorname{disc} K|
                +h(D-2)\log\mathrm N_F\mathfrak n .
\]
For \(j\ge1\), the local Artin conductor of \(\operatorname{Sym}^j\rho_v\otimes\omega_v^a\) is at most \((j+1)(a(\rho_v)+a(\omega_v^a))\). For the Swan part, at each positive ramification index the new codimension is at most \(j+1\) and is zero if both original actions are trivial. For the tame plus monodromy term, the new codimension is at most \(j+1\) in \((\ker N)^I\), and it is zero if both original tame-plus-monodromy terms are zero. Summing over \(j,a\) uses \(\sum_{j\ge1}b_j(j+1)=D-2\). The \(j=0\) terms give exactly two copies of the character conductor contribution. The conductor–discriminant formula \(\prod_a\mathfrak f_{\omega^a}=\mathfrak d_{K/F}\), together with the absolute factor \(|\operatorname{disc}F|^{hD}\), gives the displayed bound. This argument does not require squarefree level.

All \(h[F:\mathbb Q]D\) real gamma shifts, with each complex gamma written as two real ones, lie in \([0,M(k_{\max}-1)/2+1]\), where \(k_{\max}=\max_v k_v\). At a real place the nonzero angular weights give complex gamma factors, and any middle line has real shift \(0\) or \(1\). A sign twist at that place only changes the middle-line parity. Thus the analytic conductor logarithm is at most
\[
 \log A_M+[K:\mathbb Q]D\log(4+|t|+M(k_{\max}-1)/2).
\]

As a ramified example over \(\mathbb Q\), take the unitary \(\pi_\Delta\otimes\xi\), where \(\xi(2)=i\) generates the quartic characters modulo \(5\). Its central character is \(\xi^2\), \(K=\mathbb Q(\sqrt5)\), and the level is \(25\) because at \(5\) two unramified Weil characters are twisted by a character of conductor exponent one. For \(M=1\),
\[
 Q_1=\zeta_K^2 L(s,\pi_\Delta\otimes\xi)L(s,\pi_\Delta\otimes\xi^3).
\]
Both cuspidal local factors at \(5\) are \(1\), so the log coefficient at \(5^k\) is \(2\log 5\) for each \(k\ge1\), and the absolute finite conductor is \(5^6\).

## The exact centered window

Fix \(B,\kappa>0\). Put \(S_A(x)=\sum_n\Lambda_A(n)(x/n-1)_+\), \(T_v H(x)=e^{-v}H(e^v x)\), and \(w_B(v)=2(B-v)/B^2\) on \(0\le v\le B\). With \(c_K=\operatorname{FP}_{s=1}(\zeta_K'/\zeta_K)(s)\), set
\[
 C(x)=\int_0^B w_B(v)\left[T_v S_{\zeta_K}(x)
                  +\frac{S_{Q_M}(x)-T_v S_{Q_M}(x)}{D}\right]dv
        -x\left(\log x-1-c_K+\frac{(1-2/D)B}{3}\right).
\]
The count before subtracting the center is nonnegative by the coefficient cap. Suppose for every \(\eta>0\) there are arbitrarily large \(Y\) with
\[
  \int_Y^{Y^{1+\kappa}} C(x)_+x^{-1/2}\,\frac{dx}{x}\le Y^\eta .
\]
Then all strip zeros of every \(L_F(s,\operatorname{Sym}^j\pi\otimes\omega^a)\) with \(0\le j\le M\) lie on \(\Re s=1/2\). This includes the untwisted prefix and RH for \(\zeta_K\).

For \(A=Q_M,\zeta_K\), subtract \(x(a_A\log x-a_A-c_A)\) from \(S_A(x)\), with \(a_A\) the pole order at \(1\) and \(c_A\) the finite part of \(A'/A\) there. The resulting two Laplace transforms have both singular terms at \(1\) canceled. The shift compactly averages their transforms with factor \(Z_B(z)=\int_0^B w_B(v)e^{(z-1)v}dv\), up to terms that are entire. The strip residue of the centered count is
\[
 -\frac{Z_B(z)m_{\zeta_K}(z)+(1-Z_B(z))m_{Q_M}(z)/D}{z(z-1)} .
\]
The triangular kernel satisfies \(0<\Re Z_B(z)<1\) in the strip, so shared zeros survive and real poles have positive residues. The coefficient bounds give continuity and \(O(e^{2u})\) growth for \(C(e^u)\), and finite products give a discrete pole set. The stated window is the positive-part input to the generic Landau theorem at \(u=\log x\), with exponent \(1/2\). It gives the upper exclusion, and the dual permutation with functional equations gives the lower exclusion. [Pinned triangular and transform calculation](https://github.com/Sodelin/Research-Commons/blob/65a0b8f1d33646f8bbbbc6638d6754996211f31b/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/positive-window-finite-symmetric-powers.md) · [Pinned Lean Landau theorem](https://github.com/Deicyde/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauWindow.lean#L83-L84)

For the converse alone, assume those critical-line statements. Write
\[
 \mathcal L=\log A_M+[K:\mathbb Q]D\log(4+Mk_{\max}).
\]
The entire completion \([s(s-1)]^2 A_M^{s/2}\gamma_M(s)Q_M(s)\) has order at most one and a reflection equation about \(1/2\) up to sign. Real Euler coefficients and the dual permutation give the required symmetry. Pairing zeros \(1/2\pm it_\rho\) in the Hadamard product removes the linear exponential by reflection. Taking the real logarithmic derivative at \(2+it\), using the Euler cap and the gamma shifts, bounds
\[
 \sum_{\rho}\frac{1}{1+(t-t_\rho)^2}
   \ll \mathcal L+[K:\mathbb Q]D\log(3+|t|),
\]
where multiplicities are included. The difference of zero fractions at \(1/4+it\) and \(2+it\) is \(O((1+(t-t_\rho)^2)^{-1})\) per zero. Shift the smoothed Perron integral with kernel \(x^s/[s(s-1)]\) to \(1/4\). Use horizontal heights separated from the ordinates by a small constant times the reciprocal of the displayed local-count bound. Such heights exist in each sufficiently high unit interval by the same bound, and at these heights the horizontal integrals tend to zero. The new vertical integral is \(O(x^{1/4}\mathcal L)\). The residues at the zeros have total absolute size at most \(\sqrt{x}\sum_\rho(1/4+t_\rho^2)^{-1}\ll\sqrt{x}\mathcal L\). The residue at \(1\) gives the smooth center of \(S_{Q_M}\). Apply the same argument to \(\zeta_K\) with a simple pole and absolute conductor \(|\operatorname{disc}K|\). After normalization by \(D\) in the \(Q_M\) term and compact averaging, this yields uniformly for \(x\ge2\)
\[
 |C(x)|\ll_B \sqrt{x}\left[
 \log|\operatorname{disc}K|+\frac{h(D-2)}D\log\mathrm N_F\mathfrak n
                    +[K:\mathbb Q]\log(4+Mk_{\max})\right].
\]
The square-root window follows for each fixed family. The forward implication uses no critical-line hypothesis and gives no bound on the locations of good windows. [Hadamard formula and zero counts for completed \(L\)-functions, Iwaniec–Kowalski, §5.3](https://doi.org/10.1090/coll/053)

The coefficient identities, conductor comparison and arithmetic instantiation are hand proofs. The pinned generic Landau implication is Lean-verified. The required forward estimate is open, and no numerical zero tests are used. The individual prime-ideal counts give no signed additive estimate at a fixed Goldbach target.
