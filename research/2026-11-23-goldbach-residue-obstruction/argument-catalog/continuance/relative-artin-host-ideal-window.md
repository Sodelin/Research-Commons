# Relative Artin host and an ideal-prime window

For \(E=\mathbb Q[x]/(x^3-x-1)\), let \(M\) be its closure, \(K=\mathbb Q(\sqrt{-23})\) and \(\chi\) either nontrivial character of \(\operatorname{Gal}(M/K)=C_3\). The associated Artin factor is \(L_\rho(s)=L_K(s,\chi)\). The following are hand identities and a conditional reduction.

## Relative arithmetic and the CM obstruction

Take \(A=\mathbb Q(\zeta_m)\) with \(23\mid m\), so \(K\subset A\). The maximal abelian subfield of \(M\) is \(K\), hence \(M\cap A=K\) and \(\operatorname{Gal}(MA/K)=C_3\times\operatorname{Gal}(A/K)\). The cubic ideal Frobenius projector consequently factors from the norm-Dirichlet projector as a class function. The extension \(M/K\) is unramified, so \(MA/A\) is unramified and \(|D_{MA}|=|D_A|^3\). Despite this exact discriminant relation, \(MA\) is not CM: complex conjugation restricts to a transposition in \(M\), while a Galois CM field has central complex conjugation. The pinned proof obtains its CM premise from the cyclotomic field realization and uses it for window-related cohomological bounds. Thus the arithmetic enlargement does not give those bounds. [Pinned CM field derivation](https://github.com/Deicyde/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/CMFieldExponentialBounds/IsCMFieldOfIsChiField.lean#L7-L8) · [Use of the CM premise](https://github.com/Deicyde/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/LayerLe.lean#L29-L43).

More generally, if \(B/\mathbb Q\) is Galois CM, then \(M\) cannot lie in \(B\) because its noncentral complex conjugation would descend from a central one. Thus \(M\cap B\subseteq K\). In the compositum, Chebotarev realizes primes splitting completely in \(B\) with both identity and 3-cycle Frobenius in \(M\). No exact projector based solely on splitting in such an auxiliary \(B\) can distinguish those classes.

The CM obstruction here depends on the signature. For example \(x^3-4x-1\) is irreducible with squarefree positive discriminant \(229\), and its \(S_3\) closure is totally real. Its compositum with \(\mathbb Q(\zeta_{229})\) is CM, because complex conjugation is trivial on the closure and central on the cyclotomic factor. The compositum still has a nonabelian quotient and the rational-residue character test still fails. This separates the CM issue from the cyclotomic and character requirements.

## An ideal-indexed replacement for the finite Fourier identity

Let \(S_c(a)\) sum \(\log \mathrm N\mathfrak p\,(a/\mathrm N\mathfrak p^j-1)_+\) over prime powers of \(K\) of class \(c\in C_3\). Let \(B_K(a)=\sum_c S_c(a)\) and \(B_\chi(a)=\sum_c\chi(c)S_c(a)\). Conjugation on \(K/\mathbb Q\) preserves ideal norms and exchanges inverse classes, so \(B_\chi=B_{\chi^{-1}}\). The identity-class projector is \((1+\chi+\chi^{-1})/3\). For any fixed \(\lambda>1\), the positive weighted prime-ideal sum
\[
 A_\lambda(a)=S_1(a)+\lambda^{-1}\sum_{c\ne1}S_c(\lambda a)
\]
therefore equals
\[
 \frac{B_K(a)+2\lambda^{-1}B_K(\lambda a)}{3}
 +\frac23\bigl[B_\chi(a)-\lambda^{-1}B_\chi(\lambda a)\bigr].
\]
The notation \(G_L\) means the normalized observable from the preceding notes, with \(G_K=B_K-a\log a+(1+c_K)a\) and \(c_K=\operatorname{FP}_{s=1}(\zeta_K'/\zeta_K)\). Set \(G_\rho=B_\chi+aL'_\rho(1)/L_\rho(1)\). Then
\[
 A_\lambda(a)-a(\log a-1-c_K+\tfrac23\log\lambda)
 =\frac{G_K(a)+2\lambda^{-1}G_K(\lambda a)}{3}
 +\frac23\bigl[G_\rho(a)-\lambda^{-1}G_\rho(\lambda a)\bigr].
\]
The nontrivial linear correction cancels. The term involving \(G_K\) is controlled in absolute value by Dirichlet GRH because \(\zeta_K\) factors over \(\mathbb Q\). This identity is an ideal-level analogue of the finite character decomposition in the pinned proof. [Pinned decomposition](https://github.com/Deicyde/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SizeWindowBrackets/FirstPrimeNeSecondPrime.lean#L75-L101).

## Why a one-sided difference window suffices

Let \(\Phi(s)\) be the Laplace transform of \(G_\rho(e^u)\) on \(u\ge0\). Replacing \(G_\rho(a)\) by \(G_\rho(a)-\lambda^{-1}G_\rho(\lambda a)\) multiplies \(\Phi(s)\) by \(1-\lambda^{s-1}\), up to an entire term from the finite initial interval \([0,\log\lambda]\). The factor is nonzero in the open strip and positive at its real points. Thus all strip poles of the transform survive, and the required positive residues at real poles stay positive. The same pinned Landau criterion therefore applies to the difference. In particular, an upper bound \(O_\epsilon(a^{1/2+\epsilon})\) on arbitrarily late full windows \([Y,Y^{3/2}]\) for \(A_\lambda\) minus its explicit main term would suffice for GRH of \(L_\rho\), taking \(\epsilon\downarrow0\) and reflecting by the functional equation. The upper bound is the remaining estimate. No iterative extension of sparse windows is needed for this implication. [Pinned Landau criterion](https://github.com/Deicyde/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauWindow.lean#L83-L84).
