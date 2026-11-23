# Proof memo — The S₃ Artin factor and the Goldbach long-divisor range

**Verdicts.** Direct transfer of the Dirichlet construction to S₃ is **unsupported**. Its generic zero-free criterion does transfer **conditionally**, through an explicit estimate below. On the Goldbach side, a longer balanced odd–odd range is **proved by hand** using classical congruence estimates. Deriving the gain from nonabelian prime splitting counts is **unsupported**.

## 1. The S₃ test

**Lean verification.** Sutherland reports kernel replay and statement comparison for the five headline theorems. At the original archive pin, `Main.lean` uses `allChi` for right-half-plane nonvanishing, `Claim.strip allChi` for the strip theorem, and `Formalism.VW.critLine allChi` for the primitive theorem. The nonvanishing chain runs from `allChi` through `everyCharacter_of_row`, `every_character_of_literature_of_vWin` and `every_character_of_theta_integrals_local_matching` to `TopPlug`. There `zero_free_all_of_green_v_win` supplies `supplyChi ψ (hV ψ)` to `zeroFreeAll_of_topG` at scale `3 / 2`. This memo identifies the pinned declarations and uses the public report for the kernel replay. [MIT verification](https://math.mit.edu/~drew/grh/#what-was-verified) · [Archive pin](https://github.com/Deicyde/riemann-hypothesis/commit/40e56bab026552e089d7afcfeff08d2defb9c005) · [Main](https://github.com/Deicyde/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Main.lean#L4-L12) · [MainTheorems](https://github.com/Deicyde/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Supplements/Kernels/MainTheorems.lean#L7-L16) · [MainConclusion](https://github.com/Deicyde/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean#L7-L11) · [EveryCharacterOfLiteratureOfVWin](https://github.com/Deicyde/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean#L810-L813) · [Theta-integral bridge](https://github.com/Deicyde/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean#L69-L73) · [TopPlug](https://github.com/Deicyde/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean#L12-L18).

**Hand verification.** Take \(E=\mathbb Q(\alpha)\) with \(\alpha^3-\alpha-1=0\). The polynomial is irreducible by the rational-root test. Its squarefree discriminant \(-23\) is the field discriminant. The closure \(M\) has group \(S_3\) with quadratic resolvent \(K=\mathbb Q(\sqrt{-23})\). The permutation representation on the three embeddings is \(\mathbf1\oplus\rho\). For either nontrivial character \(\vartheta\) of \(A_3\), \(\operatorname{Ind}_{A_3}^{S_3}\vartheta=\rho\) by its character values \(2,0,-1\). Artin formalism, including inertia-invariant local factors at the ramified primes, and reciprocity therefore give
\[
\zeta_E(s)=\zeta(s)L_{\mathbb Q}(s,\rho),\qquad
L_{\mathbb Q}(s,\rho)=L_K(s,\chi).
\]
Here \(\chi\) is the cubic Hecke character of \(M/K\). The conductor identities give \(Q_\rho=|D_E|=|D_K|\mathrm N\mathfrak f_\chi=23\), so \(\mathfrak f_\chi=(1)\). Hecke theory supplies entireness and the functional equation. The completion has factor \(23^{s/2}\Gamma_{\mathbb C}(s)\) and root number \(+1\), also obtained by dividing the completed zeta functions. [Artin on induction](https://doi.org/10.1007/BF02941010) · [Artin on conductors and discriminants](https://geodesic.mathdoc.fr/item/JRAM_1931__164_149742/) · [Hecke](https://geodesic.mathdoc.fr/item/NGWGMP_1917__1917_58995/) · [Tate, §3.5](https://www.math.ias.edu/~goresky/pdf/3-01Tate.pdf).

**First target-dependent obstruction.** The `supplyChi` lemma turns `VWinAt ψ 401` into `HostExW (3 / 2) (GChi ψ).req`. Its cyclotomic host test `IsChiField` requires \(E_{\rm host}\hookrightarrow\mathbb Q(\zeta_m)\) and describes its fixing subgroup by rational residue classes and scalar characters. All such subfields are abelian Galois, ruling out \(M\) and \(E\) as direct substitutions. For any \(m\), \(M\cap\mathbb Q(\zeta_m)\subseteq K\). The identity and a 3-cycle both restrict trivially to that intersection. Chebotarev in the compositum gives primes \(p\equiv1\bmod m\) with traces \(2\) and \(-1\). The required first Euler coefficients therefore cannot be encoded by rational Dirichlet residue classes. A replacement for the geometric construction would have to build the host and supply lemma using the cyclic cubic character on ideals of the quadratic resolvent, with their norms and ramified local factors. [supplyChi](https://github.com/Deicyde/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/CharacterBoxes/SupplyChi.lean#L8-L16) · [IsChiField and VWinAt](https://github.com/Deicyde/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean#L19-L49) · [Residue-class kernel](https://github.com/Deicyde/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/CharacterBoxes/TwistForm.lean#L9-L17).

**Sufficient replacement at the analytic interface.** Let \(\Lambda_\rho(n)\) be the coefficients of \(-L_\rho'/L_\rho\) and set
\[
G_\rho(y)=\sum_{n\le y}\Lambda_\rho(n)(y/n-1)+y\,\frac{L_\rho'}{L_\rho}(1).
\]
For each \(0<\varepsilon<1/52\), it suffices to prove that some \(C_{\rho,\varepsilon}>0\) satisfies
\[
\forall Y_0\ge2\ \exists Y\ge Y_0\ \forall y\in[Y,Y^{3/2}],
\qquad G_\rho(y)\le C_{\rho,\varepsilon}y^{1/2+\varepsilon}.
\tag{W}
\]
To verify the conditional implication, apply the pinned generic Landau theorem to the real function \(g(u)=G_\rho(e^u)=O_\rho(e^{2u})\) for \(u\ge0\). Its Laplace transform is
\[
\Phi(s)=-\frac{L_\rho'(s)}{s(s-1)L_\rho(s)}
              +\frac{L_\rho'(1)}{(s-1)L_\rho(1)} .
\]
The singularity at \(1\) is removable. The Dedekind zeta quotient gives \(L_\rho(1)>0\) by residues and nonvanishing on \(\Re s=1\) away from \(1\) by the classical Dedekind zeta nonvanishing theorem. The Euler product covers \(\Re s>1\). Each zero \(z\) in the open strip is a simple pole of \(\Phi\) with residue \(-\operatorname{ord}_z(L_\rho)/(z(z-1))\), positive for real \(z\). The zeros are discrete. On \([U,3U/2]\) for \(U=\log Y\), (W) supplies the majorant \(C_{\rho,\varepsilon}e^{(1/2+\varepsilon)u}\). Its integral against \(e^{-(1/2+\varepsilon)u}\) is \(C_{\rho,\varepsilon}U/2\le e^{\eta U}\) for every \(\eta>0\) on sufficiently late windows. The theorem yields \(\Re z\le1/2+\varepsilon\). Let \(\varepsilon\downarrow0\) and apply the functional equation. This application is by hand. (W) remains the new estimate. At fixed \(Q_\rho=23\), its constant and window choices may depend on \(\rho,\varepsilon\). A family version may impose \(C_{\rho,\varepsilon}\le C_\varepsilon Q_\rho^{A_\varepsilon}\) with independent constants. Any upper bound on where the next window occurs requires a separate quantifier. [Dirichlet window](https://github.com/Deicyde/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/PrimitiveCosets/Imports.lean#L8-L19) · [Generic hypotheses](https://github.com/Deicyde/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauZeroFreeCriterion.lean#L15-L29) · [Generic theorem](https://github.com/Deicyde/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauWindow.lean#L83-L84).

## 2. Fixed-\(N\) Goldbach long divisors

Use \(L=\log N,\ H=\sqrt N,\ \delta=1-\beta\), \(D=\lfloor\exp((\delta/64)L^\delta\log L)\rfloor\) and \(Y=\lfloor\exp(L^{\delta/2})\rfloor\). Let \(T_N(F)\) be the original ordered sum of \(-\mu(h)\mu(d)\log h\log\ell\) on \(qh+d\ell=N\). Keep \(q,h\in(H/2,H]\), the strict cofactor cutoff \(h>\lfloor H/2\rfloor\), the original middle intermediate-prime count mask, and \((qh,N)=1\). Require squarefree \(qh,d\ell\) with both Möbius signs \(-1\), no prime factor at most \(Y\) in \(d\ell\), and \(d,\ell\ge H/F>D\). The pinned reflection bound is \(\ll N(1+\log F)^2/\log Y\), giving \(o(N)\) for \(F=\exp((\log Y)^\eta)\) with \(0<\eta<1/2\). [Pinned GRH cutoff](https://github.com/Sodelin/Research-Commons/blob/4ad4701470274b6793bbcd352b1c9493733e7727/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/third-pass-two-boundaries.md) · [Pinned reflection bound](https://github.com/Sodelin/Research-Commons/blob/7d368fba264a6b9c05167ac1a4d8432a7205e39e/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/double-reflection-long-divisors.md) · [Baker–Harman](https://doi.org/10.1112/jlms/s2-43.2.193).

**Hand proof. Joint congruence estimate → exact inequality → longer range.** Uniformly at each even \(N\) for \(2\le F,\ \log F=O(\log Y),\ H/F>D\),
\[
 |T_N(F)|\ll N\,\frac{(1+\log F)^2}{(\log Y)^2}+N^{3/4+o(1)}.
\tag{1}
\]
Thus \(F=\exp((\log Y)^\eta)\) gives \(o(N)\) for every fixed \(0<\eta<1\). For example, \(\eta=3/4\) gives \(O(N/\sqrt{\log Y})\).

Orient each orbit by \(q<h,\ d<\ell\). Squarefreeness excludes equality. The two odd parities give orbit weight exactly \(-\mu(h)\mu(d)\log(h/q)\log(\ell/d)\), of size at most \(2\log 2\,\log F\). To upper bound the number of orbits, fix a rough \(d\in[H/F,H]\) coprime to \(N\), as forced by the support. For squarefree \(e\) made of primes at most \(Y\), count all block pairs with \(qh\equiv N\bmod de\). The joint estimate for \(e\le Y^{C'\log L}\), with \(C'\) fixed, is
\[
 A_e(d)=\frac{(H/2)^2\varphi(d)}{d^2}\prod_{p\mid e}g_N(p)+O(H^{1/2+o(1)}),
 \quad
 g_N(p)=
 \begin{cases}
 (p-1)/p^2,&p\nmid N,\\
 (2p-1)/p^2,&p\mid N.
 \end{cases}
\tag{2}
\]
Write \(e=e_0e_1\) with \(e_0=(e,N)\). For \(p\mid e_0\), expand \(1_{p\mid qh}=1_{p\mid q}+1_{p\mid h}-1_{p\mid q}1_{p\mid h}\). Rescale the intervals by the corresponding divisors of \(e_0\). The remaining congruences have unit right sides modulo \(r=de_1\). The rectangular Kloosterman estimate has main density \(\varphi(r)/r^2\) and error \(O_\epsilon(r^{1/2+\epsilon})\) for intervals of length at most \(r\). Full periods and a remainder cost \(H^{o(1)}\) since \(r\ge H/F\). The at most \(3^{\omega(e_0)}\) rescalings cost another \(H^{o(1)}\). The expansion and the CRT give the two displayed densities. [Estermann](https://doi.org/10.1112/S0025579300002187) · [Shparlinski, Theorem 13](https://arxiv.org/pdf/1103.2879).

Apply upper Bonferroni to exclude \(p\le Y\) from \((N-qh)/d\), truncating at even \(k\asymp C\log L\). There are at most \(Y^k=H^{o(1)}\) moduli, so the aggregate error per \(d\) is \(H^{1/2+o(1)}\). The density differs from \(\prod_{p\le Y}(1-g_N(p))\) by at most \((\sum_{p\le Y}g_N(p))^{k+1}/(k+1)!\). Since \(g_N(p)\le2/p\), the latter is \(O(L^{-A})\) for any fixed \(A\) by choosing \(C\) large. The product is \(O(1/\log Y)\) by Mertens and \(g_N(p)\ge 1/p-1/p^2\). The same truncation on a dyadic interval of scale \(X\ge H/(2F)\), with local density \(1/p\) and total floor error \(O(Y^k)\), counts \(O(X/\log Y)\) rough \(d\). Hence their reciprocal sum is \(\ll(1+\log F)/\log Y\). Sum the sieved (2) over \(d\) using \(\varphi(d)\le d\), then multiply by the orbit weight bound. This yields (1).

**Failed nonabelian inference.** Artin GRH here together with Dirichlet GRH gives effective single-prime splitting counts through \(\zeta_M=\zeta\,L(s,\operatorname{sgn})L_\rho^2\). The missing inference is from those counts to (2), a joint congruence on two moving variables that may be composite. The balanced support even forces \(d,\ell>1\), so it has no prime \(d\ell\) endpoint. [Lagarias–Odlyzko](https://websites.umich.edu/~lagarias/PUBLICATIONS/algebraic.html).

For a further conditional gain on the same sector, fix \(F=Y^c\), \(c>0\), and let \(U_N(s,t)\) sum \(\mu(h)\mu(d)\) on the original oriented support with \(\log(h/q)\ge s,\ \log(\ell/d)\ge t\). Then
\[
 T_N(F)=-\int_0^{\log 2}\int_0^{2\log F}U_N(s,t)\,dt\,ds .
\]
A fixed-\(N\) theorem \(\sup_{s,t}|U_N(s,t)|\le C N/(\log Y)^{1+\epsilon}\) gives \(|T_N(Y^c)|\le2cC(\log 2)N/(\log Y)^\epsilon\), improving the \(O(N)\) from (1) there. Such a theorem requires signed additive cancellation at the same target, which the single-prime estimate does not address.

**Numerical check.** 448 exact complete-residue comparisons passed for the local density in (2), using \(d\in\{11,13,17,121\}\), \(e\in\{1,2,3,5,6,10,30\}\), and even \(2\le N\le34\) coprime to \(d\). The asymptotic bound and Artin application above are hand arguments.
