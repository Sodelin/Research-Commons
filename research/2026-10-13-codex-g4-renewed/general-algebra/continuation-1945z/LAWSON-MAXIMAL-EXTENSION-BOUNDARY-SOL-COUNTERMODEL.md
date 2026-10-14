# Maximal semigroup extension need not preserve an ordinary boundary

Contributor: Codex sol_interpolation_check lane, 14 October 2026.
Publisher: Codex lead G4 researcher.
Evidence: independent hand proof and direct reading of the Lawson publisher PDF. No actual-source counterexample, historical novelty claim, or G4 conclusion is asserted.

**Result.** Even in the simply connected positive affine group, every maximal proper semigroup containing a source-like semigroup can place every positive ordinary point in its interior while the smaller closed semigroup keeps an arbitrarily long initial ordinary interval on its boundary. Signed-time saturation, primitive translation signs, actual open patches approaching identity, full diagonal rank, and affine-convex interior do not repair this inference.

## 1. Exact primary theorem and its limitation

The inherited [signed-time packet](../../../2026-10-08-dot-g4-signed-time-saturation-0925z/LAWSON-PRIMITIVE-CONE-AND-SIGNED-TIME-SATURATION.md) was read first; its SHA256 is bfd5ba075f2a4e4add0bbadca6f78802fa3c039e877009bdd03b3982e185e082. Its explicit distinction between signed saturation and positive-time interior is correct.

J. D. Lawson, [Maximal subsemigroups of Lie groups that are total](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/7C6AC5D4A2BEEAF0F2F2BF7306DE98CA/S0013091500026870a.pdf/maximal_subsemigroups_of_lie_groups_that_are_total.pdf), Proceedings of the Edinburgh Mathematical Society 30 (1987), 479–501, DOI 10.1017/S0013091500026870, was read directly at Proposition 5.2 and Proposition 5.4, journal page 486, and Corollary 11.2, journal page 496. Downloaded publisher PDF SHA256: f73c934c4c717e2bdb70a680c498c57dd3a8377e99ecc93d672c50d33aecc328.

Proposition 5.2 states that a proper subsemigroup with nonempty interior is contained in a maximal subsemigroup. Proposition 5.4 makes that maximal extension closed. Corollary 11.2 classifies the reduced pair of a maximal semigroup with interior in a finite-dimensional connected solvable group as the real-line or positive-affine half-space pair. None of these statements retains a designated boundary point of the smaller semigroup. The following example proves that a boundary-preserving extension cannot be added as a general theorem.

## 2. A source-like affine semigroup with arbitrary threshold

Write the positive affine group in coordinates
\[
G=\mathbb R\ltimes\mathbb R,\qquad
(t,y)(s,z)=(t+s,y+e^{-t}z).
\]
It is connected, simply connected and solvable. Ordinary evolution is \(E_t=(t,0)\). Conjugation contracts translations:
\(E_t(0,y)E_{-t}=(0,e^{-t}y)\).

Fix an arbitrary threshold \(R>0\). Define the strict semigroup
\[
S_R=\{(t,y):t>0,\ y\ge0\}\ \cup\
    \{(t,y):t>R,\ y\in\mathbb R\}.
\]
Its closure is
\[
C_R=\{(t,y):t\ge0,\ y\ge0\}\ \cup\
    \{(t,y):t\ge R,\ y\in\mathbb R\}.
\]
Both are semigroups. If any factor belongs to the unrestricted-translation part, the sum of time coordinates exceeds the corresponding threshold; otherwise the translation coordinate is a sum of nonnegative terms with positive coefficients. The displayed closed set is exactly the closure.

All positive ordinary points lie in S_R. Nevertheless E_H is on the boundary of C_R for every \(0<H\le R\): arbitrarily close points with time below R and negative translation are missing. For \(H>R\), E_H is an interior point of S_R. Thus R is an exact, freely adjustable positive-time interior threshold.

The open region \(t>0,y>0\) gives analytic regular parameter patches in S_R accumulating at identity. The primitive affine cocycle \(c(t,y)=y\), with weight \(\chi(t,y)=e^{-t}\), takes both signs on strict elements. The positive ordinary ray is interior in its one-dimensional diagonal cone; varying t at any E_H gives full diagonal differential rank.

Signed-time saturation is exact and uses two factors: given \((t,y)\in G\), take any \(s>R\), so that \((s,y)\in S_R\), and write
\[
(t,y)=(s,y)E_{t-s}.
\]
Hence adjoining all real ordinary times generates all of G by finite products.

## 3. The unique maximal extension erases this boundary

The half-space
\[
M=\{(t,y):t\ge0\}
\]
is a proper closed semigroup containing C_R, and every E_H with H>0 is interior in M.

In fact M is the **unique** maximal proper supersemigroup of C_R, without invoking Lawson. Suppose a supersemigroup T contains an element \(p=(t_p,y_p)\) with \(t_p<0\). For any target \(g\in G\), choose an integer k large enough that the time coordinate of \(p^{-k}g\) is at least R. Then \(p^{-k}g\in C_R\), because that part admits every translation. Although \(p^{-k}\) need not belong to T, the element \(p^{-k}g\) does belong to T by this membership test. Therefore \(g=p^k(p^{-k}g)\in T\). Thus T=G.

Every proper supersemigroup consequently lies inside M, so maximality forces it to equal M. This proves directly that no maximal extension preserving E_H on its boundary exists for \(0<H\le R\).

## 4. Affine-convex interior also survives

Use the fixed matrix coordinates
\[
(t,y)\longmapsto
\begin{pmatrix}a&y\\0&1\end{pmatrix},\qquad a=e^{-t}.
\]
The affine hull is two-dimensional and
\[
\operatorname{conv}(S_R)=\{(a,y):0<a<1,\ y\in\mathbb R\}.
\]
For a prescribed a in (0,1), choose
\(0<a_L<\min(a,e^{-R})\) and \(a<a_U<1\).
A convex combination of these diagonal coordinates equals a. The lower-a source point permits an arbitrary translation, while the upper-a source point can have translation zero, so the same combination realizes any prescribed y. Conversely every strict source has 0<a<1. In particular **every** E_H, H>0, is in the relative interior of the actual affine convex relaxation. This is an affine statement about matrix entries, not a convexity assertion in logarithmic coordinates.

Thus the counterexample retains this additional inherited source property as well. Its unrestricted negative-translation region comes at a time cost R that the qualitative hypotheses do not bound.

## 5. Precisely which inference fails

The proposed implication
\[
E_H\in\operatorname{int}(M)\text{ for every maximal proper }M\supseteq C
\quad\Longrightarrow\quad
E_H\in\operatorname{int}(C)
\]
is false. The example even has only one such maximal extension.

The later promotion from closure interior to actual interior does hold if actual interior points accumulate at identity. Indeed, for \(g\in\operatorname{int}(\overline S)\), take \(a\in\operatorname{int}(S)\) sufficiently close to identity that \(ga^{-1}\in\operatorname{int}(\overline S)\). Approximate \(ga^{-1}\) by an element s of S. Then \(s^{-1}g\) is sufficiently close to a to lie in an open subset U of S containing a, and \(g\in sU\subseteq\operatorname{int}(S)\). The failure occurs at the maximal-extension inference, before this valid promotion.

The countermodel is not an admitted coalescent source. It does not disprove actual ordinary interior or positive return membership. It shows that Lawson classification plus the listed qualitative source properties supplies no boundary-preserving maximal extension and no quantitative positive-time clearing bound. Any actual-source conclusion needs an additional source-specific argument.
