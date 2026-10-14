# Exact nine-state quadratic certificate reduction and its diagonal-neutral obstruction

Contributor: Codex sol_interpolation_check lane, 14 October 2026.
Publisher: Codex lead G4 researcher.
Status: new hand algebraic reduction and scoped certificate obstruction, using inherited actual-source identities. One bounded rational sign countercheck is distinguished below. No ordinary cap-nine exclusion, exact return construction, fixed-cap master closure, or general G4 conclusion is proved.

## 1. Inherited source and what is new

Retain arbitrary finite strict natural private INDEPENDENT words, positive ordinary connectors, interior coins, unequal finite positive arms, opaque current-root routing, and one parameter tuple across arities. The inherited spectral representation is
\[
R(K)=
\begin{pmatrix}
b_9&X&Y&V\\0&b_7&0&U\\0&0&b_6&T\\0&0&0&b_4
\end{pmatrix}.
\]
A bare cell has positive diagonals \(p_j\), upper entries \(f,f\), lower entries \(-h+2e,h\), and V=0. In particular the exact append recurrence retains
\[
V'=Vp_4+(Y-X)h+2Xe.
\]
The old square decomposition, its two physical defects, selected-band cancellation examples, and fair-separated Green obstruction are inherited; they are not new results of this note.

The new step is an exact **per-cell three-by-three quadratic test**, including arbitrary ordinary-neutral diagonal coefficient/potential corrections. Actual diagonal completion then disproves this entire globally dissipative template when tested on unrestricted upper-state coordinates. This identifies precisely which extra state restriction a successful variant would have to supply.

Pinned providers:
- [Exact source-state interface](../../../2026-10-07-dot-g4-coupled-source-state-interface-0252z/METHOD-COMPARISON-AND-SOURCE-STATE.md): SHA256 7da5c426153438a70513dc7bf703f5ab77630831d4196bd6e83f718c4f75470f.
- [Strict exact f-zero cell arcs](../../../2026-10-08-codex-g3-g4-coordinated-1000z/g4-stopping/two-insertion/ACTUAL-LOWER-SELECTED-CANCELLATION.md): SHA256 ec2ee928996f18c1f6481270eb1d54460b8044a800d6c5b14dae67d687bd9f0f.
- [Full-rank ordinary diagonal returns](../../../2026-10-04-dot-g3-structure-followons-2200z/uniform-diagonal/UNIFORM-TIME-DIAGONAL-FINAL.md): SHA256 ab700065a7d0ed1a6ef5a680743ecffabdc24728325a1a58b70673d254c41905.

## 2. Exact normalized append and a finite-dimensional inequality

For a prefix define
\[
a=X/b_7,\quad b=Y/b_7,\quad v=V/b_4,
\]
and let \(z=(D_3,\ldots,D_9)\) be its seven ordinary-neutral logarithmic Newton diagonal defects. These defects add under composition and vanish at every ordinary kernel.

For the next bare cell put
\[
k=p_6/p_7>1,\qquad
l=\frac{b_9f}{b_7p_7},\qquad
s=\frac{b_7}{b_4p_4}>0,\qquad
\delta=(D_3(B),\ldots,D_9(B)).
\]
Every quantity comes from the same physical cell and actual prefix. Exact matrix multiplication gives
\[
a'=a+l,\quad b'=kb+l,\quad
v'=v+s[(-h+2e)a+hb],\quad z'=z+\delta.                 \tag{1}
\]
No rare-route expansion, lower-forest substitution, or independent tuning of f,h,e occurs here.

Consider the energy template
\[
F=v+c(z)(a^2-b^2)+\Phi(z),                             \tag{2}
\]
with arbitrary finite real-valued functions c and Phi, taking c>0 for the intended ordinary energy decrease. Write \(c'=c(z+\delta)\) and \(\Delta\Phi=\Phi(z+\delta)-\Phi(z)\). The l-squared terms cancel exactly. Thus
\[
\begin{aligned}
F'-F={}&(c'-c)a^2+(c-c'k^2)b^2\\
&+[2c'l+s(-h+2e)]a+[-2c'kl+sh]b+\Delta\Phi.           \tag{3}
\end{aligned}
\]
This is a specific source-coupled per-cell inequality; all body dependence remains in l and s.

Let
\[
L_1=2c'l+s(-h+2e),\qquad L_2=-2c'kl+sh.
\]
Requiring (3)<=0 for every real a,b is exactly the negative-semidefiniteness of
\[
M=
\begin{pmatrix}
c'-c&0&L_1/2\\
0&c-c'k^2&L_2/2\\
L_1/2&L_2/2&\Delta\Phi
\end{pmatrix}.                                      \tag{4}
\]
Indeed vectors (a,b,1) test every direction with nonzero last coordinate by scaling, and the remaining directions by limits. Equivalently, put \(r_1=c-c'\), \(r_2=c'k^2-c\). The exact Schur conditions are
\[
r_1,r_2\ge0,\qquad
\Delta\Phi+\frac{L_1^2}{4r_1}+\frac{L_2^2}{4r_2}\le0, \tag{5}
\]
where a zero denominator requires its numerator to vanish and contributes zero.

Appending an ordinary duration t leaves a,v,z unchanged and sends b to \(e^{6t}b\). Hence
\[
F'-F=-c(z)(e^{12t}-1)b^2.                            \tag{6}
\]
At identity and any ordinary endpoint, a=b=v=0,z=0, so (2) takes the same value. If (4) held along all actual prefixes, (2) would give a word-count independent telescoping certificate. Conditions (4)--(5) are stronger than mere endpoint equality: they demand global prefix dissipation.

## 3. Actual diagonal completion forbids this global template

**Claim.** No choice of c(z),Phi(z) can make (4) negative semidefinite for every actual prefix diagonal and every strict bare cell, while testing unrestricted a,b.

First, every prescribed strict cell can be included in a strict word with exactly ordinary diagonals through cap nine. To prove this, the inherited full-rank diagonal return supplies an open ball around zero in the actual defect image z. For a cell with defect delta choose an integer N sufficiently large that \(-\delta/N\) lies in that ball. Choose one strict finite word C realizing \(-\delta/N\). Concatenate positive pads, the prescribed cell, and N copies of C. Defect additivity makes its endpoint z=0. All factors remain actual, and its finite positive pair hazard selects its ordinary diagonal endpoint. This is a diagonal completion, not a full-forest return.

Negative semidefiniteness in (4) forces \(c(z+\delta)\le c(z)\) at every cell. Along the above diagonal cycle, ordinary pads do not change z, and the first and last c values agree. Therefore c must stay equal at every cell of that cycle, including the prescribed cell.

Now prescribe an inherited strict cell with
\[
f=0,\qquad -h+2e\ne0.                               \tag{7}
\]
Such cells are genuinely available: the exact f-zero arcs
\(B_\sigma(u)=B(1/2,\exp[-u z_\sigma(u)],u)\), u>0 sufficiently small, satisfy
\[
h=-12W_\sigma u^4+O(u^5),\qquad
e=-3W_\sigma u^4+O(u^5),
\]
with \(W_\sigma\ne0\). Thus \(-h+2e=6W_\sigma u^4+O(u^5)\ne0\). The cell has strict arms and an interior coin.

For this cell l=0 and c'=c. Matrix (4) has first diagonal entry zero but \(L_1=s(-h+2e)\ne0\). A negative-semidefinite matrix cannot have a nonzero off-diagonal entry in a row whose diagonal is zero. Equivalently, at b=0 equation (3) is a nonconstant linear function of a, regardless of DeltaPhi. Contradiction.

This argument allows **arbitrary** ordinary-neutral diagonal functions, not only an additive logarithmic correction. The obstruction uses actual source cells and the actual diagonal-return provider, rather than an arbitrary triangular-matrix substitution. Its force is limited to the unrestricted-state certificate requirement.

## 4. A bounded strict countercheck to a simpler local sign

One might instead try to make the extra defect sign-definite by the local inequality
\[
f\,J\ge0,\qquad J=2e-(1-p_7/p_6)h.                   \tag{8}
\]
The actual strict cell with arm survivals x=y=9/10 and g=1/10 disproves (8):
\[
f=
-\frac{43906291560714991394907138911013963}
{2502500000000000000000000000000000000000}<0,
\]
\[
J=
\frac{723282808177318233491398997379}
{52104028754540000000000000000000000}>0.
\]
Therefore fJ<0. Positive prefix and denominator factors cannot repair this local sign.

These are exact rational evaluations of the inherited current-root ordinary-EPPF formula, using the unchanged evaluator [exact_source_defects.py](../../../2026-10-08-codex-g3-g4-coordinated-1000z/g4-stopping/two-insertion/exact_source_defects.py), SHA256 a0c6b0aa8220cdbc246d2189d7c6f6e9aec7c0b6a5647dd071a27d7a1102e47b. A bounded six-fixture diagnostic motivated this one displayed countercheck; it was not a full-fibre search. No fixture is claimed to satisfy ordinary endpoint equations. This calculation only refutes the stated pointwise shortcut.

## 5. What remains open after the attempt

Full ordinary equality through cap nine certainly gives a=b=v=0 and all diagonal defects zero at the endpoint. It does **not** make intermediate a,b freely variable, so Section 3 does not rule out a valid certificate on a newly proved actual-prefix cone. Additional T/U bands, unselected forest rows, or source-history constraints could define such a cone. No such cone has been supplied here.

The no-go also does not cover coefficients depending on elapsed pair time, nonordinary-neutral diagonal variables, the full lower-state history, or higher/nonquadratic terms. An elapsed-clock-dependent coefficient can decrease around a diagonal-neutral cycle and evade the monotonicity argument; its finite target budget would need separate control.

Thus the general 2Xe term has not been killed by matching additional rows. The new rigorous reduction is (3)--(5), and the new scoped obstruction is that all ordinary-neutral diagonal corrections within (2) fail the global unrestricted-prefix test. A source-specific constrained inequality must use information absent from this template. This is a materially more explicit certificate gate, not an exclusion of arbitrary finite words.
