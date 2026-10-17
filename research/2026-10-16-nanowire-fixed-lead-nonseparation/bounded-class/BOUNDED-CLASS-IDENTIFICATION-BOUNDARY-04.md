# Bounded-potential identification: an explicit contact bound and the exact remaining energy question

**Date:** October 17, 2026, 00:58 UTC. **Author:** dot, working with Nolan. **Status:** source-bound hand-proof draft for independent review. No numerical solver, SMT decision, Lean build, or new physical experiment is claimed. The compactness, perturbation and real-algebraic ingredients are classical; historical novelty is not established.

## What this establishes

For the same finite Rashba wire and fixed leads as the accepted nonseparation theorem, a hard bound on every scalar onsite potential gives an explicit uniform bound on the zero-energy open-wire inverse. Consequently the visibility cannot change by a fixed margin under arbitrarily small changes of those bounded potential vectors.

That is **not** an inverse estimate from energy measurements. On a closed bounded potential class, arbitrarily close complete lowest-energy curves with opposite fixed visibility margins exist if and only if an exactly equal pair of such curves exists. Whether that collision occurs in a substantial bounded class of these wires is not settled here.

This draft also gives an explicit field-grid approximation bound and an exact real-algebraic decision reduction. Together they identify the unresolved source-specific question without assuming injectivity, changing the target, or replacing one physical device by separately fitted devices at different fields.

The bounded class is an expressly restricted class. It does not replace or weaken the already proved [unbounded-potential theorem](https://github.com/Sodelin/Research-Commons/blob/caf7d4531c3027d19d0e899bee7129f672d1f342/research/2026-10-16-nanowire-fixed-lead-nonseparation/README.md). Original Taylor implementation admission remains open.

## 1. Fixed physical contract and notation

Retain the accepted model, with N = 60, length 0.6 μm, pairing Δ = 1/5 meV, spin-orbit hopping λ = 5/2 meV, a single fixed hopping t in the previously certified interval, and zero internal dissipation. At every field B in [0,Bmax], Bmax = 2 meV,

\[
H(a,B)_{jj}=a_j\tau_z+B\sigma_x+\Delta\tau_x,
\qquad H_{j,j+1}=T=-t\tau_z-i\lambda\sigma_y\tau_z.
\]

The lower block is T†. The real vector a is held fixed throughout the field sweep. Scalar disorder is V_j = a_j − (2t−1), so a hard disorder bound |V_j| ≤ Vmax implies |a_j| ≤ A := |2t−1| + Vmax. The results below apply to a specified closed subset C of the box [−A,A]^N; they do not assume all such subsets describe realistic fabrication.

The normal leads and contacts remain exactly those of the accepted theorem. At zero energy their self-energy is −iγI at either endpoint, with **γ = 1 meV fixed**. Keeping the symbol γ in intermediate inequalities only records units; no lead parameter is varied. Let Π = ΠL + ΠR, K(a,B) = −H(a,B) + iγΠ, and G = K^−1. Then

\[
r_L=I_4-2i\gamma G_{LL},\qquad Q(a)=\det r_L(a,B_*),\qquad B_*=2.
\]

Particle-hole symmetry makes Q real. Full two-lead scattering is unitary, so r_L is a contraction, though generally not unitary itself. This can also be checked directly: for the endpoint embedding W with WW† = Π, S = I − 2iγW†G W is unitary by the resolvent identity G − G† = −2iγGΠG†. These are the previously used scattering conventions, not an authenticated reconstruction of Taylor's unpublished transport code.

The observation is F(a)(B) = s_min(H(a,B)), the lowest nonnegative BdG energy. Let m > 0 be a fixed visibility margin and define

\[
C_- = \{a\in C:Q(a)\le -m\},\qquad
C_+ = \{a\in C:Q(a)\ge m\}.
\]

The classification claims below concern their union. If either class is empty, its absence must be established and classification on the remaining class is trivial. We assume both classes nonempty when defining a two-class separation distance.

## 2. Explicit uniform inverse bound under bounded potentials

All matrix norms here are Euclidean operator norms; vector norms are Euclidean. Put

\[
\tau=\sqrt{t^2+\lambda^2},\quad C_0=A+B_{\max}+\Delta,\quad
R=2+(C_0+\gamma)/\tau,\quad d=\lfloor(N-1)/2\rfloor,
\]
\[
\rho=\min\left\{\frac{\tau^2}{\gamma},\frac{\gamma}{4NR^{2d}}\right\}>0.
\]

**Claim.** For every a in [−A,A]^N and every allowed B,

\[
s_{\min}(K(a,B))\ge\rho,\qquad \|G(a,B)\|\le\rho^{-1}. \tag{1}
\]

**Proof.** T T† = T†T = τ²I, so inversion of either hopping block has norm 1/τ. Take any vector x with norm one, write its site blocks as x_j, set y = Kx and ε = ||y||. The imaginary quadratic form gives

\[
\gamma(\|x_1\|^2+\|x_N\|^2)
 =\operatorname{Im}\langle x,y\rangle\le\varepsilon.
\]

Thus either endpoint has norm at most sqrt(ε/γ). Set a_0 = (C_0+γ)/τ and u = sqrt(ε/γ) + ε/τ. The block equation, with x_0 = 0, implies

\[
\|x_{j+1}\|\le a_0\|x_j\|+\|x_{j-1}\|+\varepsilon/\tau.
\]

The endpoint damping has been bounded by γ even at interior sites, which only enlarges this bound. Induction gives ||x_j|| ≤ R^(j−1)u: the first step uses a_0+1 ≤ R, and subsequent steps use a_0+1/R+R^(−(j−1)) ≤ a_0+2 = R. Propagating from the right endpoint gives the corresponding bound R^(N−j)u. Therefore every site has norm at most R^d u, and

\[
1\le\sqrt N R^d(\sqrt{\varepsilon/\gamma}+\varepsilon/\tau).
\]

If ε ≤ τ²/γ, then ε/τ ≤ sqrt(ε/γ), giving ε ≥ γ/(4NR^(2d)). If ε > τ²/γ, it already exceeds the other member of the displayed minimum. Thus ε ≥ ρ for every unit x, proving (1). In particular K is invertible uniformly. ∎

This estimate is deliberately conservative and can be extremely small. For the finite example's fixed hopping and the onsite box A = 1000 meV, one may weaken it to the entirely rational lower bound 1/(240·43^58) meV. This is a mathematical conditioning guarantee, not a useful laboratory energy resolution.

### Consequence for parameter changes, not for inverse energy recovery

For two potential vectors a,b in the box, the inverse identity and the diagonal perturbation norm give

\[
\|r_L(a)-r_L(b)\|\le 2\gamma\rho^{-2}\|a-b\|_\infty.
\]

For two 4 × 4 contractions, replacing their columns one at a time and applying Hadamard's inequality gives |det r − det s| ≤ 4||r−s||. Hence

\[
|Q(a)-Q(b)|\le 8\gamma\rho^{-2}\|a-b\|_\infty. \tag{2}
\]

An opposite-margin pair consequently satisfies

\[
\|a-b\|_\infty\ge \frac{m\rho^2}{4\gamma}. \tag{3}
\]

Equation (3) excludes the accepted asymptotic construction's combination of bounded parameters, vanishing parameter difference and fixed visibility difference. It **does not** imply an energy-curve gap: two separated parameter vectors may have equal energy observations. Reversing the one-sided spectral perturbation inequality would be invalid.

## 3. Exact collision versus positive-error identification

For any a,b and fields B,B′, the singular-value variational inequality gives

\[
|F(a)(B)-F(b)(B')|\le\|a-b\|_\infty+|B-B'|. \tag{4}
\]

Indeed the onsite change has norm ||a−b||∞ and the Zeeman change has norm |B−B′|. Taking the minimum of ||Hx|| over unit x proves the singular-value inequality directly; no separation of individual eigenvalue branches is required.

Since C is compact and Q is continuous by Section 2, C− and C+ are compact. The map F into continuous functions with their supremum norm is continuous by (4). Thus

\[
\delta_{\rm full}=\min_{a\in C_-,\ b\in C_+}\ \sup_{0\le B\le B_{\max}}
 |F(a)(B)-F(b)(B)| \tag{5}
\]

is attained. In particular:

1. δ_full = 0 if and only if some opposite-margin pair has exactly equal lowest-energy curves at every field.
2. δ_full > 0 if and only if there is no such pair.
3. A deterministic rule correct for every device in C− ∪ C+ and every additive observation error with supremum norm at most ε exists exactly when δ_full > 2ε. This statement includes ε = 0 and uses closed error balls.

For item 3, two opposite-class error balls overlap if the curve distance is at most 2ε, because their midpoint is a common observation. When δ_full > 2ε all opposite-class balls are disjoint, so their class membership defines a correct rule on their union; extend it arbitrarily outside that union. Conversely an attaining pair at distance at most 2ε forces conflicting answers at its midpoint. The existence claim alone is not an efficient reconstruction algorithm.

The distinction from the unbounded theorem is exact: compactness prevents a nonattained zero separation from arising solely by escape to infinite barriers. It does not prove that equal-curve collisions are absent.

## 4. A quantitative bridge from a full field interval to a finite menu

Let B_0 = 0 < B_1 < ... < B_J = Bmax be a fixed endpoint-inclusive grid with maximum spacing h. Define δ_grid by replacing the supremum in (5) by the maximum over this grid. Then

\[
\delta_{\rm grid}\le\delta_{\rm full}\le\delta_{\rm grid}+h. \tag{6}
\]

For a fixed pair, the absolute curve difference is 2-Lipschitz by (4). Every field is within h/2 of a grid point, so its value is at most the grid maximum plus h. Minimizing this pointwise pair inequality proves (6).

Consequences:

- If a grid certificate proves δ_grid > 2ε, the full curves and that grid both identify the label at radius ε.
- A lower bound δ_full ≥ d_0 > 2ε yields a sufficient mesh condition h < d_0−2ε.
- There exists some finite grid with δ_grid > 2ε if and only if δ_full > 2ε. For rational/algebraic Bmax, equal subdivisions give an effective enumerable family of grids.
- A particular menu has its own δ_grid. Existence of a finer separating menu does not establish separation for a pre-existing 512-setting experiment or assert that extra settings are experimentally accessible.

The earlier theorem controls the full curve, and therefore every fixed menu. No recovery of Taylor's exact field list is claimed here. Calibration and model errors can be included in ε only if actual uniform error bounds justify that budget.

## 5. Exact real-algebraic decision formulation

Assume the fixed physical constants, Bmax, B*, margin m and error ε are rational or real algebraic, and C has a specified finite semialgebraic description. Fix N; no countably infinite or arbitrary-dimensional source class is introduced.

In the stated basis H is real symmetric and polynomial in a,B. The following finite polynomial conditions specify its lowest nonnegative BdG energy uniquely:

\[
\mathrm{Low}(a,B,e):\quad e\ge0,\quad
\det(H(a,B)^2-e^2I)=0,\quad H(a,B)^2-e^2I\succeq0. \tag{7}
\]

The positive-semidefinite condition can be written as nonnegativity of all principal minors. It is finite, although potentially enormous. It is not enough to require an arbitrary eigenvalue equation: (7) specifically selects the smallest absolute energy.

To encode Q, introduce real and imaginary parts of G, impose KG = I, form r_L, and impose q = Re det r_L and Im det r_L = 0. Section 2 proves that this inverse is unique and that no singular solutions have been introduced. PHS supplies the reality identity. All these are polynomial relations over the real algebraic coefficients; the labels are q ≤ −m and q ≥ m.

For a finite field menu, the exact question whether opposite error balls overlap is the existential real formula

\[
\exists a\in C_-,\ b\in C_+\quad
\bigwedge_j\exists e_j,f_j\;[
\mathrm{Low}(a,B_j,e_j)\land\mathrm{Low}(b,B_j,f_j)
\land |e_j-f_j|\le2\varepsilon]. \tag{8}
\]

For the full field interval it is

\[
\exists a\in C_-,\ b\in C_+\quad
\forall B\in[0,B_{\max}]\quad\exists e,f\;[
\mathrm{Low}(a,B,e)\land\mathrm{Low}(b,B,f)
\land |e-f|\le2\varepsilon]. \tag{9}
\]

The potential vectors are quantified **before** B and remain shared across all settings. The energies are uniquely fixed by (7). Moving the potential quantifiers inside the field quantifier would ask a different, physically invalid question. Setting ε = 0 in (9) asks for an exact full-curve collision.

Classical effective quantifier elimination for real closed fields decides (8) and (9), including the emptiness checks for the two source classes. This follows from the Tarski–Seidenberg theorem and its effective algorithms; see [Saugata Basu, *Algorithms in Real Algebraic Geometry: A Survey*, §2.1, Theorem 2.1 and §2.1.1](https://www.math.purdue.edu/~sbasu/raag_survey2011_final.pdf). This is a standard theorem applied to a fully specified finite model, not a new decision-theory result. It makes no claim of feasible runtime for a 240-dimensional BdG matrix.

An exact solver's certified answer to these formulas would settle the corresponding bounded-model question. No such answer has been obtained here. A timeout, UNKNOWN, numerical optimizer, or approximate δ-satisfiability result alone would not establish either exact collision or global separation.

## 6. What can already be said for a concrete bounded box

The [published finite pair](https://github.com/Sodelin/Research-Commons/blob/b6b1f91d84e58506b9028dec1ff0c59e05317224/research/2026-10-16-nanowire-fixed-lead-nonseparation/finite-example/README.md) belongs to the onsite box A = 1000 meV, with its fixed rational hopping t = 25.08215 meV. These two specific profiles also lie in the disorder box Vmax = 950.8357 meV; this is not an equivalence of the two whole boxes. Its two margins exceed m = 0.1, and

\[
\delta_{\rm full}\le 0.00009999\ \mathrm{meV}=0.09999\ \mu\mathrm{eV}.
\]

Therefore no uniformly correct classifier on this box exists at closed energy-error radius ε ≥ 0.000049995 meV = 0.049995 μeV. This is an immediate bounded-class consequence of the already certified pair, not a new computation. The barrier magnitude is a mathematical example; physical feasibility and typical-device frequency have not been established. It gives no answer for every smaller positive error, or for a smaller physically motivated box that excludes the pair.

## 7. Decisive next condition and attribution

For a specified physically admitted hard potential class, the decisive missing condition is now explicit: either prove an opposite-margin equal-energy-curve collision, or prove its absence and obtain a quantitative positive separation. The latter would permit finite measurement extraction via (6), but no positivity result is assumed. Recovering the original lead/disorder implementation would still be needed before applying any of these declared-model conclusions to the Taylor data.

The closest physical novelty comparison remains [the published directed prior audit](https://github.com/Sodelin/Research-Commons/blob/f174251a09468254c778a1136ed5b975173fc378/research/2026-10-16-nanowire-fixed-lead-nonseparation/NOVELTY-COMPARISON-20261017.md): known resonance-width physics, a verified specific realization, and unresolved historical novelty. The boundary-propagation estimate above is elementary finite-matrix analysis. Compactness, spectral Lipschitz continuity, midpoint error-ball logic, mesh approximation and quantifier elimination are classical. Their application here clarifies what a bounded physical claim would require; it is not a new general physics result or a solution of the original implementation-admission gap.
