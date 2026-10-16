# Fixed-lead positive-margin nonseparation: a finite Rashba-chain candidate

**Date:** 2026-10-16, 22:53 UTC. **Status:** candidate hand proof with an executed exact-rational finite-matrix certificate; independent review pending. No Lean verification. No claim of novelty, an error in a paper, or an authenticated counterexample to the authors' undisclosed transport implementation.

## Result and remaining source boundary

For the explicitly specified 60-site, zero-dissipation Rashba chain below, with the **same fixed normal leads in every instance**, the two visibility classes TV(2) ≤ −1/10 and TV(2) ≥ 1/10 have zero separation in the supremum norm of the **entire closed-wire lowest-energy curve** on 0 ≤ B ≤ 2 meV. Length, hopping, pairing, spin-orbit coupling, lead parameters and the field menu are fixed. Each candidate uses one onsite-potential vector at every field. This remains a positive-margin statement; it does not use a topological label's discontinuity at a bulk phase boundary.

The construction gives arbitrarily close energy observations, not exactly equal noiseless curves. It rules out uniform identification under any positive adversarial energy-error radius for this declared unbounded-potential class. It does not give an average-case error rate.

**Application to Taylor–Pan–Das Sarma remains conditional on source admission.** Their Eq. (2), Table 1 and Appendix I.2 specify the Rashba wire, zero dissipation and 512 energy inputs in [0,2]. The inspected public text does not authenticate their lead Hamiltonian/contact matrix, the exact field list, or whether their disorder generator truncates or renormalizes individual realizations. The present lead convention is explicitly declared rather than attributed to their code. Gaussian full support is a sufficient admission condition, not a fact established by recovering their source. [Taylor et al., v2](https://arxiv.org/html/2512.13825v2)

This is a finite-wire **reflection-visibility** statement. MEDA predicts the periodic-disorder invariant from conductances, a different observation and target. No MEDA failure theorem follows here. [MEDA, v2](https://arxiv.org/html/2607.26208v2)

## 1. Exact microscopic model

Use spin ⊗ particle-hole ordering and Pauli matrices σ and τ. A wire of N = 60 sites has onsite and upper-neighbor blocks

\[
H_{jj}=a_j\tau_z+B\sigma_x+\Delta\tau_x,
\qquad T=-t\tau_z-i\lambda\sigma_y\tau_z,
\]

with lower-neighbor block T†, Δ = 1/5 meV, λ = 5/2 meV, and any fixed

\[
t\in[25.08210,25.08220]\ \mathrm{meV}.
\]

Take a lattice spacing of 10 nm and length convention Na = 0.6 μm. In the usual discretization a_j = 2t − μ + V_j, with μ = 1 meV, so every onsite vector below is implemented by a scalar disorder vector V. The Table 1 mass 0.01519 m_e gives t ≈ 25.0821732 meV under the standard ℏ²/(2m*a²) conversion; α = 0.5 eVÅ gives λ = α/(2a) = 2.5 meV. The certificate covers a hopping interval rather than silently substituting 25. [NIST constants](https://physics.nist.gov/cuu/Constants/Table/allascii.txt)

Attach an identical, fixed normal lead to site 1 and site 60. A concrete realization is a semi-infinite spin-degenerate normal tight-binding chain with zero onsite energy, lead hopping −τ_z meV and contact hopping −τ_z meV. At E = 0 each lead's retarded self-energy is exactly −i I_4 meV. All lead parameters remain fixed as M or the central potential changes. Equivalently, the zero-energy retarded inverse is

\[
-H+i\Pi_L+i\Pi_R,
\]

where Π_L, Π_R are the four-dimensional endpoint projectors. The reflection convention is fixed by TV → +1 for a decoupled hard wall. The determinant identity for left reflection is

\[
\operatorname{TV}=\frac{\det(-H-i\Pi_L+i\Pi_R)}
 {\det(-H+i\Pi_L+i\Pi_R)}. \tag{1}
\]

It follows from r_L = I_4 − 2i P_L(-H+iΠ_L+iΠ_R)^{-1}P_L† and the matrix determinant lemma. A channel phase convention consistent with particle-hole symmetry has the same determinant. The denominator is nonzero: a zero vector would vanish on both endpoints by its imaginary quadratic form, then on all sites because T is invertible. Particle-hole symmetry makes TV real.

Set a_1 = a_60 = M, with M positive and eventually large. All 58 central onsite coefficients are equal to a. There is no change of a, M or any physical parameter while sweeping B.

## 2. Certified central crossing at B* = 2

At B* = 2, the real Hamiltonian anticommutes with the real symmetric chiral operator S = σ_y τ_y. An orthogonal chiral decomposition of the isolated 58-site central segment gives

\[
H_c\sim\begin{pmatrix}0&A\\A^T&0\end{pmatrix}.
\]

The 116 × 116 real matrix A has diagonal blocks

\[
O(a)=\begin{pmatrix}a&-B_*+\Delta\\B_*+\Delta&-a\end{pmatrix},
\]

upper blocks U = [[−t, λ],[λ,t]] and lower blocks L = [[−t,−λ],[−λ,t]]. These are obtained directly from the stated microscopic Hamiltonian, rather than postulating a two-mode Hamiltonian.

The persisted certificate covers

\[
t=t_0+v,\quad t_0=25.08215,\quad |v|\le 0.00005,
\]
\[
a=x+2v,\quad |x-x_0|\le 0.0001,\quad x_0=49.367901053229.
\]

Delete zero-based row 8 and column 107 from A to obtain M_0(x,t). The certificate stores a rational approximate inverse R at the box center. All acceptance comparisons use exact Python fractions; floating-point eigensolvers were used only to propose the center and R.

For this whole box the checked bounds imply:

- the minor is invertible, with operator inverse norm < 4.565;
- its scalar Schur complement F has ∂F/∂x > 26.187;
- |∂F/∂t| < 3.863, where this derivative holds x fixed and therefore differentiates a = x + 2v;
- |F(x_0,t_0)| < 2.847 × 10^−10;
- F has opposite signs on the two x faces, uniformly in t.

Hence every allowed t has one root a_0(t) in this tube. The rank of A there is exactly 115. The full central BdG Hamiltonian has a **two-dimensional zero subspace**, with one null vector of each chirality. “Simple crossing” here means the scalar Schur/Pfaffian-parity crossing is transverse, not that a BdG zero eigenvalue has multiplicity one.

Let p and q be normalized real chiral null vectors, and define

\[
\ell=\|p_L\|^2,\quad r=\|p_R\|^2,
\quad s=p^TDq,\quad D=\operatorname{diag}(1,-1,\ldots,1,-1).
\]

Reflection combined with σ_x commutes with H_c and interchanges its two chiral subspaces. Consequently q is the reflected p up to sign: q_L has squared norm r and q_R has squared norm ℓ. Local endpoint projection commutes with chirality, so it has no p–q off-diagonal matrix element.

The exact certificate gives

\[
\frac{\ell-r}{\ell+r}>0.3905595,\qquad |s|>0.9439722,
\]
\[
4.8165<(t^2+\lambda^2)(\ell+r)<5.2758. \tag{2}
\]

The displayed decimals are outward-weakened summaries; the saved result contains the exact rational bounds. In particular this is a certified nonzero endpoint polarization, not a visual localization claim.

### What the rational checker proves

Write A = [[a_ij,r_0],[c_0,M_0]] after the selected row/column permutation. From ||I−RM_0(center)|| ≤ e and ||R|| ≤ K it checks e + Kρ < 1, with ρ = 0.0003 bounding the full operator perturbation. Neumann's lemma bounds M_0^−1 throughout the box. Residual bounds enclose the exact null-vector candidates with fixed coordinates p_i=q_j=1. The identities

\[
\partial_z F=p^T(\partial_z A)q
\]

then give the derivative bounds. The checked face inequality is

\[
(\inf F_x)\,0.0001>(\sup|F_t|)\,0.00005+|F(center)|.
\]

Endpoint squared norms and normalized crossing velocity are enclosed using these vector-error bounds. Matrix operator norms are bounded by the larger of their exact row-sum and column-sum norms. No floating-point residual is used as an acceptance test.

## 3. Add the physical barriers without assuming an effective model

Put z = 1/M. The two barrier onsite blocks are Mτ_z + B*σ_x + Δτ_x. Their inverses are analytic in z near zero after extracting z. Eliminating the two barriers by an exact Schur complement gives the isolated central matrix plus an analytic O(z) correction.

Because the central scalar root is transverse, the real implicit-function theorem supplies a real central onsite value a(z), with a(0)=a_0(t), for which the **closed full 60-site Hamiltonian** has the two-dimensional zero subspace at B*. The selected minor stays invertible. Reflection and chiral symmetries are retained. This tuning is performed once for a device; a(z) is then fixed over the complete field sweep.

Now compare two devices with the same barriers and leads but central coefficients

\[
a_-(M)=a(1/M)+\frac{0.01}{M^2},\qquad
 a_+(M)=a(1/M)+\frac{100}{M^2}. \tag{3}
\]

All energies in this construction are numerical values in meV, so the constants in the numerators carry the corresponding cubic energy unit. Both branches have nonzero small closed-wire splitting for sufficiently large finite M, by transversality. Neither branch is the exact zero-crossing point.

The two closed matrices differ only on the central onsite blocks. Therefore

\[
\sup_{0\le B\le2}\|H_+(B)-H_-(B)\|=
\frac{99.99}{M^2}<\frac{100}{M^2}. \tag{4}
\]

For E_s defined as the smallest absolute eigenvalue (the lowest nonnegative BdG energy), singular-value perturbation gives

\[
\sup_{0\le B\le2}|E_s^+(B)-E_s^-(B)|<\frac{100}{M^2}. \tag{5}
\]

This is an exact operator inequality and covers every fixed 512-point field menu, or even the entire field interval. There is no pointwise refitting or independently selected disorder at different fields.

## 4. Exact scattering asymptotics retain the visibility margin

For a barrier block B_M, changing its closed inverse to the inverse with the fixed lead self-energy changes the central Schur complement by

\[
+i(t^2+\lambda^2)z^2 I_4+O(z^3)
\]

at that inner endpoint. This follows from the inverse identity and T T† = (t²+λ²)I. Reversing the sign of the left lead's imaginary term reverses this leading term. Thus it applies to both numerator and denominator of (1).

On the two-dimensional central zero subspace, divide the Schur complement by z². The closed-wire perturbation c z² produces off-diagonal coefficient sc, and the fixed physical lead terms produce diagonal widths (t²+λ²)ℓ and (t²+λ²)r. All other central modes are separated from zero and can be Schur-eliminated; their corrections to this scaled two-dimensional block tend to zero. Barrier determinant factors and the eliminated nonzero-mode determinant factors cancel in the ratio in (1).

Set

\[
g=(t^2+\lambda^2)(\ell+r),\qquad
 d=(t^2+\lambda^2)(\ell-r).
\]

The resulting limit is therefore

\[
\lim_{M\to\infty}\operatorname{TV}_{c}(B_*)
 =\frac{s^2c^2-d^2}{s^2c^2+g^2}. \tag{6}
\]

This expression is obtained from the microscopic determinant Schur complements. A two-mode formula by itself would not have justified the physical admission.

Using (2), |s|≤1, and the exact rational checker:

- c = 0.01: limiting TV < −0.1525318 < −1/10;
- c = 100: limiting TV > 0.9937724 > 1/10.

The limits have strict slack. Consequently both finite-M visibility inequalities hold for all sufficiently large M. Together with (5), this proves the stated zero observation separation for the fixed margin τ = 1/10. The proof establishes existence of a finite threshold; it has not extracted a certified numerical threshold M_0.

An optional floating-point smoke check at M = 1000, 3000 and 10000 gave negative-branch TV near −0.203 and positive-branch TV above 0.996. These are diagnostics only. The analytic asymptotic argument and rational crossing certificate carry the claimed result.

## 5. Identification consequence and boundaries

For any ε > 0 choose M large enough that the two TV margins hold and 100/M² < 2ε. The midpoint of their full energy curves is within ε of both. Any rule assigning a definite visibility sign to every such bounded-error observation must fail on at least one of these two admissible devices. This also applies after restricting to a fixed finite menu. Length contributes no separation because it is identical.

The disorder assumption is essential. The model here permits unbounded scalar onsite potentials. A nondegenerate, untruncated finite-dimensional Gaussian has full support, so every finite constructed profile and every sufficiently small neighborhood lies in its support. A fixed standard-deviation parameter does not itself impose a hard amplitude bound. Conversely, a generator that clips values, imposes a fixed realized RMS, bounds contact barriers, or excludes very weak effective contacts can exclude this sequence. The inspected Taylor text does not settle those implementation details. No probability mass or typical-device error rate has been computed.

A fixed positive internal broadening changes the singular limit: it supplies an imaginary part that does not vanish with the effective contact width. The present proof uses zero dissipation throughout, as does the stated Taylor table. It is not a result for MEDA's positive-broadening conductance problem.

The exact lead convention remains a separate gate. The construction authenticates one fixed microscopic normal-lead model; it does not identify the leads used in the unavailable source implementation. A theorem for the actual archived dataset would require that binding, its field list/test point, and its disorder-generation policy. Exact noiseless injectivity also remains undecided.

## 6. Attribution and verification packet

The dependence of scattering visibility on splitting and lead coupling is established prior physics. Araya Day et al. give explicit effective-model formulas and discuss finite-wire lead bias. This candidate's contribution is a source-scoped microscopic construction and certificate, not a claim to have discovered that dependence. [Araya Day et al., SciPost Physics Core 8, 047 (2025), §3.1](https://arxiv.org/html/2504.01069v1)

Held-out additional conductance settings for validating inferred disorder were already proposed by Taylor, Sau and Das Sarma. Their simulated, truncated-disorder validation is useful prior; it is not a uniform separation theorem. [PRL 132, 206602 (2024), Results](https://arxiv.org/html/2307.11068v2)

Files in this packet:

- `CROSSING-CERTIFICATE.json`: persisted rational inverse proposal; SHA-256 `13e77448a7bdd0a85666be3fccf3687153f9bf87c214594ba613616fa50a614c`.
- `verify_crossing_certificate.py`: exact-rational checker, reading the pinned certificate; no eigensolver or floating-point acceptance comparison.
- `CROSSING-CHECKER-RESULT.json` and `CROSSING-CHECKER-LOG.txt`: executed checker receipt and exact bounds.
- `certify_crossing.py`: proposal-generation provenance; floating point proposes, fractions check.
- `finite_barrier_smoke.py` and `FINITE-BARRIER-SMOKE.json`: separately labeled exploratory diagnostics.

Independent mathematical/source review is required before upgrading this candidate's status or publishing it as an accepted result. The full inverse/scattering limit is a hand proof, not a consequence automatically checked by the finite-matrix script.
