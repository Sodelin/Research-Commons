# All finite channel counts: the exact conductance–reflection-determinant region

**Date:** October 17, 2026, 01:10 UTC. **Author:** dot (OpenAI), working with Nolan. **Status:** hand-proof candidate for independent review. The extension to arbitrary finite channel count was explicitly requested. No Lean verification, new numerical execution, historical novelty, or microscopic realization theorem is claimed.

## Result

For every finite integer N ≥ 1, let a zero-energy particle-hole-symmetric reflection matrix be

\[
r=\begin{pmatrix}A&B\\\overline B&\overline A\end{pmatrix},
\quad A,B\in\mathbb C^{N\times N},\quad \|r\|\le1.
\]

Define the dimensionless local conductance and real reflection determinant by

\[
g=N-\|A\|_F^2+\|B\|_F^2,\qquad Q=\det r.
\]

In the physical interpretation, spin is already counted among the N incoming electron channels; conductance is measured in e²/h, with current into the device. Full loss-free scattering makes its reflection block contractive. Reflection need not itself be unitary. The mathematical theorem only uses the displayed symmetry and contraction.

**The sharp inequalities are**

\[
0\le g\le2N,\quad |Q|\le1,\quad
Q\ge1-g,\quad (-1)^NQ\ge g-(2N-1). \tag{1}
\]

More strongly, these inequalities describe the entire attainable (g,Q) region in this algebraic class. For a fixed g ∈ [0,2N], the possible determinants form exactly:

- **Even N:**
  \[
  \max\{-1,1-g,g-2N+1\}\le Q\le1.
  \tag{2}
  \]
- **Odd N:**
  \[
  \max\{-1,1-g\}\le Q\le\min\{1,2N-1-g\}.
  \tag{3}
  \]

N = 1 gives the exact identity Q = 1−g. N = 2 gives the previously reviewed inequality Q ≥ |g−2|−1. The lower-edge certificate Q ≥ 1−g is independent of N, so it remains valid even if the total channel count is unknown but finite and the stated conductance formula applies. The high-conductance edge depends on N and its parity.

“Sharp” refers to the class of all contractive PHS reflection matrices. It does not assert that every extremizer is realized by the connected fixed-hopping Rashba chain or by a fabricated device. Actual source subclasses can have smaller observation fibres.

## 1. Majorana conversion, orientation and conductance

Let

\[
U=2^{-1/2}\begin{pmatrix}I&I\\-iI&iI\end{pmatrix}.
\]

The PHS condition makes U r U† real. This basis lists all first Majorana coordinates, then all second coordinates. Apply the fixed real permutation Π that changes this order to adjacent pairs, and put

\[
R=\Pi U r U^\dagger\Pi^T,\quad
J=\bigoplus_{j=1}^N\begin{pmatrix}0&1\\-1&0\end{pmatrix},\quad
K=RJR^T.
\]

Then R is a real contraction, det R = Q, and K is real antisymmetric with ||K|| ≤ 1. The adjacent-pair orientation gives Pf(J) = 1. Pfaffian congruence therefore yields

\[
\operatorname{Pf}(K)=\det(R)\operatorname{Pf}(J)=Q. \tag{4}
\]

For clarity, write A=a+ib and B=c+id with real matrices. Before the adjacent-pair permutation,

\[
UrU^\dagger=
\begin{pmatrix}a+c&-b+d\\b+d&a-c\end{pmatrix}.
\]

The trace of the upper-right block of RJRᵀ in that grouped order is

\[
\operatorname{tr}[(a+c)(a-c)^T-(-b+d)(b+d)^T]
=\|A\|_F^2-\|B\|_F^2.
\]

Thus, in adjacent order,

\[
\sum_{j=1}^N K_{2j-1,2j}=N-g. \tag{5}
\]

Equivalently, if the antisymmetric inner product is defined as one half of the Frobenius inner product, this is ⟨J,K⟩ = N−g. No extra factor of two or unresolved Pfaffian orientation is suppressed.

## 2. A finite auxiliary density matrix, constructed explicitly

This step is an algebraic proof device. It does not claim that the auxiliary state is the physical state inside the wire.

On (C²)⊗N, use the standard Pauli matrices and define Jordan–Wigner Majoranas

\[
c_{2j-1}=Z_1\cdots Z_{j-1}X_j,\qquad
c_{2j}=Z_1\cdots Z_{j-1}Y_j.
\]

They are Hermitian and satisfy c_a c_b + c_b c_a = 2δ_ab I. With this convention

\[
Z_j=-ic_{2j-1}c_{2j},\quad n_j=(I-Z_j)/2,\quad
P=\prod_j Z_j=(-1)^{\sum_j n_j}.
\]

The reference K = J corresponds to the vacuum with P = +1.

The real antisymmetric normal form gives

\[
K=O\left(\bigoplus_j\lambda_jJ_2\right)O^T,
\quad O\in O(2N),\quad |\lambda_j|\le1.
\]

Set d = Oᵀc and Z′_j = −i d_(2j−1)d_(2j). The d's satisfy the same anticommutation identities. The Z′_j are commuting Hermitian involutions. Define

\[
\rho=2^{-N}\prod_{j=1}^N(I+\lambda_j Z'_j). \tag{6}
\]

Every factor is positive semidefinite, and the factors commute; hence ρ is positive semidefinite. Every nonempty product of distinct d generators has zero trace. One elementary proof conjugates it by a d generator that anticommutes with that product: for an even-length nonempty product choose a generator in it; for an odd-length product choose one outside it, which exists because 2N is even. The trace changes sign. Consequently expanding (6) gives tr ρ = 1.

The same trace orthogonality gives

\[
-i\operatorname{tr}(\rho d_{2j-1}d_{2j})=\lambda_j,
\]

and all cross-pair two-point expectations vanish. Transforming back yields

\[
-i\operatorname{tr}(\rho c_a c_b)=K_{ab}\quad(a\ne b). \tag{7}
\]

There is no difficulty at λ_j = 0 or ±1: (6) is a polynomial product of positive factors and includes mixed and rank-deficient states directly.

For parity, the top Clifford product transforms by det O. In particular

\[
\prod_j Z'_j=(\det O)P,
\qquad
\operatorname{tr}(\rho P)=(\det O)\prod_j\lambda_j
=\operatorname{Pf}(K)=Q. \tag{8}
\]

This explicitly handles det O = −1. No unproved unitary implementer for an orientation-reversing transformation is required. Equations (5) and (7) also give

\[
\operatorname{tr}\!\left(\rho\sum_j n_j\right)
=\frac{N-\sum_jK_{2j-1,2j}}2=\frac g2. \tag{9}
\]

## 3. The all-N inequalities

On a joint occupation eigenvector with k particles, k is an integer in [0,N] and

\[
(-1)^k\ge1-2k.
\]

This is an operator inequality P ≥ I−2Σ_j n_j. Taking expectation in ρ and using (8)–(9) proves Q ≥ 1−g.

Apply the same inequality to the hole number N−Σ_j n_j. Its parity is (−1)^N P, yielding

\[
(-1)^NQ\ge1-2N+g.
\]

The expectation bounds 0 ≤ Σ_j n_j ≤ N give 0 ≤ g ≤ 2N. Alternatively they follow directly from contraction. The determinant bound |Q| ≤ 1 follows from the singular values of r, or from parity expectation. This proves (1).

The identity-versus-full-Andreev orientation is therefore explicit: replacing r by r times the full electron/hole swap sends g to 2N−g and Q to (−1)^N Q. The even/odd distinction is essential.

## 4. Sharp endpoint constructions

The following constructions take direct sums by electron mode, with the corresponding conjugate hole modes. They preserve PHS and contraction. Normal identity reflection on one mode has (g,Q)=(0,+1); perfect Andreev reflection on one mode is [[0,1],[1,0]] and has (g,Q)=(2,−1).

### 4.1 Low edge

For any g ∈ [0,2], let s=1−g and take on one mode

\[
r_s=\frac12\begin{pmatrix}1+s&1-s\\1-s&1+s\end{pmatrix}.
\]

Its eigenvalues are 1 and s, so it is contractive. Its conductance is 1−s=g and determinant s=1−g. Add identity reflectors on the other N−1 modes. This attains the low sloping edge, including s=0 and both endpoints.

### 4.2 A continuously tunable two-mode positive reflector

For θ ∈ [0,π/2], set

\[
A=\cos\theta\,\sigma_x,\qquad B=\sin\theta\,\sigma_z,
\qquad r_\theta=\begin{pmatrix}A&B\\B&A\end{pmatrix}.
\]

Because A²+B²=I and AB+BA=0, r_θ is real symmetric and unitary. Both A+B and A−B have determinant −1, so det r_θ=+1. Its conductance is 4sin²θ and covers [0,4].

For even N, N/2 such blocks attain Q=+1 at every g ∈ [0,2N]. For odd N, add one identity mode to (N−1)/2 blocks, attaining Q=+1 for every g ∈ [0,2N−2]. Equal θ in the blocks suffices to fill those intervals; when no block is present, the interval is the singleton {0}.

### 4.3 Negative flat edge

For odd N, one perfect-Andreev mode plus (N−1)/2 two-mode blocks attains Q=−1 at every g ∈ [2,2N]. For even N, one perfect-Andreev mode, one identity mode and (N−2)/2 two-mode blocks attain Q=−1 at every g ∈ [2,2N−2]. This includes N=2, where the interval is the singleton {2}.

### 4.4 High edge

Apply the full electron/hole swap to the low-edge construction. It sends (g,Q) to (2N−g,(−1)^N Q). Thus for even N it attains Q=g−2N+1 on [2N−2,2N], and for odd N it attains Q=2N−1−g on that interval.

These constructions attain every lower and upper endpoint stated in (2)–(3). They are algebraic reflection models; they are not asserted to be scalar-potential profiles in the original 60-site wire.

## 5. Every intermediate determinant is attainable

Fix g. The set

\[
\mathcal K_g=\{K\in\mathbb R^{2N\times2N}:K^T=-K,
\ \|K\|\le1,\ \sum_jK_{2j-1,2j}=N-g\}
\]

is convex and compact. Pfaffian is a continuous polynomial, so its image on this connected set is a compact interval.

Every K in this set is of the form RJRᵀ for some real contraction R. Indeed in the preceding normal form choose

\[
R=O\bigoplus_j\operatorname{diag}(\lambda_j,1).
\]

Then ||R||≤1 and RJRᵀ=K, including zero λ_j. Undoing the fixed adjacent-pair and Majorana basis changes gives a contractive PHS r with the prescribed conductance and determinant. Thus no extra covariance constraint was introduced by the auxiliary state. Since Section 4 attains both endpoints, every value between them is attained. This completes the exact-region claim.

If desired, any real contraction R has a real orthogonal two-lead dilation

\[
\mathcal S=\begin{pmatrix}
R&\sqrt{I-RR^T}\\
\sqrt{I-R^TR}&-R^T
\end{pmatrix}.
\]

The square-root intertwining identity follows from a singular-value decomposition and proves orthogonality. Scaling R continuously to zero shows det S=+1 because its block dimension is 2N, which is even. Transforming both leads back to Nambu coordinates gives a full unitary PHS scattering matrix. This only supplies algebraic loss-free scattering admission, not a local Hamiltonian, fixed Rashba hopping, specified contact implementation, or multi-setting realization.

## 6. Optimal conductance-only compatibility under a margin promise

Suppose 0<m≤1 and the admitted alternatives obey Q≥m or Q≤−m. This source promise must be independently justified; wanting a binary answer does not establish it. Projection of the exact region gives the following complete compatibility ranges:

| Channel parity | Positive-margin conductance range | Negative-margin conductance range |
|---|---|---|
| N even | [0,2N] | [1+m,2N−1−m] |
| N odd | [0,2N−1−m] | [1+m,2N] |

These include N=1: the two ranges are [0,1−m] and [1+m,2], with an excluded interval under the promise.

For an authenticated additive-error interval I=[y−η,y+η], intersect I with these two ranges. If it meets exactly one, the promised label is certified. If it meets both, the algebraic class contains opposite-margin reflectors compatible with the same report. If it meets neither, the report, error bound and source promise are mutually inconsistent. Closed range endpoints count as intersections; there is no hidden strictness convention.

This optimal promise-based rule differs from directly proving Q≥m without assuming a promise. For example, Q≥1−g directly certifies Q≥m when g≤1−m. Under the two-class promise, merely excluding all negative-margin models can certify the positive label over a larger range. A restricted physical source class may permit additional certificates; the algebraic ambiguity does not show such devices exist there.

With unknown but finite N, the universally valid low-edge estimate remains Q≥1−g. Hence an error upper bound u<1 gives Q≥1−u>0 without knowing N. A high-conductance inference requires N and its parity; applying the even-N high-edge sign to odd N would be wrong.

## 7. Prior work, significance and limits

The physical source relations are standard: [Beenakker, Dahlhaus, Wimmer and Akhmerov, arXiv:1012.0932v3, §II](https://arxiv.org/pdf/1012.0932) gives the canonical PHS blocks and channel counting, while its reflection-only eigenvalue formulas use the stronger assumption of unitary reflection. [Rosdahl et al., PRB 97, 045421, Eqs. (3)–(5)](https://pure.tudelft.nl/ws/portalfiles/portal/46877558/PhysRevB.97.045421.pdf) supplies the local transport formula; our sign is current into the device.

The auxiliary covariance facts are established prior, not a new discovery. [Sergey Bravyi, *Lagrangian representation for fermionic linear optics*, arXiv:quant-ph/0404180v2, §IV, Eqs. (17)–(19)](https://arxiv.org/pdf/quant-ph/0404180) gives the Pfaffian correlation rule, product-state construction and covariance criterion. Its Majorana sign convention differs from the explicitly vacuum-calibrated convention above. [Grabsch, Cheipesh and Beenakker, arXiv:1903.11498v2, §2.2, Eqs. (11)–(12)](https://arxiv.org/pdf/1903.11498) applies Pfaffian parity formulas to open subsystems. Section 2 proves the needed finite identities directly rather than leaving orientation or existence implicit.

There is also a direct unitary-reflection antecedent: [Wimmer, Akhmerov, Dahlhaus and Beenakker, arXiv:1101.5795v2, §II, Eq. (3)](https://arxiv.org/pdf/1101.5795) writes g=1−Q+4Σ′R_n. Its nonnegative remainder already implies Q≥1−g in that setting. The present proof permits arbitrary contractive reflection with nonquantized Q; it does not claim the unitary special case as new. The accompanying directed prior assessment records additional unitary bounds and the limits of the search.

The useful extension is a complete sharp relation between aggregate local conductance and finite reflection determinant for every finite channel count, with an exact margin/noise compatibility interpretation. The argument is a short composition of established covariance, parity, contraction and continuity facts. Historical novelty of this particular composition and region has not been established. It should not be described as a new parity principle or a new topological invariant.

The result does not identify protected Majorana modes, a thermodynamic phase, the original Taylor implementation, finite-temperature averages, finite-bias measurements, floating-condensate conductance, or calibration/model errors not included in an authenticated error interval. Nor does it prove a complete inverse theorem for several settings of one fixed physical wire. The auxiliary density matrix and extremizing scatterers are algebraic tools, not claimed experimental preparations.
