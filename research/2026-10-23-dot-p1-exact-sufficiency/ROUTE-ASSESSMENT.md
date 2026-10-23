# P1: exact sufficient-algebra compression does not supply the sharper rate

23 October 2026, 16:30 UTC. Contributor: dot (OpenAI), working with Nolan.

**Source-led hand route assessment, with coordinating algebra/source review.** No new P1 rate, general impossibility result, independent whole-proof acceptance, historical-novelty claim or execution. This is an application of classical quantum sufficiency and Schur–Weyl duality, with the elementary original-source calculation given below.

## 1. Current evidence and unchanged target

Main was read at `8603ddd3b8fdb2dadf74e766bded30b8ec803172`. The accepted-work addendum remains blob `d92fee6359766251627c2537a29c14832aa83b0e`. The latest relevant [15:06 PR3 checkpoint](https://github.com/Sodelin/Research-Commons/pull/3#issuecomment-6368010560) preserves the sharper risk/increment gap; the later [16:06 implementation report](https://github.com/Sodelin/Research-Commons/pull/3#issuecomment-6369224397) changes infrastructure evidence, not P1 mathematics. No later P1 rate supplier was found in the inspected comments/current addendum. This is a bounded finding, not an assertion about unpublished owner work.

The original class is

\[
\rho_h=\frac{e^{-\beta H_h}}{\operatorname{Tr}e^{-\beta H_h}},\quad
H_h=\sum_{1\le |P|\le k}h_P P,\quad |h_P|\le1,\qquad
M=\sum_{j=1}^{\min(k,N)}3^j\binom Nj.
\]

Here beta>0 and k are fixed. N, the coefficients, interaction incidence, every finite candidate ensemble, every prior, and the copy budget vary. There is no degree, total per-site strength, minimum-eigenvalue, smooth-prior, known-source-basis, or purification promise.

Two sufficient sharper estimates remain unsupplied:

\[
\sup_{\text{finite admitted ensembles, priors }p}R_B^*(p,n)
\le C_{\beta,k}M/n,                                      \tag{R}
\]

where the optimal n-copy procedure has a classical density-matrix output and squared-Bures loss, or

\[
\chi_{2n}(p)-\chi_n(p)\le C_{\beta,k}M
\quad\text{for every such ensemble and prior and every }n\ge1. \tag{D}
\]

The source label is fixed across all copies. These are sufficient routes, not assertions equivalent to optimal two-source testing or matching its lower envelope.

The [19 October conditional transfer](https://github.com/Sodelin/Research-Commons/blob/2a2ee35f0660daaa6c41c78ad8c1f6e636ce935f/research/2026-10-19-p1-distance-weighted-pgm-route/actual-distortion/square-root-comparison/P1-SQUARE-ROOT-PGM-COMPARISON-20261019.md) and its [review](https://github.com/Sodelin/Research-Commons/blob/2a2ee35f0660daaa6c41c78ad8c1f6e636ce935f/research/2026-10-19-p1-distance-weighted-pgm-route/actual-distortion/square-root-comparison/P1-SQUARE-ROOT-PGM-INDEPENDENT-REVIEW-20261019.md) are already complete. Under (R), n>=ceil(12288 C M/epsilon²), 0<epsilon<=1, gives the original full-trace test with exactly n copies per unknown source, 2n total, ideal error<=1/4 and the recorded effective-precision slack to1/3. No pilot copies are free.

Under (D), monotonicity of the accepted increments gives delta_(2n-1)<=CM/n. The [20 October PGM theorem](https://github.com/Sodelin/Research-Commons/blob/43cebb410eed5fbf6764b000f0b2e40d77090e25/research/2026-10-20-p1-pgm-information-increment/P1-PGM-AFFINITY-INCREMENT-20261020-v2.md) therefore gives squared full-trace risk<=8CM/n at q=2n-1 copies. Feeding that risk into the existing conversion charges 2q=4n-2 original copies, with n chosen to satisfy its accuracy/error constants. This assessment does not supply (R) or (D), alter upper13/accepted lower domains, or reopen the completed transfer.

## 2. Saved routes checked before choosing this one

The current addendum, the saved global-entropy/capacity-difference assessment, the 18 October exponential-geometry audit, the 19 October Bures-supplier audit, and the full modular-work acquisition proof/review were read first.

* Classical Yatracos/VC theory already supplies the declared known-common-basis commuting result; the full one-body result is also already reviewed. [Existing proof and review](https://github.com/Sodelin/Research-Commons/tree/36677b23e79bf89bf2e98a8fa9e7e1cee642e830/research/2026-10-19-p1-distance-weighted-pgm-route/actual-distortion). Neither was reproved.
* The apparently new Fisher-information source was already audited in `P1-EXPONENTIAL-GEOMETRY-UNIFORMITY-CHECK-20261018-0202.md`; its fixed-dimension/local-error regularity assumptions are not a uniform state-risk theorem. The original admitted rare-sector control and its limitation remain intact.
* The [accepted modular acquisition assessment and review](https://github.com/Sodelin/Research-Commons/tree/c6981fd51259bbe8e252f41142e41e4ff817eed1/research/2026-10-18-dot-new-attacks-0419z/p1-modular-work/acquisition) rule out a particular globally unitary-invariant readout shortcut. They explicitly do **not** exclude retaining the Schur representation registers and using locality-aware measurements.
* The accepted isotropic-reference and transverse-greedy failures remain narrow. The old transverse coordination sentence listing the conditional transfer as open is superseded by the [13:30 correction](https://github.com/Sodelin/Research-Commons/blob/342f2ed3d5b2628f846f54b80d07d8305afa1723/docs/P1-P5-ACCEPTED-WORK-ADDENDUM.md), not re-adopted here.

Targeted searches of the saved P1 directories and repository did not locate the exact minimal-sufficient-algebra calculation below. This bounded search does not establish novelty or exhaustive absence.

## 3. Distinct candidate mechanism

The proposed shortcut was to exploit the M log-density coefficients by losslessly compressing the n-copy experiment into an exact sufficient algebra of complexity polynomial in n with exponent O(M), then use a dimension-controlled estimation/information argument. This retains the quantum orientation registers and is different from weak-Schur spectral readout, classical VC reduction, local Gaussian asymptotics, or subtracting global redundancy bounds.

The first proposed dimension premise is false for the original class when N>=2 and k>=2. In fact its exact sufficient algebra is already the usual full d-dimensional iid Schur algebra, with d=2^N.

### Primary sufficiency interface actually used

Jenčová–Petz, [*Sufficiency in quantum statistical inference*, arXiv:math-ph/0412093v1](https://arxiv.org/pdf/math-ph/0412093v1), Theorem1(iv) and the minimality paragraph after Theorem3, characterize the minimal sufficient subalgebra by the reference-relative modular cocycles. Theorem5 addresses exact coarse-grainings through an isomorphic sufficient algebra after the reference-support reduction. Here all systems are finite dimensional, the reference is the faithful maximally mixed member, and every Gibbs density is faithful. Thus no infinite-dimensional, support, or asymptotic hypothesis is imported. Only these passages and the related exponential-family Theorem6 were inspected, not the complete paper.

Let S_n(A)=sum_(r=1)^n A^(r) on (C^d)^(tensor n). Let A_n be the unital complex *-algebra generated by the n-copy densities of the original family. The maximally mixed member belongs to that family. Because its density is scalar, the cocycle algebra is exactly A_n: spectral functional calculus in finite dimensions converts positive invertible densities into their imaginary powers and conversely.

The same conclusion already holds for the **finite admitted ensemble**

\[
\mathcal F_N=\{I/d\}\cup
\left\{\rho_P=\frac{e^{-\beta P}}{d\cosh\beta}:
P\text{ a nonidentity Pauli word of weight one or two}\right\}. \tag{1}
\]

Every displayed Hamiltonian has one coefficient equal to1, all others0, with all N physical spins retained. There are L=1+3N+9 binomial(N,2) members. This uses no unknown-source gate or change to the admitted interaction class.

### Step A: the cocycles contain all collective one- and two-body generators

For (1), with omega_n=I/d^n,

\[
(\rho_P^{\otimes n})^{it}\omega_n^{-it}
=(\cosh\beta)^{-int}e^{-it\beta S_n(P)}.                 \tag{2}
\]

Scalar phases are in a unital algebra. Differentiating this finite-dimensional one-parameter group at t=0 shows S_n(P) belongs to its generated algebra. Conversely, exponentials of these generators give every density in (1).

### Step B: commutators generate all Pauli weights, algebraically

For any A,B,

\[
[S_n(A),S_n(B)]=S_n([A,B]),                             \tag{3}
\]

because terms on different copies commute. Induct on the support size r of a target Pauli word P. We already have r=1,2. For r>=3 choose distinct support sites i,j. Choose single-site Pauli letters U,V with UV=iP_i. Let R agree with P away from i,j, put U at i and identity at j; let Q have V at i, P_j at j and identity elsewhere. Then R has weight r-1, Q has weight2, and they anticommute at exactly i. Thus [R,Q]=2iP, and (3) gives S_n(P).

Consequently the algebra contains S_n(A) for every traceless Hermitian d-by-d A, since Pauli words form a real basis. It contains exp(iS_n(A))=(exp(iA))^(tensor n), hence the entire collective SU(d) representation. Scalar phases add U(d) without changing the algebra.

This is an algebraic generation statement. It **does not** claim that higher-weight P is an admitted source Hamiltonian, nor implement these commutators by free physical controls.

### Step C: exact algebra and dimension

Every tensor power rho^(tensor n) commutes with copy permutations. Conversely, classical Schur–Weyl duality says the algebra generated by U^(tensor n), U in U(d), is the whole commutant of those permutations. The primary exposition in Bacon–Chuang–Harrow, [arXiv:quant-ph/0601001v1](https://arxiv.org/pdf/quant-ph/0601001v1), SectionII.B, equations5–12, states both mutual-centralizer directions and the representation decomposition. No circuit implementation or gate-cost result is used here. Thus

\[
\boxed{\mathcal A_n
=\{X:[X,V_\pi]=0\ \forall\pi\in S_n\}
=\bigoplus_{\lambda\vdash n,\,\ell(\lambda)\le d}
\operatorname{End}(Q_\lambda^d)\otimes I_{P_\lambda}.}    \tag{4}
\]

The finite ensemble (1) already generates (4), and the entire original Gibbs family has the same algebra: containment in the permutation commutant supplies the reverse inclusion.

Its complex vector-space dimension has an elementary orbit count. Use the d² single-copy matrix units as an operator basis. Permutation conjugation permutes the n tensor factors. An invariant operator has one coefficient per orbit; the orbit is specified by the d² nonnegative multiplicities summing to n. Hence

\[
\boxed{\dim_{\mathbb C}\mathcal A_n=\binom{n+d^2-1}{d^2-1}.} \tag{5}
\]

For each fixed N, its polynomial degree in n is d²-1=4^N-1. Therefore no constant C_(beta,k) can give dim A_n <= (n+1)^(C_(beta,k)M) for all N,n at a fixed k>=2: choose N with 4^N-1>C_(beta,k)M and then let n grow. The same exponent obstruction persists if a finite N-dependent prefactor is allowed. Exact coarse-graining does not replace this algebra by one of smaller isomorphism type; this is the limited purpose of the sufficiency theorem above.

## 4. Why this does not contradict the desired rate

Exact sufficient-algebra dimension is not statistical difficulty. The finite ensemble (1), already having the full algebra (4), nevertheless satisfies

\[
0\le\chi_{2n}(p)-\chi_n(p)\le\chi_{2n}(p)\le H(p)\le\log L
\]

for **every** prior on its L labels. In particular that ensemble obeys (D) trivially. It is a control demonstrating why (5) cannot be converted into an exponential copy lower bound or a counterexample to the desired Gibbs rate. No arbitrary nonlocal or unitarily rotated Gibbs source is admitted by invoking Schur–Weyl duality.

Nor does the result prohibit full Schur processing followed by locality-sensitive operations, approximate or prior-dependent compression, state-sensitive estimation, or a direct two-source test. It only rejects the exact algebra-dimension replacement d²→O(M). For k=1 the collective Lie algebra is different; the already accepted one-body risk theorem is untouched.

## 5. Stopping point and genuine missing estimate

This route produces no affirmative sharper bound. Exact lossless compression alone retains the generic ambient Schur algebra, so it does not supply an O(M/n) risk theorem just from the number of log-density generators. Cumulative dimension bounds would additionally still not license subtracting two upper bounds to prove a same-prior increment.

The remaining sufficient statement is still (R) or (D), with constants independent of N, n, finite candidate set, prior and interaction incidence. A refinement would have to prove a **quantitative state-risk or conditional-information estimate for the restricted Gibbs subset within these blocks**, rather than substitute the size of the algebra. Approximate compression would require its actual uniform risk/decision error, preparation cost and every physical input copy to be controlled; the exact sufficiency theorem supplies none of those quantitative premises. No concrete source-matched approximate construction is available from the inspected passages, so it is not adopted as a new project or advertised as a promising solution.

The useful result of this bounded continuation is the exact failure of one different proposed import, with the original-source witness and an explicit nonimplication control. It does not change P1's accepted upper/lower bounds, its completed conditional conversion, P5's author-complete unrestricted negative result, existing ownership, or any canonical claim count. Further work should require an actual candidate estimate toward (R)/(D), not another compression interface or a repeated literature census.

## Inspection and verification limits

All calculations above are hand arguments, not executed symbolic checks. The primary theorem statements/passages named above were accessed directly. One recursive GitHub tree request failed with a closed transport; bounded directory/current-file/comment reads succeeded, so no repository-wide completeness is claimed. A mistakenly recalled unrelated arXiv identifier was discarded and is not evidence. No primary-access restriction was bypassed. The coordinating review checked the displayed commutator generation, orbit-count dimension and finite-ensemble nonimplication, and opened the two primary papers. This is not independent whole-proof acceptance; no external peer review, novelty, Lean, native or empirical certification is implied.
