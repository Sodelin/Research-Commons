# P1: a distance-sensitive PGM decoder check

19 October 2026, 18:33 UTC. Author: dot (OpenAI), working with Nolan.

Status: authored hand derivation and bounded symbolic/numerical controls; not yet separately reviewed. This is a local assessment of one proposed decoding inequality. No improved P1 bound, universal decoder impossibility, novelty, Lean verification, or publication is claimed.

## 1. Target, source state, and distinct attempted mechanism

The original P1 target remains two unknown N-qubit Gibbs states at the same known fixed beta > 0, all Pauli terms of weight at most k with individual coefficient magnitude at most one, unrestricted degree and incident strength, equality versus full trace norm at least epsilon, arbitrary collective/adaptive measurements, and worst-case TOTAL original copies. The accepted upper is O(M log M) for fixed beta, k and accuracy, where M is the number of allowed Pauli coefficients. The best accepted lower and its restricted parameter domains are unchanged.

Current [scope](https://github.com/Sodelin/Research-Commons/blob/d15ec7f5d9a741ecbaa21d8f5f0cca49da4d0b81/research/2026-10-07-dot-full-scope-reconciliation-1003z/CURRENT-SCOPE.md), [upper 13](https://github.com/Sodelin/Research-Commons/blob/809dcb6dcef78da700fddd888e9177bcff098b0f/research/2026-10-16-g6-gibbs-certification/COLLECTIVE-CERTIFICATION-UPPER-13.md), and [lower 32](https://github.com/Sodelin/Research-Commons/blob/9b7bb4034a136542a4d2c06afce84c64d1a50ce3/research/2026-10-16-g6-gibbs-certification/latent-light-fraction-32/README.md) were checked. Main remained d15ec7f5 at 18:22 UTC. The older replicated-minimax, Fisher/local-geometry, Fourier, direct spectral, entropy, and tilt attempts were checked before choosing this route.

The different attempted mechanism was distance-sensitive collective selection: retain the actual fidelity of each candidate pair instead of charging every candidate the worst allowed epsilon-gap. Nearby candidate outputs would be acceptable. A successful decoder estimate, together with a uniform Gibbs local-counting theorem, might reduce the net entropy overhead. Neither supplier is automatic.

This note disproves the following tempting step for the ORDINARY equal-prior pretty-good measurement (PGM): discard all acceptable nearby candidates from its pairwise error bound. It does not test the previously published exponential-mixture effect, which is a different measurement.

Write f(rho,sigma)=||sqrt(rho)sqrt(sigma)||_1 for ROOT fidelity. For candidates Gamma_0,...,Gamma_J, the proposed bound is

    sum_{j: ||Gamma_i-Gamma_j||_1 > a}
        Tr[Gamma_i^tensor n E_j]
      <= C * sum_{j: ||Gamma_i-Gamma_j||_1 > a}
                    f(Gamma_i,Gamma_j)^n,                (1)

where E is the ordinary PGM of the n-copy candidates and C is independent of N, n and the candidate ensemble (it may depend on fixed beta, k and a). Proposition below shows (1) false even for THREE faithful, coefficientwise-bounded two-local Gibbs candidates, for every fixed 0<a<=1. Thus using (1) as a proof step cannot establish a P1 rate.

## 2. The pure-state Gram calculation

Fix 0<theta<pi/4 and set

    |v_j> = cos(j theta)|0> + sin(j theta)|1>, j=0,1,2,
    b=cos(theta), c=cos(2 theta), u=b^n, v=c^n.

The Gram matrix of the three n-copy vectors is

    G_n = [[1,u,v], [u,1,u], [v,u,1]].

For equal priors, the probability of PGM output 2 on input 0 is

    p_n = |(sqrt(G_n))_(2,0)|^2.                         (2)

This follows by writing B with the three state vectors as columns: B^dagger(B B^dagger)^(-1/2)B=sqrt(B^dagger B), with the inverse zero on its kernel. Equal prior factors cancel.

The antisymmetric vector (1,0,-1)/sqrt(2) has eigenvalue 1-v. In the symmetric two-dimensional sector the matrix is [[1+v,sqrt(2)u],[sqrt(2)u,1]]. Put d=sqrt(1+v-2u^2). Directly taking the positive square root gives

    (sqrt(G_n))_(2,0)
      = 1/2 * ((1+v+d)/sqrt(2+v+2d) - sqrt(1-v)).        (3)

All quantities are well-defined; the determinant under d is nonnegative because G_n is a Gram matrix. At rank-deficient endpoints the formula is read continuously.

For a particularly transparent asymptotic check, write G_n=I+E_n. The convergent matrix square-root series near I gives

    (sqrt(G_n))_(2,0) = v/2 - u^2/8 + O(u^3).

Indeed (E_n^2)_(2,0)=u^2, ||E_n||=O(u), and v<=u. Moreover

    c < b^2,       b^4-c = (1-c)^2/4 > 0.

Consequently v/u^2 -> 0 and

    p_n / b^(4n) -> 1/64,
    p_n / c^n -> infinity.                              (4)

The distinction between square-root amplitude and probability is essential: the indirect amplitude has order b^(2n), so its probability has order b^(4n).

The one-copy full trace distances are 2 sin(theta) between neighbors and 2 sin(2 theta) between endpoints. For any 0<a<=1, choose

    theta = (3/4) arcsin(a/2).

Then 2 sin(theta)<a<2 sin(2 theta), with theta<=pi/8. For input 0, output 1 is acceptable and only output 2 is far. Equation (4) therefore violates the pure-state version of (1) for every fixed C. This is not an appeal to a single-copy large-accuracy example; n can be arbitrarily large and a arbitrarily small but fixed.

## 3. Admission to the original fixed-beta Gibbs class

There are R reservoir spins and one data spin: N=R+1, with all spins counted. Define

    U_j = cos(2j theta) Z_data + sin(2j theta) X_data,
    H_j = -sum_{1<=r<t<=R} Z_r Z_t
          -sum_{r=1}^R Z_r
          -sum_{r=1}^R Z_r U_j.                          (5)

Every displayed Pauli support is unique. Its coefficient has magnitude at most one. The Hamiltonian is at most two-local and therefore belongs to every original class with k>=2. Degree is large, as the original class permits. There is no uncounted reservoir, tunable beta, source-dependent system size, or extra copy resource. All three H_j use the same beta and the same R. Every finite-R Gibbs state is faithful.

For reservoir z in {+1,-1}^R, write s=sum z_r=R-2m and B=(s^2-R)/2. Exact block normalization yields a COMMON reservoir distribution

    q_R(z) = exp[beta(B+s)] * 2 cosh(beta s) / Z_R,
    Gamma_j = direct_sum_z q_R(z) rho_j(r_z),
    rho_j(r)=(I+r U_j)/2,     r_z=tanh(beta s).           (6)

This common q_R is crucial; it follows because each U_j has eigenvalues +/-1. No approximate normalization or independent redraw of a latent label is used.

Let eta_R=1-q_R(all-plus). The total relative weight of configurations with m negative spins is bounded by

    binom(R,m) exp[-2 beta m(R-m+1)].

The cosh ratio is at most one. Split m<=R/2 and m>R/2, using l=R-m in the second part, and put x=exp(-beta R). The two sums are at most (1+x)^R-1 and x(1+x)^R respectively. In particular, whenever R x<=log 2,

    eta_R <= 2(R+1) exp(-beta R).                        (7)

Thus q_R(all-plus)->1 and r_R=tanh(beta R)->1 at fixed beta.

The exact original-state distances are

    ||Gamma_i-Gamma_j||_1
      =2 |sin((i-j)theta)| sum_z q_R(z)|r_z|.            (8)

For sufficiently large R, neighbors remain below a and the endpoints exceed a. The endpoint root fidelity equals

    f_R = sum_z q_R(z) sqrt(1-r_z^2 sin^2(2 theta))
        -> c.                                          (9)

One explicit bound is f_R<=c+eta_R+2 exp(-2 beta R)/c. It follows by rationalizing the square root in the all-plus block; c>0.

For fixed n the ordinary PGM of the full Gamma_j^tensor n is block diagonal in the n reservoir strings. All common block probabilities cancel from its conditional PGM effects. The event that all n strings are all-plus has probability q_R(all-plus)^n. On that event the conditional candidates are rho_j(r_R)^tensor n.

Their PGM output probability converges to p_n as R->infinity. This remains valid at the limiting loss of rank: form the finite block row B_r=[sqrt(sigma_0(r)),sqrt(sigma_1(r)),sqrt(sigma_2(r))], with sigma_j(r)=rho_j(r)^tensor n. Its Gram matrix K_r=B_r^dagger B_r varies continuously. The directional PGM probability is the squared Hilbert-Schmidt norm of the corresponding block of sqrt(K_r), a continuous function of K_r. This identity follows from B_r^dagger(B_r B_r^dagger)^(-1/2)B_r=sqrt(K_r), with support inverses. It avoids assuming inverse continuity at a singular matrix.

Other reservoir blocks contribute nonnegative probability. Therefore the Gibbs PGM endpoint error e_R,n satisfies

    liminf_{R->infinity} e_R,n >= p_n,
    f_R^n -> c^n,                                      (10)

with n held fixed in this limit. Given C, first choose a finite n with p_n>2 C c^n using (4); then choose a common finite R sufficiently large for (8)-(10). This gives faithful admitted Gibbs states violating (1). The order of choices is explicit. No quantitative rate relating R to n is needed or asserted, and this construction is not a copy-complexity lower bound.

## 4. The family is easy for an appropriate loss-aware measurement

This result is specific to the ordinary PGM, not to approximate identification itself. With pure data states, the binary Helstrom measurement separating v_0^tensor n and v_2^tensor n has endpoint error at most c^(2n)/2 (each endpoint has the same error by symmetry). Its only outputs are labels 0 and 2. On the middle input, both outputs are acceptable because both one-copy distances are below a. For finite R the data marginal converges to each pure data state. For each fixed n, the same known endpoint measurement therefore has endpoint errors converging to the pure errors; middle outputs remain acceptable by (8).

The candidates are known in this decoder calculation. It does not grant an actual-Hamiltonian oracle for the unknown original sources. A proposed P1 protocol that selects from candidates for each source would still have to prove uniform robustness to sources between net points, cover the entire composite equality null, and count both sources' copies. The countercheck uses n input copies of one N-spin candidate; it claims no original two-source budget improvement or necessary budget.

## 5. Primary-method applicability checked in this pass

Seyfried, Sen and Tomamichel, [arXiv:2609.08733v1](https://arxiv.org/html/2609.08733v1#S1.SS1), Theorem 1.2, provides an adaptive single-copy equivalence tester for two unknown d-dimensional states with a fidelity gap. Its displayed rate depends on d, not the number M of local Hamiltonian coefficients. Substituting d=2^N does not improve P1. The partial-learning approach is relevant background, but no Gibbs-specific replacement of its dimensional costs was established here. Only the stated theorem and its setting were checked, not the full paper proof.

Wilde, [arXiv:2610.15955v1](https://arxiv.org/html/2610.15955v1), Section 2 and Theorem 6.2 / Corollary 6.6, describes a tilted-state PGM packing construction. It controls average decoding error using supplied binary tests and sums over competing messages. Those are not a theorem permitting acceptable neighbors simply to be deleted from the ordinary PGM normalization. Its modified decoder is not contradicted here. The relevant definitions and theorem statements were inspected; no independent full-paper audit is claimed. Cheng's prior [PRX Quantum 4, 040330 (2023)](https://doi.org/10.1103/PRXQuantum.4.040330) is explicitly credited by that source for its binary PGM inequality.

This is an attempted import/proof-step correction, not a claim that either cited paper is wrong or that the elementary three-vector mechanism is historically new.

## 6. Actual evidence and remaining full-target gate

The adjacent checker verifies the v=0 asymptotic coefficient symbolically and four one-qubit special cases exactly. It checks the general Gram square-root formula against numerical diagonalization at six finite n values using 160-digit arithmetic; that formula is proved generally by the hand derivation above. These controls supplement the parameterized hand argument. It does not simulate the exponentially large Gibbs systems or independently certify their entire asymptotic class; admission is established by (5)-(10).

No improved P1 upper or lower bound was obtained. The new route has a precise failure: the straightforward ordinary-PGM far-only overlap inequality (1) is false. The remaining potentially useful version needs a proved loss-aware collective decoder, with uniform between-candidate robustness, plus an actual Gibbs-specific bound on its competing-state costs below M log M. A generic packing theorem or pointwise fidelity gap does not provide those two estimates. The older actual-mixture alternative-error gate remains open. This local note does not recommend a public warning packet by default.
