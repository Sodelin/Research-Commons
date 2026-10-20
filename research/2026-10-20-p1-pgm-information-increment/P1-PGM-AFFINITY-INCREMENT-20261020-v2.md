# P1: direct PGM affinity risk from a Holevo increment

20 October 2026 UTC. Authored hand derivation by dot (OpenAI), working with Nolan. The identity-reference channel inequality, block-Gram reduction, and measurement consequences received the scoped hand-proof PASS recorded in independent-review/REVIEW.md. This is not external peer review, a historical novelty claim, or formal verification.

## Outcome and precise remaining gate

For a finite prior (p_i,rho_i), define R_i=rho_i^{tensor n}, S=sum_i p_i R_i, and

    w_ij=p_i p_j Tr(R_i S^{-1/2} R_j S^{-1/2}),
    A_ij=Tr(sqrt(rho_i) sqrt(rho_j)),
    Q_n=sum_ij w_ij ||sqrt(rho_i)-sqrt(rho_j)||_2^2,
    delta_n=S_vN(sum_i p_i R_i tensor rho_i)-S_vN(S)-sum_i p_i S_vN(rho_i).

The inverses are on support; below the Gibbs candidates are faithful, so S is invertible. The scoped theorem is

    Q_n <= 2(1-exp(-delta_n)) <= 2 delta_n.                 (T)

The actual n-copy PGM, with candidate state rho_j as classical output after outcome j, has expected squared Bures risk at most Q_n and expected squared FULL trace norm at most 4Q_n. A_ij is affinity, NOT root fidelity. This is a measurement-level bound, not conversion of an unmeasured predictor into a classical estimator.

The original P1 scope is unchanged: two unknown N-qubit fixed-known-beta Gibbs states; at most k-local Pauli terms with every coefficient individually bounded by one; unrestricted degree and interaction sum; equality versus full trace norm at least epsilon; all copies charged; collective/adaptive measurements permitted. Write M=sum_{j=1}^k 3^j binom(N,j). The accepted upper13 and lower32 are NOT changed by this candidate alone.

A uniform bound delta_n <= C_(beta,k) M/n is still unproved. A uniform dyadic bound chi_(2n)-chi_n <= C_(beta,k) M would suffice, because delta_n is nonincreasing. Cumulative chi_n <= C M log n alone retains a logarithmic factor and does not prove that dyadic estimate by subtraction. The finite-prior PGM depends on the specified ensemble and prior, not on the realized unknown source label; the existing minimax/decoder machinery must still be used to obtain a prior-independent two-source test. Exactly n copies per unknown input would mean 2n total, with no extra source-copy acquisition in the PGM definition.

## 1. A channel inequality with maximally mixed input reference

Let Phi:B(H)->B(K) be CPTP, let sigma=Phi(I_H), and let r be a density matrix. Restrict the output to support sigma, on which sigma is invertible. Initially assume r>0. Set, for 0<q<=1,

    F(z)=sigma^{(z-1)/2} Phi(r^z) sigma^{(z-1)/2},
    f(q)=log ||F(q)||_{1/q}.

Claim: f is convex. This follows from Schatten-norm complex interpolation and the following explicit vertical-line bound, which is the part that must not be replaced by a commutativity assumption.

For real q and t, the 2-by-2 operator matrix

    [ r^q         r^{q+it} ]
    [ r^{q-it}    r^q      ]

is positive. Indeed r^q commutes with r^{it}, and the matrix factors using the unitary r^{it}. Complete positivity, followed by conjugation by diag(sigma^{(q-1)/2},sigma^{(q-1)/2}), gives a positive matrix [Y Z;Z* Y], where

    Y=sigma^{(q-1)/2} Phi(r^q) sigma^{(q-1)/2}=F(q),
    Z=sigma^{(q-1)/2} Phi(r^{q+it}) sigma^{(q-1)/2}.

Hence Z=Y^{1/2} K Y^{1/2} for a contraction K. Holder's Schatten inequality gives ||Z||_p <= ||Y||_p for p>=1. The imaginary powers of sigma in F(q+it) are outside Z and are unitary on the left and right, so

    ||F(q+it)||_{1/q} <= ||F(q)||_{1/q}.                 (1)

On any closed strip q in [a,b] subset (0,1], apply the Schatten three-lines theorem with reciprocal norm exponent affine in q: p_a=1/a, p_b=1/b, p_q=1/q. Equation (1) bounds each entire vertical boundary by its real-point norm. It follows that

    f((1-theta)a+theta b) <= (1-theta)f(a)+theta f(b).

There is no need for Phi(r) to commute with sigma. Imaginary input powers remain inside Phi and are handled by complete positivity, not discarded.

Because Phi is trace preserving, f(1)=log Tr Phi(r)=0. Differentiate the finite-dimensional trace at q=1, writing Y=Phi(r):

    f(q)=q log Tr F(q)^{1/q},
    F'(1)= (log sigma)Y/2 + Y(log sigma)/2 + Phi(r log r),
    f'(1)=Tr r log r - Tr Y log Y + Tr Y log sigma
          =D(r||I_H)-D(Phi(r)||Phi(I_H))=:Delta.

All logarithms are natural. The first relative entropy uses the unnormalized positive reference I_H, which is allowed in the displayed expression; it equals -S_vN(r). This is not a divergence to the normalized maximally mixed state, although the dimension constants would cancel under consistent normalization.

The tangent inequality for a convex f gives f(1/2)>=f(1)-(1/2)f'(1)=-Delta/2. Therefore

    Delta >= -log ||sigma^{-1/4} Phi(sqrt r) sigma^{-1/4}||_2^2.   (2)

For singular r, apply the proof to r_eta=(1-eta)r+eta I_H/dim(H) and take eta down to zero. Entropy, square roots and all expressions involving the fixed invertible sigma are continuous on the finite-dimensional state space. Phi(r_eta)>0 on support sigma. This proves (2) without an input minimum-eigenvalue assumption.

Equation (2) is NOT the statement that ordinary unrotated Petz recovery has the universal fidelity remainder. The right-hand side is a normalized-channel Hilbert-Schmidt contraction applied to sqrt r, not fidelity between r and a recovered density matrix. No generic unrotated-recovery theorem is imported.

## 2. Exact block-Gram reduction

Let C be the n-copy Hilbert space and let L be the finite candidate-label space. Define A:L tensor C -> C by its block columns A_i=sqrt(p_i) sqrt(R_i). Then AA*=S and

    G=A*A,  G_ij=sqrt(p_i p_j) sqrt(R_i) sqrt(R_j).

G is a density matrix and shares all nonzero eigenvalues with S. Even when the Gibbs states are faithful, G is generally singular; the regularization in Section 1 is therefore needed.

Functional calculus gives

    (sqrt G)_ij=sqrt(p_i p_j) sqrt(R_i) S^{-1/2} sqrt(R_j),
    ||(sqrt G)_ij||_2^2=w_ij.                           (3)

Define a CPTP channel from B(L tensor C) to B(L tensor C tensor B), where B is one single-copy Hilbert space, by

    Phi(X)_ij=X_ij tensor sqrt(rho_i) sqrt(rho_j).       (4)

To verify complete positivity and trace preservation, choose an orthonormal basis (e_a) of B and Kraus operators

    V_a (|i> tensor u)=|i> tensor u tensor sqrt(rho_i)e_a.

Then Phi(X)=sum_a V_a X V_a*, and sum_a V_a*V_a=I because Tr rho_i=1. In particular,

    sigma=Phi(I)=direct_sum_i (I_C tensor rho_i).

Phi(G) is the block Gram matrix with block columns sqrt(p_i) sqrt(R_i) tensor sqrt(rho_i). It therefore has the same nonzero eigenvalues as omega_(n+1)=sum_i p_i R_i tensor rho_i. Moreover,

    Tr Phi(G) log sigma=sum_i p_i Tr(rho_i log rho_i).

Consequently the channel gap Delta in (2), with r=G, is exactly delta_n.

Finally, the ij block of sigma^{-1/4} Phi(sqrt G) sigma^{-1/4} is

    (sqrt G)_ij tensor rho_i^{1/4} rho_j^{1/4}.

Its squared Hilbert-Schmidt norm sums to

    sum_ij ||(sqrt G)_ij||_2^2 Tr(rho_i^{1/2} rho_j^{1/2})
      =sum_ij w_ij A_ij
      =1-Q_n/2.                                      (5)

We used sum_ij w_ij=1, since these are the actual joint prior/PGM outcome probabilities. Substituting (5) into (2) gives delta_n>=-log(1-Q_n/2), proving (T). The independent review checks the interpolation and exact Gram reduction, including singular supports.

## 3. Operational consequences, kept separate from the unproved rate

The POVM is Lambda_j=p_j S^{-1/2} R_j S^{-1/2}. It is defined on exactly n original copies. It is not a Hamiltonian oracle, purification oracle, or recovery channel that generates extra physical copies. It may be computationally expensive, which is allowed for this copy-complexity question.

For root fidelity f_ij=||sqrt(rho_i)sqrt(rho_j)||_1, affinity A_ij<=f_ij. Thus squared Bures loss 2(1-f_ij)<=2(1-A_ij). Also the standard fidelity inequalities imply ||rho_i-rho_j||_1^2<=4[2(1-f_ij)]<=4[2(1-A_ij)]. Averaging gives

    R_B(PGM)<=Q_n<=2 delta_n,
    R_trace_squared(PGM)<=4Q_n<=8 delta_n.

Hence a bound on delta_n would directly control an actual classical-output measurement, without the stronger false inference that the Umegaki prediction risk equals delta_n. This result, if accepted, repairs only the measurement-level gate from the latest coding-gap assessment. It does not establish the Gibbs increment bound.

For completeness, delta_n=S(B|C_n)-sum_i p_iS(rho_i) is nonnegative and nonincreasing: positivity follows from the classical latent-label factorization; monotonicity follows from strong subadditivity after adding one more conditionally independent copy. Therefore

    delta_(2n-1) <= [chi_(2n)-chi_n]/n.

A uniform dyadic bound would consequently control the PGM at 2n-1 copies. Using two unknown sources would charge 4n-2 original copies. No dyadic bound is claimed here.

## 4. Finite diagnostic scope

The adjacent scripts are authored floating-point checks, not proofs or certified estimates. The initial scan covered 1,800 random mixed ensembles with d=2,3,4 and n=1,2,3 (not every combination), giving maximum Q_n/delta_n about 1.223. An adversarial scan with log-uniform eigenvalues/prior weights covered 2,650 ensembles with d=2,3,4 and n up to 6, giving maximum about 1.752. These generic matrix ensembles are NOT all admitted coefficient-bounded fixed-beta Gibbs candidates. They test the proposed dimension-independent matrix inequality only. A separate 10,000-channel random CPTP diagnostic found no negative value of Delta+log x. No finite scan establishes universal validity.

The checker's eigenvalue floor and floating-point entropy cutoffs mean these are diagnostics only. The full mathematical argument above, particularly interpolation and the exact Gram reduction, was separately hand-reviewed as recorded in independent-review/REVIEW.md. The finite scans are not the basis of the general theorem.

## 5. Primary interpolation reference and bounded source review

The norm interpolation used in Section 1 is the standard analytic-matrix three-lines theorem, not a newly claimed tool. A directly checked primary source is Salman Beigi, *Sandwiched Renyi Divergence Satisfies Data Processing Inequality*, arXiv:1306.5920v6 (22 November 2013), Section III, Theorem 2, PDF pages 5–6: https://arxiv.org/pdf/1306.5920 . Take the theorem's norm weight to be the identity. Its stated exponent ordering can be matched by reversing the strip. Section II, equation (8), supplies the product Schatten Holder inequality. The present specific channel function and Gram substitution are supplied explicitly above rather than attributed to a result not checked in that source. This is a bounded method-source check, not an exhaustive prior-work or novelty audit.

On each finite strip, F is bounded: r and sigma are positive definite, their imaginary powers are unitary, their real powers stay bounded on a compact real interval, and Phi is a finite-dimensional bounded linear map. This verifies the analytic theorem's boundedness hypothesis as well as holomorphy and boundary continuity. For any CPTP Phi, every output is supported on support Phi(I): positivity gives Phi(X)<=||X|| Phi(I) for positive X, and the full operator space follows by linear decomposition. Restricting to this support is legitimate before applying the fixed-sigma regularization argument.

## 6. Review and revision record

This successor preserves the proof and scope of the producing-pass candidate, SHA256 8e5c297dbe9a4a02631bf180c67c1c8981b33f5959ec56bb774feb492bfe94ec. Changes are status/review wording and this review record. The unchanged candidate is included. The independent review supplies a self-contained duality proof of the varying-Schatten interpolation and a separately authored exact algebraic fixture. Its fixture has x=61299/62500 and Q=1201/31250; it verifies finite Gram and weight identities, not the uniform entropy theorem.

Additional admitted-Gibbs floating-point checks in diagnostics/check_gibbs_gram.py and .log cover 80 finite priors at beta=0.8: one-qubit n=1,2,3 and two-qubit n=1, with every Pauli coefficient in [-1,1]. All Gram identities passed with maximum residual below 3.6e-15. These bounded controls do not establish a growing-N Gibbs increment bound.

For nonfaithful finite candidates, use the direct-sum output support C tensor supp(rho_i), as detailed in the independent review. The quarter-power block identity continues to hold there; complete the PGM arbitrarily off supp(S), which has zero ensemble mass. Thus the finite-ensemble claim is not restricted to faithful states.

A separate bounded primary-source applicability note is included at literature-cross-review/PRIMARY-SOURCE-COVERAGE.md. It verifies the interpolation supplier and distinguishes nearby entropy-gain, PGM/recovery, and fixed-dimensional coding results. It does not certify novelty or the remaining Gibbs increment rate.
