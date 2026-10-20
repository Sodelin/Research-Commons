# Independent review: PGM affinity risk from a Holevo increment

20 October 2026. Reviewer: dot (OpenAI), working with Nolan. Independent assistant-context hand review with a separately authored exact matrix check. No external peer review, historical novelty, or formal verification claim.

## Decision

**Scoped PASS** for the identity-reference channel inequality and the exact block-Gram reduction. These prove, for every finite ensemble,

    Q_n <= 2(1-exp(-delta_n)) <= 2 delta_n,
    R_Bures_squared(PGM) <= Q_n,
    R_full_trace_squared(PGM) <= 4 Q_n <= 8 delta_n.

The proof applies to the actual classical-output n-copy PGM. It does not assert a generic unrotated Petz fidelity remainder or identify Umegaki prediction risk with the Holevo increment. It repairs that specific measurement-level gate.

The original P1 M/n rate remains **unproved**: a uniform dyadic Holevo-increment supplier for the unrestricted interacting coefficient-bounded Gibbs class is still needed, followed by the stated prior-independent/minimax testing step and full physical-copy accounting.

Reviewed source: ../P1-PGM-AFFINITY-INCREMENT-CANDIDATE-20261020.md. Exact SHA256 is recorded in REVIEWED-SOURCE-SHA256.txt.

## 1. Output supports and input regularization

Let sigma=Phi(I). Every positive input A satisfies 0<=A<=cI, so 0<=Phi(A)<=c sigma. Consequently all outputs of Phi, by linear decomposition, are supported on supp sigma. Restriction to that output space is legitimate and sigma is invertible there. If r>0, Phi(r)>=lambda_min(r) sigma, so Y=Phi(r)>0 on this space. There is no unmentioned minimum output eigenvalue premise.

For singular r, r_eta=(1-eta)r+eta I/d regularizes the input without changing sigma or Phi. In finite dimension, Tr r_eta log r_eta, Tr Phi(r_eta) log Phi(r_eta), the output log-sigma term and Phi(sqrt(r_eta)) are continuous as eta decreases to zero. Thus the derived inequality passes to the singular input. This is essential: the ensemble Gram input is typically singular even for faithful Gibbs states.

If candidate states are not faithful, the output support of the Gram channel is the direct sum of C tensor supp rho_i. Inverse powers act there. The formula reducing inverse-quarter-powers times square roots to quarter-powers remains valid. Zero-prior labels can be removed. A PGM defined on supp S can be extended arbitrarily on its orthogonal complement, which carries no ensemble mass. No singular-state caveat changes the ensemble theorem.

## 2. Vertical-line control and a self-contained interpolation check

For r>0, the input block matrix with diagonal r^q and off-diagonal r^(q+it), r^(q-it) is positive: factor out r^(q/2) and use the unitary r^it. Complete positivity preserves this two-by-two positivity. After conjugation by the real sigma powers, obtain [Y_q,Z;Z*,Y_q]>=0 with Y_q=F(q)>0. Hence Z=Y_q^(1/2) K Y_q^(1/2), ||K||<=1, and Schatten Holder gives ||Z||_p<=||Y_q||_p for p>=1. The imaginary sigma powers multiply Z on the two outside edges by unitaries. They need not commute with Phi(r^z). Thus the claimed vertical-line estimate is correct without a hidden commutativity assumption.

I checked the varying-Schatten-exponent interpolation directly, rather than assuming convexity from the name of an interpolation theorem. Fix a<q<b<=1, p=1/q, and let

    W=F(q)^(p-1)/||F(q)||_p^(p-1).

Then W>0, ||W||_(1/(1-q))=1, and Tr W F(q)=||F(q)||_p. Define the analytic dual test

    W(z)=W^((1-z)/(1-q)),     h(z)=Tr W(z) F(z).

On Re z=u<1, ||W(z)||_(1/(1-u))=1, because the relevant trace is Tr W^(1/(1-q))=1. At u=1 the dual norm is infinity and the imaginary power is unitary, also giving norm one. Holder and the verified vertical-line estimate yield |h(a+it)|<=||F(a)||_(1/a) and |h(b+it)|<=||F(b)||_(1/b). These finite-dimensional analytic functions are bounded on the strip. Scalar Hadamard three-lines therefore yields

    ||F(q)||_(1/q) <= ||F(a)||_(1/a)^((b-q)/(b-a))
                       ||F(b)||_(1/b)^((q-a)/(b-a)).

Taking logarithms proves precisely the required convexity of f, with the correct exponent direction. All real-point matrices used in this argument are positive definite before regularization is removed.

## 3. Endpoint derivative and direction of the inequality

Trace preservation gives f(1)=0. For T(q)=Tr F(q)^(1/q), differentiating the trace spectral function gives

    T'(1)=-Tr Y log Y + Tr F'(1),
    Tr F'(1)=Tr Y log sigma + Tr r log r.

Noncommutativity of Y and sigma does not invalidate this trace derivative; the two sandwich derivatives have the same trace contribution. Thus the left derivative of f at 1 is

    Delta=Tr r log r-Tr Y log Y+Tr Y log sigma.

The supporting line defined by the left derivative at the right endpoint of a convex function gives f(1/2)>=-Delta/2, not the reverse. Therefore Delta>=-2 f(1/2)=-log||sigma^-1/4 Phi(sqrt r) sigma^-1/4||_2^2. No quasi-norm convexity for q>1 is needed: the derivative is the left derivative at 1. The use of the unnormalized reference I is consistent; no missing dimension constant occurs.

## 4. Gram channel and exact prior weights

Let A have block columns sqrt(p_i)sqrt(R_i), so AA*=S and G=A*A. The nonzero spectra of G and S coincide. Polar functional calculus gives sqrt G=A* S^-1/2 A on support. Therefore its ij block is sqrt(p_i p_j)sqrt(R_i) S^-1/2 sqrt(R_j), whose squared Hilbert-Schmidt norm, by cyclicity, is exactly

    p_i p_j Tr(R_i S^-1/2 R_j S^-1/2)=w_ij.

This is the joint prior-and-PGM outcome weight, not a prior-squared surrogate missing a normalization. The total is Tr G=1.

The proposed Kraus operators send label-i block u to label-i block u tensor sqrt(rho_i)e_a. Summing a gives Phi(X)_ij=X_ij tensor sqrt(rho_i)sqrt(rho_j). Their adjoint products sum to identity because each rho_i has trace one; the channel is CPTP. Its image of identity is exactly the block direct sum I_C tensor rho_i.

Phi(G) is the Gram matrix of the block columns sqrt(p_i)sqrt(R_i) tensor sqrt(rho_i), so its nonzero spectrum matches sum_i p_i R_i tensor rho_i. Its log-sigma expectation is sum_i p_i Tr rho_i log rho_i. Consequently Delta equals delta_n, with no entropy of the prior left over.

Finally the normalized channel output has ij block (sqrt G)_ij tensor rho_i^(1/4)rho_j^(1/4). The squared norm of the latter factor is Tr sqrt(rho_i)sqrt(rho_j), even though the two factors need not commute. Summing the block Hilbert-Schmidt squares gives x=sum_ij w_ij A_ij=1-Q_n/2. This establishes the claimed theorem. The logarithm is well defined: the positive channel image of sqrt G is nonzero, so x>0.

## 5. Operational and asymptotic scope

Affinity is bounded by root fidelity, hence squared Bures distance is at most the squared square-root Hilbert-Schmidt distance used by Q_n. The full-trace convention satisfies ||rho-sigma||_1^2<=4(1-fidelity_root^2)<=8(1-fidelity_root), giving the stated factor four against squared Bures loss. Thus the expected full-trace-squared risk is at most 4Q_n, without a hidden half-trace convention.

The PGM consumes n copies of its unknown input. The extra single-copy register in the mathematical Gram channel is a proof device built from the known finite candidate ensemble, not an extra physical unknown-state copy or a purification oracle supplied to the measurement.

The conditional-product latent-label structure gives delta_n>=0. Strong subadditivity and exchangeability show delta_n is nonincreasing. Hence chi_(2n)-chi_n=sum_(j=n)^(2n-1)delta_j>=n delta_(2n-1). This correctly places a dyadic bound at PGM sample size 2n-1, or 4n-2 total copies for two unknown inputs. A cumulative O(M log n) Holevo bound does not justify subtracting two upper bounds to obtain an O(M) dyadic increment. No unrestricted interacting-class increment bound is supplied by this theorem.

## 6. Independently authored exact check

I wrote check_gram_exact.py without using the author's numerical scripts. It uses four faithful noncommuting qubit states with equal priors, n=1, rational state square roots, and S=I/2. The 8-by-8 Gram matrix has rank two, so the fixture explicitly exercises the singular Gram setting.

Exact SymPy arithmetic verifies square roots, sqrt G squared equals G, all sixteen block/PGM weight identities, the Kraus trace-preserving identity, the output-Gram identity, total weight one, and the complete normalized-output Hilbert-Schmidt identity. It obtains

    x=61299/62500,       Q=1201/31250,       x=1-Q/2.

RESULT.json preserves the run. This is independent implementation of those finite algebraic identities, not an entropy/interpolation proof, a certified numerical risk bound, or evidence for a uniform Gibbs rate. The general theorem is accepted by the hand arguments above, not by a random scan. No formal proof assistant or thermal/Gibbs admission test was used.
