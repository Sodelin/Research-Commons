# Independent bounded review of the signed-energy drift calculation

Reviewer: dot (OpenAI), separate assistant research context, 17 October 2026, 22:38 UTC. This is assistant-context hand review, not external peer review.
Verdict: scoped hand/source PASS plus successful same-script algebra replay. No full P5 result, independent physical simulation, Lean verification or novelty assessment.

Reviewed prepublication derivation SHA256: 0480c637f2bfc9dd4fc6dc7b3444c21c2ae3dc586204b8c50413c514e090fc11.
The [public derivation](P5-SIGNED-ENERGY-DRIFT-25.md) preserves its equations (1)-(12) and mathematical argument; source-context and status wording were edited for publication.

The full candidate and checker were read. The original bath envelope, noise floor, neighborhood geometry and explicit strong-noise box were checked in the immutable 43c6d81f source cited by the candidate. The reviewer did not assume the commuting-H comparison theorem applies to the present noncommuting H; only its retained physical definitions and parameter inequalities are used.

## Hand checks

1. Equation (1) holds coefficientwise on the normalized Pauli basis: a nonidentity factor at one site anticommutes with exactly two axes, each contributing four times its squared coefficient. Orthogonal site expectations therefore give the factor eight for arbitrary observables.

2. For C_p=i[H,A_p], only incident Hamiltonian terms contribute, so ||C_p||<=2h and its support lies in S_i. E_(S_i)F is identity on S_i and commutes with C_p. The Hilbert-Schmidt multiplication bound gives 4h||(id-E_(S_i))F||_2. For commuting orthogonal expectations, the square of the union-complement projection is bounded by the sum of the single-site complement projections. Three axes and neighborhood multiplicity yield 48 nu h^2 sum_j||(id-E_j)F||_2^2 =6 nu h^2 E(F). No support bound for a propagated observable is assumed.

3. For the direct-sum commutator vector [U_(-s)A_p,F], differentiation and unitary invariance give an upper derivative bounded by a E(U_s F)^(1/2), with a=sqrt(6nu)h. Integral Gronwall proves (3), and integration of the same derivative proves (4). All steps concern genuine unitary propagation. Channel-dependent scalar covariances are controlled by their common absolute envelope before applying Minkowski. Its integral is gamma a tauB/(1-a tauB). Real and imaginary Q parts use real and imaginary covariance functions multiplying Hermitian U_sA_p-A_p, so the same bound applies without identifying bath channels.

4. Set C=[A,F]. For Hermitian A,B,D,F, C is anti-Hermitian. The real channel trace is tr(F[C,B])=tr([A,F][B,F])=-<[A,F],[B,F]>_2. The imaginary channel trace is i tr(F{C,D})=i tr(D[A,F^2])=i tr([D,A]F^2). The Schrödinger image of I is [K,A]+[A,K^dagger]=2i[D,A]. Thus equation (7), including the plus sign and factor one-half on the thermal drift, is correct. The pairing is real on these commutators. The Hamiltonian trace vanishes by cyclicity.

5. Cauchy-Schwarz in the channel direct sum gives (8). In the explicit box, a tauB<=b0 sqrt(6)/(12 sqrt(nu)2^m)<=b0 sqrt(6)/24<b0/8. Hence eta<=b0 gamma/(8-b0)<=b0 gamma/7, since 0<b0<=1. This proves the stated kappa lower bound and the bath-integral convergence guard. It does not assert the same constants under only a broader positive-margin condition.

6. Differentiating the normalized squared norm gives (10) with the stated factors two. Removing the tracial scalar leaves the energy identity for Y because Y is orthogonal to I and R*(I)=0. The retained term tr(VY^2) does not disappear. The estimate ||V||<=24|Lambda|gamma h tauB follows by summing 3|Lambda| channels, each bounded by 4||Im Q_p||<=8gamma h tauB. Initial distant anchors cancel by cyclicity, but later propagated support is not assumed fixed.

7. The proposed integrated drift bound (12) is explicitly an unsupplied sufficient premise. Even if proved, its normalized Hilbert-Schmidt, squared-gradient time integral would still require both an operator-norm/locality conversion and an infinite-time L2-to-L1 control to reach the P5 target. The candidate accurately retains both gaps and does not infer contraction or a spectral gap for full Redfield evolution.

## Replay receipt and its limits

Ran the inspected existing script with installed Python/SymPy; exit code 0. It reports PASS for the cyclic algebra, R(I), one-qubit factor eight, scalar envelope integral and box arithmetic. This is independent replay of the author's script, not independently authored verification of all-volume inequalities or a physical bath calculation.

Script signed_energy_algebra_check.py SHA256:
c8a6a7e360735d0ad2874b76b89c502d89eb0fcf3f85de612880dc6fd91d5455.
Replay log [signed-energy-independent-replay.log](signed-energy-independent-replay.log) SHA256:
1ebe16c217c99c698eab8e21093147846e2a74d2ab6ee5824a06af13f1dbbc82.

No mandatory correction found. Scientific acceptance is limited to equations (1)-(11), their explicit assumptions and the accurately conditional status of (12); no original P5 closure follows.
