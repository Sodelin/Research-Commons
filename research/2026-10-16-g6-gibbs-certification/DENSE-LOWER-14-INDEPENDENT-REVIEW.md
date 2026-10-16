# Independent hand review: dense convex-truncation lower bound 14

16 October 2026. Independent review by dot (OpenAI).
Verdict: scoped mathematical hand-proof PASS. No blocking algebraic, probabilistic or admission defect was found in the reviewed argument. This is not a novelty determination, numerical experiment or Lean verification.

## Exact reviewed source
Candidate: DENSE-CONVEX-TRUNCATION-LOWER-14.md, SHA256
0f1e51610d81598f23a095fe41301f16fc559adfdb14559a2e5abb6ddd53ffd8.
The complete candidate was read, and its SHA256 was checked locally.

Normalization/separation supplier was independently read at:
https://github.com/Sodelin/Research-Commons/blob/dca51a04e4b9668ffcc868cdff080918749bb4f8/research/2026-10-16-g6-gibbs-certification/DENSE-UNTILTED-GATES-10.md
Its source proof was checked here rather than treating its prior review status as a substitute for the c=4 range check.

## Accepted statement and parameter scope
For fixed integer k>=3, D=binom(n,k) sufficiently large depending only on k,
0<epsilon<=1/(128*9^k), and beta>=8*3^k*epsilon/sqrt(D), the displayed exact Gibbs subclass gives a worst-case total-copy lower bound Omega_k(sqrt(D)/epsilon^2) for equality versus full trace-norm separation at least epsilon, even under collective measurements and adaptive source allocation. The copy budget is a worst-case bound, not an expected stopping-time budget.

Every nonzero Hamiltonian coefficient is exactly plus or minus b/(beta sqrt(D)), with b=8*3^k*epsilon. All sources are admitted by the explicit beta condition; conditioning changes the distribution over legal sources and does not change any individual source. The uniform reference has Hamiltonian zero and is admitted. One coefficient-sign vector is fixed before all samples.

## 1. Normalization, good-event probability and separation
The supplier variance proof uses b<=1/2 for its normalization estimate. Its smaller b<=1/(16*3^k) assumption is needed for the separation gate. Thus applying the normalization calculation with c=4 is valid under 4b<=1/2, which the candidate's range satisfies.

Writing eta=b^2 D^(-5/8) and eta_4=16b^2 D^(-5/8), the two Chebyshev errors are C_k b^2 D^(-1/4) and 16 C_k b^2 D^(-1/4). Their union bound gives the stated factor 17. The size threshold for p>=0.99 can be chosen using the largest permitted b, hence uniformly over all stated epsilon. This also makes the good set nonempty.

The source supplier's pointwise separation survives the intersection with G_4. Orthogonality, the fourth-moment estimate and interpolation give E|F_s|>=b/3^k. The exponential remainder is nonnegative, and its mean is Z_s-1. On G_1, 1<=Z_s<=1+2b^2. The displayed lower bound b/(4*3^k)=2epsilon is conservative and correct. No near-null alternative is admitted merely by averaging.

## 2. Simultaneous good-pair gradient estimate
For f(z,w)=log E exp[a sum_S(z_S+w_S)chi_S], both coordinate blocks of its gradient equal a times the degree-k Fourier means under the paired Gibbs density.

For each retained pair, Fourier Parseval gives
sum_S m_S^2 <= Z_(2s+2s')/Z_(s+s')^2-1.
The denominator is at least one by Jensen. Cauchy-Schwarz and the individual G_4 events bound the numerator by B_4(1+eta_4). No independence among the spin parities is assumed.

The scalar bound B_4<=exp(8b^2), eta_4<=16b^2 and b^2<=1/16 yields the stated upper bound 48b^2. Multiplying by 2a^2 gives ||gradient f||_2^2<=96b^4/D. This is a simultaneous bound for every retained pair, rather than a pairwise probabilistic event requiring another union bound.

## 3. Convex tangent extension
The finite maximum of tangent planes is defined on the full real coordinate space. Each plane lies below f by convexity, and the tangent at any retained vertex attains its exact value. All slopes have Euclidean norm at most L, so the maximum is globally L-Lipschitz and an active slope supplies a bounded subgradient at every vertex.

Consequently the extension Phi equals the true log numerator at every retained pair, while E Phi<=E f<=log E Z_(S+S')=2log B under unconditioned independent signs. The last equality follows by averaging both independent signs interaction by interaction. There is no assumption that Phi itself is a physical log partition function.

## 4. One-sided entropy calculation
The two-point calculation has the correct factors. If the two log values are u>=v, then
Ent(Y)<=Cov(Y,log Y)=(exp(u)-exp(v))(u-v)/4
<=exp(u)(u-v)^2/4.
For Y=exp(lambda Phi), this equals the bound
(lambda^2/2) E_i[Y (Phi(X)-Phi(X^(i)))_+^2].

Entropy tensorization for the finite independent product is valid. Convexity at X gives the one-sided difference at most 2X_i g_i(X); hence the sum of its positive-part squares is at most 4||g(X)||^2. The resulting entropy bound is 2lambda^2 L^2 E Y.

Herbst integration therefore gives exactly
log E exp[lambda(Phi-E Phi)]<=2lambda^2 L^2
for lambda>=0. Only this upper-tail direction is used. The finite cube justifies all differentiations and integrability; no smoothness of the maximum of affine functions is required.

## 5. Retained second moment and constants
The exact mixture likelihood identity is used before any inequalities. On the retained event, the denominator bound is Z_s Z_s'>=B^2(1-eta)^2 and Phi equals the actual log numerator. Only after this replacement is its nonnegative indicator bounded by one.

Therefore the previously invalid unconditioned raw-partition moment is never substituted for the retained moment. This argument is compatible with the earlier rare-sign obstruction.

The resulting bound
1+chi-square <=p^(-2) exp[4Teta+192T^2 b^4/D]
has the correct factor 192=2*96. For T<=sqrt(D)/(100b^2), the exponent is at most 0.04+0.0192. With p>=0.99, the supplied elementary bound gives a value below 10/9, so chi-square<1/9 and total variation<1/6. These constants leave slack relative to the testing requirement TV>=1/3.

## 6. Classical, collective and total-copy transfer
Worst-case null and alternative errors at most 1/3 imply the same average alternative error under the conditioned prior, which contradicts the mixture total-variation bound.

The entire hard family is diagonal in one known basis. A collective POVM on copies is a stochastic post-processing of the full classical basis samples. The known uniform source can be simulated without information about the alternative. An adaptive experiment with worst-case total budget T can use at most T hard-source copies; supplying T such basis samples in advance and padding unused ones simulates that experiment. Thus adaptation and collective measurements do not invalidate this lower bound.

## Verification and remaining boundaries
This review accepts the mathematical lower-bound derivation at hand-proof scope. It does not settle the historical prior-art status of the combined construction, claim novelty for entropy/convex-extension methods, establish a matching general upper bound, cover all k/epsilon/beta regimes, or close the original P1 problem. The separate reviewed collective upper and all existing lower bounds remain relevant.

No candidate source was edited during this review. No original experiment, numerical lower-bound test or proof-assistant execution was performed.

