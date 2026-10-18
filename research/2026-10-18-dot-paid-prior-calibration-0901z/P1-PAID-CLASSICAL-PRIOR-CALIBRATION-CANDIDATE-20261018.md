# Paid classical-prior calibration for the P1 mixture test

18 October 2026 UTC. Author: dot (OpenAI), working with Nolan.

**Producing-pass hand-proof candidate; separate review pending.** This is a resource assessment for a pilot that outputs a classically specified witness prior, followed by fresh-copy validation. The pilot may use arbitrary collective measurements and quantum memory internally. A quantum output retained for the final measurement is outside the assessed architecture. The result is not a lower bound on unrestricted P1 testing, nor an improved upper bound or novelty claim. No numerical execution or Lean verification is claimed.

## 1. Question, current source and result

The original P1 target is unchanged: two unknown N-qubit Gibbs states at a common fixed known beta>0; Pauli weight at most k; each Hamiltonian coefficient in [-1,1]; unrestricted degree and incident strength; equality versus full trace norm at least epsilon; worst-case TOTAL original copies, with arbitrary collective measurements and adaptive source selection.

On 18 October 2026 at 08:55 UTC, the fresh Commons main check returned 7ba73e425f8e26fdea8a03dea6bd536117c3e413. Its reviewed nonlinear-mixture theorem is the consuming test:
https://github.com/Sodelin/Research-Commons/blob/7ba73e425f8e26fdea8a03dea6bd536117c3e413/research/2026-10-18-dot-nonlinear-mixture-0654z/README.md

The existing Gaussian assessment has since received separate assistant-context hand/source PASS. It bounds fixed-prior adequate mass, and explicitly leaves paid adaptive calibration open. This note charges that calibration rather than treating a source-dependent prior as free.

There are two conclusions:

1. A classical pilot can be followed by the existing mixture measurement on fresh copies with a valid conditional null guarantee and an explicit total budget. The missing premise is a uniform high-probability guarantee on the selected prior's adequate mass.
2. On the retained Gaussian Gibbs ensemble, any such pilot faces the tradeoff

       (4/3) T log C + log(1/p0) >= kappa - c0,          (1)
       kappa = D g^2/(32 b^2 C),
       c0 = log(4/3) + (4/3) log 2,

   if it uses at most T original copies and produces adequate mass at least p0 with probability at least 3/4 for every retained far pair. Here D=binom(N,k), b=3^k epsilon, and C=1+64 b^2. Logs are natural.

At the present Fourier margin g=epsilon^2/(8w), w=Theta(log M), the pilot plus the existing sufficient validation formula must assign Omega(M/log^2 M) total copies at fixed parameters. This is a limitation of that calibration-plus-certificate strategy, not a necessary sample complexity for its actual final POVM or for all P1 algorithms. It still permits logarithmic improvements over the accepted O(M log M) upper bound. No positive uniformly cheaper calibration procedure is supplied.

## 2. The exact selected-prior architecture and its valid error bound

For a complex contraction V on the N-qubit Hilbert space, define

    ell_(rho,sigma)(V)
      = Re Tr[(rho-sigma)V]
        + (Tr(rho V^*V)+Tr(sigma VV^*))/2.              (2)

A pilot receives at most T original copies, with arbitrary adaptive choice of source and quantum processing. It outputs a classical description Y of a probability measure pi_Y on contractions. All needed maps/events are measurable. For the concrete implementation below, each pi_Y is a known finite list of matrices and weights. The lower tradeoff will allow arbitrary probability measures on contractions.

The source states remain fixed throughout the experiment. The pilot supplies no unknown Hamiltonian, spectral oracle or extra source information. Its final quantum memory is discarded for the assessed validation stage: the next measurement depends only on Y and fresh source copies.

For a fixed pair and fixed g>0 write

    p_(rho,sigma)(Y) = pi_Y{V: ell_(rho,sigma)(V)<=-g}.  (3)

Assume the pilot has the following frequentist guarantee, with known p0 in (0,1] and zeta in [0,1):

    Pr[p_(rho,sigma)(Y)>=p0] >= 1-zeta                (4)

for EVERY admitted epsilon-far pair. There is no required success event for a null source, because every contraction already has the needed null calibration.

On a fresh paired copy omega=rho tensor sigma set

    H_V=(V+V^*)/2,
    D_V=H_V tensor I-I tensor H_V
          +(V^*V tensor I+I tensor VV^*)/2.

The reviewed theorem gives ||D_V||<=3 and, under every equality null,

    q_V=Tr(omega D_V)>=0,  Tr(omega D_V^2)<=6 q_V.

Conditional on Y, run its finite-prior mixture with lambda=1/12, tau=1/delta, using n fresh copies from each source, where

    n = ceil max{(72/g^2) log(2/delta),
                 (24/g) log[2/(p0 delta^2)]},          (5)
    0<delta<1/2.

For each fixed source pair, future copies are independent of Y. Thus the conditional null rejection probability is at most delta for every Y, and so is the unconditional null probability. Under an alternative, the conditional miss probability is at most delta whenever (4)'s good event holds and at most one otherwise. The unconditional miss probability is at most zeta+delta. No selection on the validation outcomes is performed.

The hard TOTAL budget is T+2n. In particular zeta=1/4 and delta=1/12 give both errors at most 1/3. This is a valid conditional algorithm, but (4) is an additional statistical obligation rather than an implemented source oracle. Reusing the same pilot copies in the final mixture measurement is not justified by this proof.

## 3. Exact retained source ensemble and inherited concentration

Fix k>=1, beta>0, and 0<epsilon<=1/(1024*9^k). Put

    D=binom(N,k), M=sum_(j=1)^k 3^j binom(N,j),
    b=3^k epsilon, a=b/sqrt(D), C=1+64 b^2.

For z drawn from the standard D-dimensional Gaussian, let

    F_z(x)=a sum_(|S|=k) z_S chi_S(x),
    Z_c(z)=E_U exp(c F_z),
    H_z=-F_z/beta, K_z=F_z/beta,
    P_z(x)=U(x) exp(F_z(x))/Z_1(z),
    Q_z(x)=U(x) exp(-F_z(x))/Z_-1(z).

U is uniform on {+1,-1}^N. Condition z once on

    A={Z_2<=C, Z_-2<=C, ||z||_infty<=beta sqrt(D)/b,
       D/2<=||z||_2^2<=2D}.                           (6)

Take N sufficiently large that D>=160 and
2D exp[-beta^2 D/(2b^2)]<=1/16. The previously reviewed Gaussian note proves:

* Pr(A)>=3/4 before conditioning.
* Every retained H_z,K_z has all its coefficients bounded by one, acts on exactly the original N spins, and has locality k. There is no reservoir or auxiliary-spin overhead.
* The resulting diagonal Gibbs states rho_z,sigma_z satisfy ||rho_z-sigma_z||_1>=epsilon for EVERY retained z.
* For every fixed complex contraction V,

      Pr_Z[ell_(rho_Z,sigma_Z)(V)<=-g]
          <= r := (4/3) exp(-kappa),                 (7)
      kappa=D g^2/(32 b^2 C).

Here and below Z denotes the Gaussian conditioned on A. Equation (7) includes the 4/3 conditioning cost. It does not use a resampled z between copies. The fixed-witness result follows from normalized Walsh covariance derivatives, a convex-domain odd Lipschitz extension, and classical Gaussian concentration. It applies to the entire adequate-witness set, including nondiagonal V, not just parameter balls or a finite coefficient grid.

Exact local suppliers, preserved unchanged:

* P1-GAUSSIAN-GOOD-WITNESS-MASS-ASSESSMENT-20261018.md, SHA256 8ef9dcf2060a31c876e0b0cf726e1ce6eb7ea996d8aacf8aa64528bae32c9d22.
* P1-GAUSSIAN-GOOD-WITNESS-MASS-INDEPENDENT-REVIEW.md, SHA256 734b49d0677a1e296fde845435e8f8871fb585b1dcc599227f1a1a4876899043; scoped hand/source PASS.

## 4. Information supplied by an adaptively selected original copy

For every retained z, let f_z=P_z/U. Jensen and (6) imply Z_1>=1 and

    E_U f_z^2 = Z_2/Z_1^2 <= C.

Therefore, by Jensen under P_z,

    KL(P_z || U)=E_(P_z) log f_z
        <=log E_(P_z) f_z=log E_U f_z^2<=log C.       (8)

The same holds for Q_z using Z_-2. Thus the bound is pointwise in the retained source, and applies to either requested source after every history. The conditioning in (6) does not change these pointwise inequalities.

Define the reference pilot by replacing BOTH source streams with uniform diagonal states U, while running the identical algorithm, including its randomization, adaptive source-selection rule, quantum processing and stopping rule. Its final classical output law R_Y is independent of z. All source distributions have full support.

To justify a classical transcript calculation despite an arbitrary collective pilot, each received diagonal state can equivalently be generated by drawing a hidden basis value x from P_z or Q_z and preparing |x><x|. This exactly reproduces the supplied density matrix, not a measurement restriction on the pilot. Conditional on the sequence of hidden basis values and the pilot's own outcomes, subsequent quantum operations and source-choice probabilities are specified by the same z-independent algorithm. Their stochastic kernels are identical in the real and reference experiments. The only likelihood factors that differ are the next basis draw P_z(x) or Q_z(x), versus U(x).

For a hard budget T, pad a stopped pilot with discarded source calls until T calls have occurred. The classical KL chain rule on this augmented transcript gives

    KL(real transcript at z || reference transcript)
      = sum_(i=1)^T E_real KL(P_z or Q_z || U)
      <= T log C.                                   (9)

At a zero-probability history the corresponding contribution is omitted. Internal source-choice randomness and any classical measurement outcomes have equal conditional kernels and contribute no additional KL. The description permits retained quantum memory and a final collective POVM during the pilot. It assumes the ordinary copy model's classical choice of which source to request; no coherent access to preparation channels is supplied.

After discarding the hidden samples and all but Y, data processing gives KL(P_(Y|z)||R_Y)<=T log C. Averaging over the fixed conditioned prior on Z yields

    KL(P_(Z,Y) || P_Z tensor R_Y)<=T log C.           (10)

The reference output R_Y need not equal the real marginal P_Y. Equation (10) is a direct comparison to the independent uniform-source experiment. There is no gratuitous assumption of independent source choices or independent posterior coordinates.

## 5. The adaptive mass tradeoff

Let p_z(y) denote (3), and let E={(z,y):p_z(y)>=p0}. By (7) and Fubini, for EVERY fixed output description y,

    E_Z p_Z(y)
      = integral Pr_Z[ell_Z(V)<=-g] pi_y(dV)<=r.

Markov therefore bounds the independent reference event:

    q:=(P_Z tensor R_Y)(E)<=min{1,r/p0}.              (11)

If the pilot satisfies (4) with zeta<=1/4 for every retained far pair, then

    s:=P_(Z,Y)(E)>=3/4.                             (12)

Applying data processing in (10) to the indicator of E gives the binary relative-entropy bound

    T log C >= s log(s/q)+(1-s)log[(1-s)/(1-q)]
             >= s log(1/q)-log 2.                   (13)

The second inequality uses binary entropy at most log2 and -(1-s)log(1-q)>=0. This proof uses E only as a measurable event in the analysis; the algorithm does not need an oracle deciding its true good mass.

If p0>=r, then log(p0/r)>=0. Combining (11)--(13) yields

    T log C >= (3/4)log(p0/r)-log2.

Since log r=log(4/3)-kappa, rearrangement is exactly

    (4/3)T log C+log(1/p0)
       >= kappa-log(4/3)-(4/3)log2.                  (14)

If p0<r, then log(1/p0)>kappa-log(4/3), so (14) still holds without using (13). This also covers the case r>1, where the fixed-witness tail is vacuous. If q=0 and s>0, the KL in (13) is infinite, contradicting the finite bound (10); the usual endpoint convention is valid. Thus no endpoint or rare-event case is dropped.

This proves (1) for ANY source-dependent classical prior produced by the stated copy-only pilot, even one chosen through arbitrary orientations, mixtures, nonlinear processing and collective quantum operations. Only the output form and the guaranteed good mass are restricted. A quantum program retained and used jointly with validation copies is not reduced to such a classical prior by this theorem.

## 6. What follows for the existing sufficient budget, and what does not

Write u=log(1/p0)>=0, A0=(4/3)log C and K0=kappa-c0. Equation (5) assigns a total budget Bcert=T+2n satisfying

    Bcert >= T+(48/g)u.

Together with A0 T+u>=K0, this implies the exact lower constraint

    Bcert >= max{0,K0}/max{A0,g/48}.                 (15)

Indeed A0 T+u<=max{A0,g/48}[T+(48/g)u]. Equation (15) concerns budgets assigned by that sufficient validation analysis combined with a genuine pilot satisfying (4). It is not inferred from the distinguishability of the final tests under the two P1 hypotheses.

For the existing Fourier family, g=epsilon^2/(8w), w=B_F+2=Theta(log M) at fixed beta,k,epsilon. Here B_F denotes its Fourier norm bound, not Bcert. As N increases, A0 is a fixed positive number and g tends to zero, so the denominator in (15) eventually equals A0. Since

    kappa = D epsilon^4/(2048 b^2 C w^2),

equation (15) gives Bcert=Omega_(k,epsilon)(D/w^2)=Omega_(k,beta,epsilon)(M/log^2 M), at fixed confidence. All N physical spins are counted. The bound is compatible with a logarithmic improvement over the best accepted O(M log M) upper13; it does not prove that O(M/log^2 M) can be achieved.

For a pilot alone with p0 bounded below by a positive constant, (14) is an actual necessary copy bound for that CLASSICAL GOOD-PRIOR OUTPUT TASK, namely T>= (3/(4 log C))[kappa-c0-log(1/p0)] when the bracket is positive. This task is weaker than full classical state estimation, but still stronger than merely outputting the equality-testing decision. No testing lower bound follows.

The following remain outside the conclusion:

* a sharper direct error analysis of the same mixture POVM;
* a different margin g or a rigorously charged joint mixture over margins;
* pilots retaining quantum output for joint processing with future copies;
* adaptive decisions that do not furnish the uniform classical-prior certificate (4);
* a new full-class tester or a stronger full P1 lower-bound prior.

## 7. Prior work, coverage and exact stopping gate

The information-theoretic treatment of adaptive selection is established. I freshly read Russo and Zou, *Controlling Bias in Adaptive Data Analysis Using Information Theory*, AISTATS 2016, Proposition1 (printed page1233 / PDF page2), Proposition4 and Section2.5 (printed pages1235--1236 / PDF pages4--5):
https://proceedings.mlr.press/v51/russo16.pdf
https://proceedings.mlr.press/v51/russo16.html
Those passages relate adaptive selection to information usage and compare adaptively selected laws with independent reference laws. They are attribution and methodological context here; the source does not state the present Gibbs-prior theorem. The exact needed binary KL calculation is proved in Section5 rather than imported with mismatched premises. No exhaustive prior-work audit or historical novelty is claimed.

The fixed-witness concentration input is the separately reviewed Gaussian note above. Its primary supplier is Valettas, *On the tightness of Gaussian concentration for convex functions*, arXiv:1706.09446v1, Introduction Eq.(1.1), PDF page1:
https://arxiv.org/pdf/1706.09446
Only its classical Lipschitz upper-tail inequality is used in that supplier; the separate reverse-concentration premise of convexity is not imported.

The earlier learning boundary33 requires a trace-accurate classical estimate or a small-diameter confidence set. That assumption is NOT used here: Y may be an arbitrary much coarser classical selected prior. The new calculation controls its adequate mass using the already proved whole-good-set tail and the paid transcript information. The full-span, local-mean34 and source-energy counterexamples likewise do not by themselves prove (14).

**Stopping gate:** conditional fresh-copy calibration is valid, but no concrete pilot with an original-class uniform (4) and an improved T+2n bound has been constructed. The usual paid classical-prior version also cannot certify an improved power of M at the current common Fourier threshold through the existing sufficient formula. This leaves logarithmic improvement possible and leaves the genuinely quantum-output/direct-error alternatives open. A next constructive advance must prove a complete, original-copy-accounted uniform error bound for one such procedure; choosing a prior after seeing the source without charging its acquisition is not a solution. The full optimal-copy P1 target remains open.

This note is a local hand derivation for separate review. No public upload, numerical experiment, formal build, or full-master improvement is asserted.
