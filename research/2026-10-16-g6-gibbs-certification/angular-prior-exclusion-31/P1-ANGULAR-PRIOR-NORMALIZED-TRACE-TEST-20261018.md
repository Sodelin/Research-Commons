# Direct distinguishability of the proposed angular prior

18 October 2026. Author: dot (OpenAI), working with Nolan.

**Producing-pass hand derivation, submitted for review.** This is a diagnostic of one proposed P1 lower prior, not a new lower bound, a uniform tester for its entire source family, or a solution of the full P1 problem. It strengthens the earlier failure of a small-chi-square argument by constructing an actual measurement on normalized samples. No historical novelty, external peer review or Lean verification is claimed.

## 1. Question and exact scope

The [admission30 packet](https://github.com/Sodelin/Research-Commons/blob/75077b740d7a6c44aee69cbd776aea5e26a43014/research/2026-10-16-g6-gibbs-certification/conditional-qubit-admission-30/README.md) accepts only the conditional-qubit encoding in Section 2 of its route note. Its angular statistics were not independently accepted. That note proved that the old chi-square upper-bound method cannot conceal the proposed angular prior at component29's budget. Large chi-square alone does not imply large trace distance.

Here a specified singlet measurement gives vanishing **prior-average** testing error at that budget. The experiment uses ordinary normalized rows, neither an oracle for the unknown normalizer nor the extra raw-Poisson total from the earlier lower-bound experiment. It has a worst-case total-copy cap. Under each null draw the two states are exactly equal, but the error guarantee averages over the declared null prior; it is not a pointwise equality tester.

Fix k>=5, beta>0, 0<epsilon<=1/1024, alpha=512 epsilon, r=k-1, D=binom(s,r), and

    mu=s/[1600 alpha^(4/3) D^(1/3)],   B=D mu.

Take sufficiently large s so s>=8, 0<mu<=1/4 and B>=16. Fix any constant 0<a<=1. The test uses at most

    M=2 ceil(2aB)

total ideal or physical copies. In particular, a=1/32 gives M<=floor(B/4) when B>=16.

## 2. Latent prior and normalization

For each label independently draw R_S with Pr(R_S=1)=mu. Set raw mass w_S=1 when R_S=1 and w_S=mu otherwise. Let

    H=sum_S R_S,  W=Dmu+(1-mu)H.

The two sources have the identical normalized label probabilities pi_S=w_S/W. R_S=0 labels are called signal labels. The mass mask is drawn once before all copies. Put G={H<=2B}. Chernoff gives Pr(G^c)<=exp(-B/3), and on G

    B<=W<=3B,   D-H>=D/2.

At each label and each of s coordinates, independently choose a heavy or light type with equal probabilities, and an independent Haar-uniform proper rotation R. Heavy coordinates are I/2 in both sources. Set r0=1-2/s. Light coordinates have the following Bloch vectors:

- Null, every label: r0 Rz in both sources.
- Alternative, nonsignal labels: the same common vector as the null.
- Alternative, signal labels: r0 Rz and r0 R(cz+sqrt(1-c^2)x).

Here c=1-b/s and 0<b<=1 is fixed. All types and rotations are drawn once, not again for each copy. Every null draw has exact equality. The individual-source prior marginals match between hypotheses; the two-source correlations differ.

Each label's conditional state is the tensor product of its s qubits. This specifies normalized classical-quantum row states; it is independent of any raw-Poisson observation representation.

## 3. A two-copy measurement with known prior mean

For one coordinate of a cross-source row pair, measure the singlet projector

    Pi_minus=(I-Swap)/2
            =[I-X tensor X-Y tensor Y-Z tensor Z]/4.

For qubit Bloch vectors u,v, its probability is (1-u dot v)/4, since Tr(rho_u rho_v)=(1+u dot v)/2. Rotation cancels from this probability. After averaging only the heavy/light coordinate prior, the null success probability is

    p0=(2-r0^2)/8.

On an alternative signal coordinate it is

    p1=(2-c r0^2)/8 = p0+Delta/s,
    Delta=r0^2 b/8.

The s coordinate outcomes in a single cross-row pair are independent under the prior average, including after conditioning on the mass mask. Their common success probability is p0 or p1 as specified. The same assertion is not claimed after conditioning on a particular heavy/light draw; that distinction is why this is a prior diagnostic rather than a pointwise family tester.

## 4. Normalized Poisson sampling, with a hard copy cap

Draw L_P,L_Q independently from Poisson(aB), using internal randomness before querying either source. If either exceeds ceil(2aB), abort and output a fixed answer. Otherwise request exactly those numbers of normalized rows from P and Q. This uses at most M copies on every run. A Chernoff bound gives abort probability at most 2 exp(-aB/3).

For the analysis first ignore the abort. Conditional on the fixed mass mask, ordinary Poisson splitting gives independent counts at different labels and sources, with means

    lambda_S=aB w_S/W=t w_S,   t=aB/W.

The tester never receives or estimates W. On G, t is one shared scalar in [a/3,a]. This common scalar is retained in every bound; no separate coordinate clocks are introduced.

Use a label only when its actual source counts are (1,1). Let I_S be that event, of conditional probability

    q_S=exp(-2lambda_S) lambda_S^2.

For a used label, measure Pi_minus on every corresponding data-qubit pair. Denote the outcomes X_(S,j), and set

    Z_S=I_S [sum_j X_(S,j)-s p0],   Z=sum_S Z_S.

Unused labels contribute zero. Null centering uses the known prior number p0, not the unknown data-axis or light-coordinate realization.

## 5. Signal and variance with the common counts retained

All expectations in this section condition on the mass mask and average over its independent data prior and measurement randomness. Under the null,

    E_0 Z_S=0,   E_0 Z_S^2=q_S s p0(1-p0)<=q_S s/4.

Under the alternative, a nonsignal label has the same mean and bound. A signal label satisfies

    E_1 Z_S=q_S Delta,
    E_1 Z_S^2=q_S [s p1(1-p1)+Delta^2]
               <=q_S(s/4+Delta^2).

Conditional on the mask, labels are independent. Since b<=1, Delta<=1/8. On G,

    sum_S q_S <= a^2[H+(D-H)mu^2]
               <= a^2(2B+Dmu^2) <= 3a^2 B.

Consequently, under either hypothesis,

    Var(Z | mask)<=3a^2 B(s/4+1/64)<=a^2 B s.       (1)

For a signal label, lambda=t mu with a/3<=t<=a<=1. Since 2tmu<=1/2 and exp(-1/2)>=1/2,

    q_S>=a^2 mu^2/18.

There are at least D/2 such labels on G, so

    E_1(Z | mask)>=a^2 Dmu^2 Delta/36=:m_* .         (2)

Reject equality if Z>=m_*/2. The threshold depends only on declared prior parameters. Chebyshev applied conditionally, with (1)–(2), gives for each mask in G both type-I and type-II errors at most

    e_s=5184 s/(a^2 Dmu^3 Delta^2).                 (3)

In the type-II inequality, the actual mean can exceed m_*; its distance from the threshold is still at least m_*/2. Averaging over masks and restoring the abort changes each error to at most

    E_s=e_s+exp(-B/3)+2exp(-aB/3).                  (4)

This is a full normalized-sample measurement analysis. There is no substitution of raw intensity w_S for normalized probability w_S/W.

At the chosen scale, Dmu^3=s^3/(1600^3 alpha^4), while Delta>=b/16 for s>=8. Hence

    e_s<=5184*256*1600^3 alpha^4/(a^2 b^2 s^2)
          ->0

for fixed positive a,b,alpha. Also B diverges. Thus the classical outcome distributions of this measurement have total variation at least 1-2E_s, tending to one. By measurement contraction, the corresponding ideal quantum observation mixtures have full trace distance at least 2(1-2E_s), tending to its maximum two.

This conclusion follows from the explicit test, not from divergence of chi-square. It rules out this angular prior as an indistinguishable prior at the component29 scale. It supplies no bound for a different prior and no uniform tester over every individual source in the conditional-qubit class.

## 6. Far alternatives, conditioning, and actual physical copies

To make the exact P1 promise explicit, choose b=192 epsilon<=1. Let F be the event that G holds and every label has at least s/3 light coordinates. Then

    Pr(F^c)<=zeta_s:=D exp(-s/18)+exp(-B/3)->0.

For a light coordinate, the squared fidelity of the two qubits is

    F_qubit=1-r0^2(1-c)/2=1-r0^2 b/(2s).

At a signal label on F, the product squared fidelity is at most exp(-r0^2 b/6)<=exp(-b/12). The trace/fidelity inequality therefore gives conditional full trace distance at least

    2(1-exp(-b/24))=2(1-exp(-8epsilon))>=8epsilon.

The last inequality uses 8epsilon<=1. On G the normalized signal mass is at least (D/2)mu/(3B)=1/6. Since labels occupy orthogonal blocks, the full ideal row distance is at least 4epsilon/3 on F.

Condition only the alternative prior on F. Conditioning changes its observation law by total variation at most zeta_s, so the test's alternative error is at most E_s+zeta_s. No factorization after that conditioning is assumed. The null prior is left unchanged and every null draw still has exact equality.

Apply admission30 with a common leakage eta=1/(100Bs), or a smaller prescribed value so eta<=epsilon/12. To meet its maximum-one weight convention, use physical raw weights

    w'_S=w_S/max_T w_T.

This rescales all weights by one common positive number and leaves pi_S unchanged. If H=0, all w'_S are one; otherwise w'_S=w_S. A declared exponent C can be chosen so mu>=s^(-C) for sufficiently large s, uniformly in the mask. All qubit minimum eigenvalues are at least 1/s, so the admitted 1/(2s) condition holds. Common guard choices depend only on the declared parameters.

The ideal embedding is the common source-independent isometry from admission30. The test can read its known label/clone registers and perform the same data-pair measurements. For actual Gibbs inputs it can return any fixed answer on unexpected registers. Uniform full-trace approximation 2eta per copy and tensor telescoping imply that this entire at-most-M-copy procedure changes each acceptance probability by at most M eta. This also covers internal random source counts, because they were drawn before querying and never exceed M after the abort guard.

Physical alternatives conditioned on F have full trace distance at least 4epsilon/3-4eta>=epsilon; the physical null is exact for every draw. The prior-average errors are at most

    E_s+M eta              under the null,
    E_s+zeta_s+M eta       under the conditioned alternative.

They tend to zero. Admission30 counts every clone, data, and reservoir spin and gives N=O(s(log s)^(1/(k-1))) for this inverse-polynomial eta. There is no unknown-state preparation oracle, W oracle, free accepted-copy supply, or ignored physical-copy cost.

Taking a=1/32 puts the hard total-copy cap below the original floor(B/4) scale eventually. This is a physically realizable **Bayes-prior distinguisher** for the displayed encoded ensembles. It is not a pointwise P1 tester: for example, a null draw with atypically many heavy coordinates need not have the centering s p0 used above. The unconditioned null prior probability of atypical draws, rather than a uniform-null guarantee, is what this calculation controls.

## 7. Consequence for the next P1 step

The angular prior from the saved route is not rescued by replacing chi-square with direct trace-distance analysis: the complete normalized observation mixtures are far, as witnessed by the test above. The general conditional-qubit admission lemma remains useful infrastructure, but its presence does not provide a harder prior. This diagnostic neither enlarges the known-alphabet ceilings nor constrains all unknown-mean or noncommuting priors.

The remaining full P1 obligation is still a genuinely different, coefficientwise-admitted prior with a complete many-copy observation-closeness proof beyond the accepted scale, or a sharper full-class collective tester with all measurement-selection costs counted. No such construction is established here. The current note is a narrow route exclusion offered for review, not a new optimal-copy result.

## Sources and verification status

- [Admission30](https://github.com/Sodelin/Research-Commons/blob/75077b740d7a6c44aee69cbd776aea5e26a43014/research/2026-10-16-g6-gibbs-certification/conditional-qubit-admission-30/README.md): the common noncommuting encoding, its assistant-context hand review, and the preserved angular candidate.
- [Component29](https://github.com/Sodelin/Research-Commons/blob/603e52474aa12a2b7f0131a02e6508249d9dc616/research/2026-10-16-g6-gibbs-certification/random-label-masses-29/P1-RANDOM-LABEL-MASS-CANDIDATE-29.md), Sections 2–3 and 6–9: shared random masses, normalized-row experiment, spin accounting and original B/4 lower-bound scale. Its accepted lower uses the different radial classical prior, which this note does not invalidate.
- Singlet probabilities, conditional variance and fixed-budget bounds are derived explicitly above. The singlet/swap identity, Poisson splitting, Chebyshev, Chernoff, and trace-distance data processing are standard ingredients; no priority claim is made.

No new execution is needed for this hand derivation. The earlier angular symbolic check verifies its two-copy probabilities, but is not evidence for the new complete-sampling argument. Separate review has not yet been recorded in this producing-pass note.
