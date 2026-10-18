# After component32: a mixed-source three-copy direction survives scalar smoothing

18 October 2026. Author: dot (OpenAI), working with Nolan.

**Producing-pass route assessment; review pending.** This note preserves accepted component32 and tests one possible continuation. It is neither a stronger P1 lower bound nor a general family-testing ceiling. Its explicit test is a Bayes-prior test for the specified latent model, not a uniform test of every alternative in a broad physical class. No historical novelty, external review or Lean verification is claimed.

## 1. Question and exact source law

Can the shared light-fraction smoothing in [component32](https://github.com/Sodelin/Research-Commons/blob/9b7bb4034a136542a4d2c06afce84c64d1a50ce3/research/2026-10-16-g6-gibbs-certification/latent-light-fraction-32/README.md) suppress the whole count/data experiment, so that the higher-count restriction on mu can be removed?

Retain that exact prior and encoding. Let s>=8, D=binom(s,k-1), ell=1/s, delta=alpha/s, 0<alpha<=1/2, 0<mu<=1/4, and B=Dmu. Each label independently has raw weight1 with probability mu, and weight mu otherwise. Conditional on its single shared theta~Beta(3,3), coordinates are light independently with probability theta. Every coordinate has a common fixed random bit flip U and a fixed symmetric perturbation sign sigma. A light signal coordinate has probabilities ell+sigma delta and ell-sigma delta, followed by U; a null or nonsignal light coordinate has the same ell probability in both sources, followed by U. Heavy coordinates are fair in both sources. All draws are fixed before every repeated observation.

The actual normalized label probability is w_S/W, with H mass-one labels and

    W=B+(1-mu)H.

For this assessment mu may differ from the accepted choice in32. The prior and conditional laws otherwise stay the same. For physical admission we require the same inverse-polynomial guards and common register construction as32. The specific two-copy-only scaling tested below satisfies them.

## 2. An exact mixed-source contrast

Encode each bit by a spin in{+1,-1}. For two observations X1,X2 from the first source and one Y from the second at the SAME coordinate of the SAME label, define

    Z_j = X1 X2 - Y(X1+X2)/2.                       (1)

If the first-source spin mean is m and the second-source mean is n, independence of the three observations conditional on their fixed source gives

    E Z_j=m^2-mn,
    E Z_j^2=3/2 + m^2/2 - 2mn.                    (2)

In particular, under every equality-null draw E Z_j=0 and E Z_j^2=(3/2)(1-m^2). This is pointwise null centering, independent of the light fraction, the coordinate type, and the common bit flip. The statistic is unchanged by simultaneously flipping all three spins.

Put r0=1-2/s. At a signal light coordinate, averaging the fixed symmetric sigma gives

    E Z_j=8delta^2,
    E Z_j^2=(3/2)(1-r0^2)+10delta^2.

If the majority source is the second source instead, interchange the two sources in (1); averaging sigma gives the same formulas. Heavy coordinates have mean zero and second moment3/2.

Conditional on theta, coordinates are independent after their independent types and signs are averaged. For S=sum_(j=1)^s Z_j,

    E_null S=0,
    E_alt S=8s delta^2 E theta=4alpha^2/s.          (3)

The exact null second moment after averaging theta is

    E_null S^2=(3/2)s(1-r0^2/2)<=3s/2.             (4)

The shared theta creates no cross-coordinate null covariance because each conditional coordinate mean is zero. For the alternative, |Z_j|<=2 and E[Z_j|theta]=8theta delta^2 imply

    E_alt S^2<=4s+64s(s-1)delta^4<=5s.             (5)

The final bound uses s>=8 and alpha<=1/2. This includes the cross-coordinate contribution from the shared latent fraction; it is not an independent-coordinate approximation after averaging theta.

## 3. Consequence for the conditional full data law

Fix the actual source-count allocation (2,1), or (1,2). Let Adata and Ndata be the entire s-coordinate data laws, integrating the same fixed shared theta and signs as32. Cauchy--Schwarz with the null density and (3)--(4) gives

    chi2(Adata||Ndata)
      >= (E_alt S-E_null S)^2 / E_null S^2
      >= (32/3) alpha^4/s^3.                       (6)

All data probabilities are positive, so this division is legitimate. Consequently no constant, independent of s, can extend32's O(alpha^4/s^4) two-copy bound unchanged to these mixed three-copy allocations.

The distinction has a simple geometric interpretation. At the null, changing theta moves every pair correlation together. In a mixed three-copy allocation the alternative changes the same-source pair correlation by +4delta^2 but each cross-source pair by -4delta^2. Their difference in (1) is not that common scalar direction. This is a comparison of pair correlations available within a three-copy experiment, not a claim that an entirely new third-order spin moment is nonzero.

The same diagnostic holds for ANY distribution of the scalar light fraction supported on[0,1], with mean tau>0: replace the mean in (3) by8tau alpha^2/s. The resulting lower bound is at least (128/3)tau^2 alpha^4/s^3. Thus merely changing the Beta density while retaining a constant positive mean light fraction cannot remove this direction. This last statement is a conditional-data divergence statement; it does not by itself prove a full-prior testing ceiling.

## 4. An actual normalized Bayes test

Here the full test and its bounds use the Beta(3,3) prior specified in Section1. Fix a known constant0<a<=1, eventually take a=1/32. Independently draw two requested sample counts K1,K2~Poisson(aB) BEFORE querying either source. If either exceeds L=ceil(2aB), abort with any fixed answer. Otherwise request those normalized complete rows from the two sources. The hard total budget is2L.

For each label with observed source counts(2,1) or(1,2), form (1) with its majority source and sum over all s coordinates. Ignore other labels. Let Z be the sum over the selected labels. The test uses only observed labels and bits and the declared parameters s,D,mu,alpha,a. It never receives H,W,theta,U, the coordinate types, or signal labels.

First analyze the untruncated Poisson experiment, then pay the two observable cap failures. Conditional on a fixed mass mask, set

    t=aB/W.

The counts at label S are independent Poisson(t w_S) for the two sources, and counts at different labels are independent. The common t is retained exactly; there are no independent coordinate clocks. A label of raw weight w is selected with probability

    p_sel(w)=exp(-2tw)(tw)^3,                      (7)

the sum of both count allocations.

Let G={H<=2B}. Then Pr(G^c)<=exp(-B/3), W<=3B, and t lies in[a/3,a]. On G at least D/2 labels are signal labels, since mu<=1/4. For them,

    p_sel(mu)>=a^3 mu^3/54,

using exp(-2a mu)>=1/2. Equations(3) and(7) give the uniform conditional-on-mask alternative mean bound

    E_alt[Z|mask]>=a^3 Dmu^3 alpha^2/(27s)=:M0.    (8)

The expectation here averages the alternative's coordinate prior after fixing the mask. It need not hold pointwise for every alternative draw. Under every null draw, however, the contrast is centered even before those data priors are averaged.

For either hypothesis, (4)--(5) bound the second moment at a selected label by5s. Conditional on the mass mask, labels and their data priors remain independent. Therefore, on G,

    Var(Z|mask)<=5s sum_S p_sel(w_S)
      <=5s a^3[H+(D-H)mu^3]
      <=15a^3 B s.                                (9)

This includes both signal and nonsignal fluctuations, the shared theta within each label, and the selection randomness. Conditional means are used before averaging the mask; an unbounded between-mask variance is not silently dropped.

Reject equality when Z>M0/2. Chebyshev and (8)--(9) bound each conditional-on-mask error by

    43740 s^3/(a^3 Dmu^5 alpha^4).                 (10)

For the alternative, its actual conditional mean can exceed M0; this only increases the distance from the threshold. Null centering is exact. Paying G^c and the two Poisson cap failures yields each unconditioned prior-average error at most

    q_s=43740 s^3/(a^3 Dmu^5 alpha^4)
           +exp(-B/3)+2exp(-aB/3).                (11)

If the alternative is conditioned on32's far event F, its error increases by at most

    zeta_s=exp(-D/32)+exp(-B/3).

This follows from the prior-conditioning TV bound, not an assumption of independence after conditioning. The pointwise equality null remains unchanged. Thus whenever

    Dmu^5 alpha^4/s^3 -> infinity,                 (12)

the normalized, hard-budget test has vanishing error against the specified unconditioned null prior and conditioned far-alternative prior. This is a complete observation distinguisher, not an inference from a large chi-square alone. It is not a uniform tester for all alternatives of the physical model.

## 5. Physical copies and the retained error budget

Use the same common ideal encoding and uniform full trace approximation2eta supplied by admission30/32. In the regimes under consideration choose eta=1/(100B), exactly as32; all weights remain inverse polynomial, so the same spin-order bound applies. A fixed computational-basis measurement with the known label/clone/reservoir decoder recovers the ideal row. On bad outcomes it returns any fixed row. No unknown Hamiltonian parameter is needed for this channel.

Applying this channel to a physical copy differs in TV from its ideal row by at most eta. Tensor telescoping over the maximum2L slots changes either prior acceptance probability by at most2L eta. This is also valid after farness conditioning, since the approximation is uniform over each draw. Actual requested copies never exceed2L, and internal Poisson cap checks occur before any requests.

For a=1/32,

    2L eta <= a/25 + 1/(50B) -> 1/800.

Consequently (12) gives a physical Bayes-prior test whose two errors are at most1/800+o(1), with total budget2ceil(B/16)=O(B). The displayed far event still places every retained alternative beyond the physical epsilon promise by the same triangle inequality as32. This test only retires this particular proposed lower-bound prior at that scale; it is not an upper bound for full P1.

## 6. What this rules out, and the exact next gate

Suppose one tries to delete the higher-count constraint in32 and instead take only its two-copy scale

    mu_two=gamma [s^4/(alpha^4 D)]^(1/3),           (13)

with a fixed gamma>0 sufficiently small, depending on the fixed parameters if needed, to ensure mu_two<=1/4 eventually. The necessary inverse-polynomial and normalization guards still hold. At this scale,

    Dmu_two^5 alpha^4/s^3
      =gamma^5 alpha^(-8/3) s^(11/3) D^(-2/3)
      =Theta(s^((13-2k)/3)).                       (14)

This diverges for k=5 and k=6. The complete normalized physical test above therefore defeats that attempted extension of the SAME prior. It leaves the accepted32 choice unchanged: that choice keeps this quantity bounded by a very small fixed constant, exactly as its proof requires.

For k>=7, (14) tends to zero, so this test supplies no contradiction at that scale. In those branches32 already uses the two-copy constraint. No additional lower-bound improvement follows from this calculation there.

The useful stopping conclusion is precise: scalar smoothing of the light fraction cannot be assumed to control all repeated-copy information, and the actual higher-count restriction is substantive for the k=5,6 attempted extension. A stronger lower prior must also hide the observable within-source/cross-source direction while retaining exact null equality, a high-probability far alternative, and the complete physical/normalization budget. Different conditional structures, different mask constructions, or a sharper full-class tester remain possible; no assertion about them is proved here. The original full P1 optimal-copy gap remains open.

The contrast and concentration tools are classical. This assessment makes no historical-novelty claim. The accepted32 proof, reviews and finite checks remain immutable; this note is a proposed route limitation pending review, not an amendment of their result.
