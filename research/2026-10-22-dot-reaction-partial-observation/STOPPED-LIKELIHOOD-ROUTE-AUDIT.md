# Stop-aware likelihood comparison: an exact dominated criterion and its all-rival gap

Author: dot (OpenAI). 23 October 2026 UTC.

Status: primary-source applicability audit and author hand proofs, with the precisely scoped AI-assisted hand-review PASS recorded in STOPPED-LIKELIHOOD-COORDINATING-REVIEW.md. No runtime, compilation, formal verification, or historical novelty claim.

## 1. The different route and the unchanged target

This note tests a path-space likelihood route, not another initial-jet or finite-linear-realization criterion. The target remains the exact observed-law fibre among every admitted finite mass-action diffusion rival, under the prescribed fixed full initial-state preparation, projection, full-state exit/holding convention, and finite horizon. Hidden-only reactions remain admitted; no hidden-size bound, all-start experiment, or projected-Markov assumption is introduced.

The preceding scalar, hidden-stop and nonlocal packets were reread before this attempt. They do not supply the likelihood or conditional-law providers below. The positive-moment theorem also does not, by itself, compute an observation-conditioned path likelihood or classify hidden reaction freedom.

The proposed pipeline is: construct a density of each rival's full stopped-path law relative to the target; condition that density on the observed held path; then characterize every rival for which the conditional density is one. The second step is exactly valid when the first step is valid. The first step is not a necessary prerequisite for observation equivalence, even in a fixed three-species linear reaction graph.

## 2. What the primary change-of-measure sources actually supply

Cheridito, Filipovic and Yor's operators in equations (2.1)–(2.3) share the same diffusion covariance alpha. Theorem 2.4 assumes the transformed martingale problem is well posed, absolute continuity of initial distributions, and the localized exponential-integrability condition (2.4). Its density identity initially applies on {T<S_infinity}; global identities require the additional stated survival or uniform-integrability conditions. Its killing-by-potential setting is not automatically our boundary-held observation. [Primary published reprint, Section 2, equations (2.1)–(2.8), Theorem 2.4, PDF pp. 4–7](https://arxiv.org/pdf/math/0508450).

The well-posedness quantifier concerns existence and uniqueness of the mathematical model for initial distributions; it is not an all-start measurement experiment. The failed hypothesis in the construction below is the shared covariance/dominated full-law comparison. No survival-conditioned or pre-exit-only identity is silently extended to the complete held record.

Sarkka and Sottinen's Appendix A.1 requires a unit-mean stochastic exponential. Theorem A.2 compares a target with a transformed importance process s*, whose differential is L(t)B(t)^(-1) ds; it does not leave the importance path unchanged when its dispersion differs. Theorem A.3 treats a specified deterministic/stochastic block structure. Their observation contract is discrete noisy measurements, not our exact continuous coordinate record. [Primary author preprint, arXiv0705.1598v2, Section 2.2 and Appendix A.1–A.3, PDF pp. 4–7 and 24–27](https://arxiv.org/pdf/0705.1598v2).

Consequently, allowing a transformed auxiliary process is a potentially useful repair, not evidence that arbitrary original diffusion path laws are mutually absolutely continuous. Its transformation must separately preserve the required observation, initial preparation and stopping record. Neither inspected result supplies all such transformations or every finite chemical realization. These are bounded applicability findings about the cited results, not a claim about every nonlinear filtering method.

## 3. The exact conditional-likelihood identity

Let P and Q be the full stopped/held path laws on a common canonical continuous-path space through H, and let F be the common observation map, here coordinate projection of the already held path. Write G=sigma(F). Suppose Q is absolutely continuous with respect to P, with density Z=dQ/dP.

**Lemma.** The observed laws F_*Q and F_*P agree if and only if

    E_P[Z | G] = 1    P-almost surely.                     (1)

**Proof.** For every bounded measurable observation test phi,

    E_Q[phi(F)] = E_P[Z phi(F)]
               = E_P[E_P[Z | G] phi(F)].

Thus E_P[Z | G] is the pulled-back density of the observed law. Equality of the observed measures is equivalent to its being one almost surely. Equivalently, use indicators of every G-event in the defining conditional-expectation identity. QED.

This is a classical conditional-density fact. Because P and Q already include the entire actual stop/hold record, the lemma retains nonlocal stopping information. It neither assumes the projection is Markov nor replaces the hidden-dependent exit with a visible exit. Its domination hypothesis is substantive; equation (1) is not defined as a full-path likelihood when Q is singular to P.

## 4. A common interior-domain diagnostic with genuine hidden stopping

Fix a0,b0>0 and H>0. All models below have exactly the same three labeled species, deterministic full initial state (a0,b0,b0), and reactions

    A -> 2A, rate 1;
    B -> 2B, rate u>0;
    C -> 2C, rate v>0.

Under the polynomial mass-action diffusion convention, before the full stop,

    dA = A dt + sqrt(A) dW_A,
    dB = u B dt + sqrt(u B) dW_B,
    dC = v C dt + sqrt(v C) dW_C,

with independent Brownian motions. Fix the common open domain

    I=(a0/2,3a0/2),   J=(b0/2,3b0/2),   U=I x J x J.

Its closure lies strictly inside the positive orthant. Let tau be the first exit of the full state from U; hold every coordinate afterwards. Write P_(u,v) for the full held-path law through H and O_(u,v) for its A-coordinate law. Local smoothness and uniform nondegeneracy on this compact box give the unique stopped law. The three independent one-coordinate processes give the same construction up to their first exit.

**Proposition 1.** For every u,v>0,

    O_(u,v) = O_(v,u).

If u!=v, the full labeled laws P_(u,v) and P_(v,u) are mutually singular on every horizon H>0.

**Observed-law proof.** Swap the entire B and C paths. Their initial values coincide, their interval J is the same, and this permutation carries the rate pair (u,v) to (v,u). It leaves the A path and the first full-box exit time unchanged pathwise. Therefore it leaves the held A record unchanged, giving the displayed law equality. This preserves the actual full-state stop, rather than discarding hidden exits. In particular a hidden coordinate can exit before the others with positive probability: interior nondegeneracy gives positive probability of exiting J before a fixed small time, while the other independent coordinates stay in their intervals. QED for the equality; singularity follows from the common measurable statistic constructed next.

The symmetry is classical and is not offered as a new nonidentifiability theorem. Its role is to disprove the proposed necessity of a raw full-labeled-law density, even for two rivals already in one observed-law fibre.

## 5. One measurable quadratic-variation statistic for the whole continuum

Let barB be the B coordinate of the full held path. Its bounded-on-the-box semimartingale decomposition under P_(u,v) is

    barB_t = b0 + D_t + M_t,
    D_t = integral_0^t 1_(s<tau) u B_s ds,
    [M]_t = integral_0^t 1_(s<tau) u B_s ds.             (2)

The two integrals happen to coincide here; D is finite variation while M is a continuous martingale. Since tau>0 almost surely and B is continuous at zero,

    lim_(t down to 0) [barB]_t / (b0 t) = u.            (3)

To use this simultaneously as a separation of measures, we specify one Borel path statistic rather than choose a model-dependent quadratic-variation version.

Put h_j=H*2^(-j), j>=1. For each j,n form the sum Q_(j,n) of squared barB increments along the 2^n equal subintervals of [0,h_j]. Each sum is a continuous function of the canonical path. Define q_j as its limit as n tends to infinity when that limit exists and is finite, and set q_j=0 otherwise. Define

    R(path) = lim_(j to infinity) q_j/(b0 h_j)

when the finite limit exists, and set R=0 otherwise. Countable limits make R Borel measurable, independent of u and v.

**Almost-sure convergence justification.** Fix any u,v. Let K^2=u*(3b0/2), bounding the quadratic-variation density of M. For the martingale increment sums on a grid of mesh h_j/2^n, Ito's formula and isometry give

    E[|Q_(j,n)(M)-[M]_(h_j)|^2]
        <= 2 K^4 h_j^2 2^(-n).                         (4)

Indeed the error is twice the sum of integrals of (M_s-M_left) dM_s over the grid cells; disjoint intervals are orthogonal, and E[(M_s-M_left)^2]<=K^2(s-left). Summing their integrals gives (4). Chebyshev's inequality and Borel–Cantelli imply convergence almost surely for fixed j. Intersect over the countably many j.

If L=u*(3b0/2), the bounded derivative of D gives Q_(j,n)(D)<=L^2 h_j^2 2^(-n). Cauchy–Schwarz bounds the cross increment sum by the square root of Q_(j,n)(D)Q_(j,n)(M), which tends to zero on the same event. Hence q_j=[barB]_(h_j) simultaneously for all j, P_(u,v)-almost surely. Equation (3) proves

    P_(u,v)(R=u)=1.                                    (5)

The almost-sure event need not be uniform over uncountably many parameters. The function R is the same Borel function for all of them, and (5) holds under each law separately; that is precisely what the separation argument needs.

For u!=v, the disjoint sets {R=u} and {R=v} have full measure under P_(u,v) and P_(v,u), respectively. This completes Proposition 1. These are **full-path** singularity sets involving hidden B, not observed A singularity sets. The observed laws in Proposition 1 are identical.

**Proposition 2.** No single sigma-finite measure on the full labeled path space dominates every P_(u,1), u>0.

**Proof.** The Borel sets E_u={R=u} are pairwise disjoint. If rho dominated every P_(u,1), then rho(E_u)>0 for every u>0, since P_(u,1)(E_u)=1. A sigma-finite measure has at most countably many disjoint positive-measure sets: cover the space by countably many finite-measure sets, then, in each, group the sets whose intersection has measure at least 1/k. Each such group is finite. This contradicts the uncountable parameter set. QED.

Proposition 2 concerns the whole labeled continuum, not a claim that every member of that continuum has the same observed law. Any particular pair is of course dominated by its mixture (P+Q)/2. That measure-theoretic observation does not give a common diffusion reference or a computable Girsanov density.

## 6. Exact outcome and missing supplier

The tested raw-reference pipeline fails as an all-rival necessity claim: an observationally equivalent rival can have no full-path Radon–Nikodym density relative to the target. In Proposition 1 the labeled covariance matrices already differ at the fixed start. No choice of drift-only Girsanov weight changes that quadratic-variation fact. Proposition 2 also rules out solving this particular issue by choosing one sigma-finite full-labeled-path reference for the entire admitted continuum.

This failure does **not** exclude a nonlinear alignment or filtering method. In fact the known B/C permutation immediately aligns the two full laws in Proposition 1. The example therefore cannot be used to refute likelihood comparisons after a suitable observation- and stop-preserving transformation. Nor does it prove that every observation fibre needs infinitely many invariants, or that a finite/effective general criterion is impossible.

There is even an elementary unrestricted pairwise repair at the level of already given measures. For R=(P+Q)/2, write p=dP/dR and q=dQ/dR. The same conditional-expectation proof gives F_*P=F_*Q if and only if E_R[p-q | sigma(F)]=0. This does not need P and Q to dominate each other. Constructing R and its conditional densities from the two unknown physical laws, however, has not eliminated the identification task; the identity is not an effective all-network characterization.

A route using transformed hidden coordinates or auxiliary processes still needs a completeness supplier: every admitted rival in the observed fibre must admit a justified representation/alignment that preserves the fixed preparation and complete held observation, with the applicable density and martingale conditions proved, and the resulting observation-conditioned equality must be characterized for all finite chemical sources. Neither inspected change-of-measure theorem supplies that alignment/completeness step or bounds unknown hidden source size.

Alternatively, one may work directly with the observed laws. Their Lebesgue decomposition relative to the target gives an exact criterion: zero singular part and density one. This remains valid even when the full laws are singular. Computing or characterizing that decomposition from arbitrary hidden mass-action dynamics with the actual stop is precisely an unsupplied part of the master, not a completed network-identification theorem. A law-valued nonlinear filter remains potentially useful; no general exclusion is claimed.

Thus the substantive output is the exact dominated lemma, the concrete source-faithful diagnostic against raw full-path domination, and a pinned missing supplier. No further restricted-family result is substituted for the original all-finite-rival target. No historical novelty, formal proof, new preparation experiment, runtime, or private upload is asserted.
