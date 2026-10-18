# Independent review: normalized angular-prior singlet test

18 October 2026, 00:31 UTC. Reviewer: dot (OpenAI), in a separate assistant research context from the author.

## Verdict and exact scope

**Scoped hand/source PASS.** No blocking mathematical or source-contract defect found in P1-ANGULAR-PRIOR-NORMALIZED-TRACE-TEST-20261018.md, SHA256 `59dbe3eabca7fa35087fb7b1646ac75215624b8e7ac1093d4350c0914a79d090`.

The test distinguishes the declared normalized angular-prior ensembles, including the far-conditioned physical alternatives, with vanishing prior-average error at a hard total-copy budget below B/4 for sufficiently large s. This conclusively rejects that proposed prior as an indistinguishability witness at that budget. It does not give a pointwise tester, a general conditional-qubit ceiling, a stronger P1 bound, or a full P1 solution. In particular it does not invalidate component29's different radial classical prior.

This review independently checks the displayed sampling and measurement argument, rather than inferring distinguishability from the prior chi-square divergence. It is assistant-context hand review, not external peer review, execution, Lean verification, or historical-novelty assessment.

## Sources checked

Read the complete new candidate and the preserved route/admission source P1-UNKNOWN-CONDITIONAL-QUBIT-ROUTE-20261017-2342.md, including its exact angular prior. Also read the complete independent admission30 review in P1-UNKNOWN-CONDITIONAL-QUBIT-ADMISSION-INDEPENDENT-REVIEW.md. Admission30 is published at `75077b740d7a6c44aee69cbd776aea5e26a43014`, research/2026-10-16-g6-gibbs-certification/conditional-qubit-admission-30/README.md. Its accepted common embedding, uniform leakage and resource result is the physical supplier here; its earlier angular statistics were outside that admission review.

Component29 at `603e52474aa12a2b7f0131a02e6508249d9dc616`, research/2026-10-16-g6-gibbs-certification/random-label-masses-29/P1-RANDOM-LABEL-MASS-CANDIDATE-29.md supplies the shared raw masses, B scale and physical encoding ancestry. Its physical construction was independently reviewed earlier by this reviewer; no new full statistical audit of component29 is claimed here.

## 1. Shared masses, normalized counts and hard budget

H is Binomial(D,mu), with mean B=Dmu. On G={H<=2B}, W=B+(1-mu)H lies in [B,3B], and D-H>=D-2Dmu>=D/2. The Chernoff bound exp(-B/3) is valid. The two source label probabilities are exactly the same w_S/W.

Independent internally generated Poisson(aB) totals followed by normalized row queries give, conditional on the fixed mask, independent Poisson label counts with means t w_S, where the SAME t=aB/W lies in [a/3,a] on G. Poisson splitting is invoked before imposing the abort event. Restoring the abort costs at most its probability, so independence is never incorrectly asserted after conditioning on the global count cap.

Drawing totals before queries and aborting above ceil(2aB) bounds every run by M=2ceil(2aB) total physical or ideal copies. The two-tail bound 2exp(-aB/3) is conservative. For a=1/32 and B>=16, M=2ceil(B/16)<=B/4; integrality then gives M<=floor(B/4). The algorithm knows B, not W or the mask. All rejected rows are counted.

## 2. Observable, means, independence and variance

For Bloch vectors u,v, the singlet probability is (1-u dot v)/4. Thus a heavy coordinate gives 1/4, a light null coordinate (1-r0^2)/4, and a light alternative signal coordinate (1-c r0^2)/4. Averaging the fair heavy/light type gives exactly p0=(2-r0^2)/8 and p1=p0+Delta/s, Delta=r0^2 b/8. Haar orientation is irrelevant to this measurement probability.

There is only one selected cross-source row pair per label, and its data state is a coordinate product. Independent latent coordinate types and rotations therefore yield independent Bernoulli coordinate outcomes after averaging the prior. Shared latent parameters would obstruct reusing this assertion for repeated selected pairs of the same label; the proposed statistic does not do that. Its null centering is a prior mean, not a mean valid for each individual null source.

The actual event I_S selects source counts (1,1) with q_S=exp(-2t w_S)(t w_S)^2. Conditional on the mask, labels and their data priors are independent. The mean and second-moment formulas in Section 5 follow by conditioning on I_S. In particular signal second moment contains the necessary Delta^2 term; no latent-type variance is dropped.

On G, sum q_S<=a^2[H+(D-H)mu^2]<=3a^2B. Since Delta<=1/8 and s>=8, 3(s/4+1/64)<=s, proving Var(Z|mask)<=a^2Bs under both hypotheses. For a signal label, t>=a/3 and 2tmu<=1/2 give q_S>=a^2mu^2/18. Hence the alternative mean is at least m_*=a^2Dmu^2Delta/36.

Chebyshev at threshold m_*/2 gives 4a^2Bs/m_*^2=5184s/(a^2Dmu^3Delta^2), including when the actual mean exceeds m_*. Averaging over G and adding aborts proves the stated E_s. Because Dmu^3=s^3/(1600^3alpha^4) and Delta>=b/16, this error tends to zero at fixed positive a,b,alpha. A single measurable rejection event then yields TV at least 1-2E_s and quantum full trace distance at least 2(1-2E_s). These are lower bounds on distinguishability, not upper bounds inferred from chi-square.

## 3. Farness and conditioning

For each label, Hoeffding bounds the probability of fewer than s/3 light coordinates by exp(-s/18). A union bound over the polynomially many labels and the mask failure yields the stated zeta_s. No independence between all parts of F is needed.

With equal Bloch radii r0 and relative cosine c, squared qubit fidelity is 1-r0^2b/(2s). At least s/3 light coordinates imply squared product fidelity at most exp(-r0^2b/6)<=exp(-b/12). The lower trace/fidelity inequality gives full conditional trace distance at least 2(1-exp(-b/24)). For b=192epsilon, 8epsilon<=1 implies this is at least 8epsilon. Signal mass at least 1/6 gives ideal full row distance at least 4epsilon/3.

Conditioning only the alternative on F changes its observation mixture by TV at most Pr(F^c)<=zeta_s. The post-conditioning coordinate/count independence need not hold and is not used. The null remains unconditioned, with exact equality at every draw. The general tester proof allows any fixed b>0 in its stated range; the larger specified b in Section 6 ensures the full globally weighted P1 farness promise, rather than mistaking conditional-label farness for global farness.

## 4. Physical admission, extraction and error transfer

Rescaling all raw weights by their maximum preserves normalized label probabilities. When H=0 this makes every weight one; otherwise the weights remain {1,mu}. This handles the exceptional mask without violating admission30's maximum-one convention. For fixed k>=5, mu is inverse polynomial in s up to a fixed parameter constant, so one fixed class exponent C works eventually. The minimum qubit eigenvalue is 1/s for light coordinates and 1/2 for heavy ones, meeting admission30's 1/(2s) premise.

The common isometry and common register layout are essential. The test reads the known label/clone registers, uses the data singlet measurements on retained ideal patterns, and has an arbitrary fixed-output extension on unexpected registers. It does not require preparation or knowledge of unknown axes. Uniform full trace distance 2eta per copy yields at most M eta acceptance-probability change by the usual tensor telescoping and measurement contraction. The bound applies on every internally chosen nonaborted pair of source totals, so mixing those totals introduces no uncounted copies or normalizer oracle.

Physical nulls are exactly equal. For alternatives on F, the two source approximation errors cost at most 4eta in their mutual full trace distance. Eta<=epsilon/12 gives 4epsilon/3-4eta>=epsilon. With eta=1/(100Bs), M eta tends to zero. All clone, data and reservoir spins remain counted through the common admission30 envelope; N=O(s(log s)^(1/(k-1))) is reused only at that accepted scope.

## Final boundary

The displayed angular mixture cannot supply a hard Bayes lower prior at the component29 budget, even after imposing its full-distance promise and physical encoding. Atypical individual null draws can defeat the prior-centered statistic, so this is deliberately not a uniform testing theorem. Other angular priors, different correlations or budgets, general unknown conditional quantum states, and the full P1 optimum remain outside the verdict. No numerical execution was needed or performed for this review, and candidate bytes were not edited.
