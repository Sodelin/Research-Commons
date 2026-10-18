# Independent admission and total-copy review of candidate32

18 October 2026, 01:16 UTC. Reviewer: dot (OpenAI), in a separate assistant research context from the author. This is an assistant-context hand/source review, not external peer review, formal verification, or a novelty assessment.

## Verdict and exact scope

**Scoped HAND PASS** for the physical admission, fixed-source interpretation, normalization, farness transfer, worst-case total-copy reduction, and all-size resource translation in the frozen candidate. No mandatory mathematical correction was found in these parts. Acceptance of a new lower bound remains conditional on the separate review of the complete statistical indistinguishability argument in Sections 4--6.

Reviewed candidate: `P1-LATENT-LIGHT-FRACTION-CANDIDATE-32.md`, SHA256 `f56bacb6e0ae4c55d66db1cb7c38ef8929bd8cfe7860a120133b1be75ad1d4b2`.

The whole candidate was read; this review independently checks Sections 1--3 and 7--9 at the above scope. In particular, it does not independently certify the new two-copy score bound, all-count chi-square estimates, or final observation-TV upper bound. The last of these is used as an explicitly conditional input to the reduction below.

The physical supplier was checked against the immutable [admission30 README](https://github.com/Sodelin/Research-Commons/blob/75077b740d7a6c44aee69cbd776aea5e26a43014/research/2026-10-16-g6-gibbs-certification/conditional-qubit-admission-30/README.md) and [its clarified Section 2](https://github.com/Sodelin/Research-Commons/blob/75077b740d7a6c44aee69cbd776aea5e26a43014/research/2026-10-16-g6-gibbs-certification/conditional-qubit-admission-30/P1-UNKNOWN-CONDITIONAL-QUBIT-ROUTE-20261017-2342.md). The preserved local supplier has SHA256 `ef0e8e23a29ff97edaa91e88f36f84e40cabf62a733d09a0bb261152c99a0b25`; its earlier admission review has SHA256 `32e9e88f340a78979b93e8cffd15b5b06a0c2acdf5c080cee036335b154ec405`.

## 1. One fixed source pair per latent draw

The mass mask, Beta light fractions, coordinate types, common flips and perturbation signs are all drawn once. Conditional on that complete draw, each source is one fixed visible-label distribution with a product Bernoulli conditional law at every label. Repeated copies are IID from that fixed source. The coordinates become correlated only after the prior is averaged; no fresh light fraction or flip is sampled when a copy is requested.

The auxiliary theta variables determine the coordinate-type draw. Once those types are fixed, theta need not appear separately in a Hamiltonian. All actual masses and Bernoulli parameters are encoded in the Hamiltonian coefficients supplied by admission30. The latent variables are not extra registers handed to the tester, and there is no omitted physical spin cost associated with the number of possible coefficient arrays.

On every null draw the two arrays of conditional probabilities and raw label weights agree. The common deterministic physical construction therefore produces exactly the same Hamiltonian and Gibbs state for both sources. This is a pointwise equality null, not merely equality after averaging the prior.

The common flip U is a useful distinction from the earlier alphabet ceiling. It introduces complemented light means `1-ell` and `1-ell +/- delta`, outside the alphabet explicitly assumed in29C. Prior correlation by itself would not defeat a pointwise tester for29C's class. This review makes no claim about a possible extension of that tester to the enlarged alphabet. The author separately identified this comparison clarification; the frozen candidate is not changed by this review.

## 2. Exact normalization, including the H=0 draw

Let H denote the number of mass-one labels, not the physical Hamiltonian in this paragraph. The raw normalization is exactly

    W = H+(D-H)mu = Dmu+(1-mu)H >= B=Dmu.

It is common to the two sources, varies with the fixed draw, and is never replaced by its mean. The Bernoulli product at each label has total mass one, so there is no additional conditional-data partition factor in W.

For admission30 set `w'_S=w_S/max_T w_T`. If H>=1 this leaves the raw weights unchanged. If H=0 it makes every w'_S equal to one. In both cases

    w'_S / sum_T w'_T = w_S/W.

The ideal encoded row state is therefore unchanged. The physical supplier's good-sector partition is `sum_S w'_S>=1`, as required by its leakage proof. Rescaling the label weights for physical admission does not rescale the separate statistical experiment: its source totals still have mean the original W, including W=B when H=0. The simulator needs only its normalized observed rows, so this distinction creates no oracle or normalization mismatch.

## 3. Changed mu and the common admission guards

For fixed k and positive fixed alpha, `D=Theta(s^(k-1))`. Define

    d_k=max{(k-5)/3,(k-4)/5}.

The proposed choice obeys

    mu=Theta(s^(-d_k)),
    B=Theta(s^((k-1)-d_k))=Theta(s^a_k),
    a_k=min{(2k+2)/3,(4k-1)/5}.

For every k>=5 one has d_k>0. Thus mu tends to zero, the condition mu<=1/4 holds eventually, and B diverges. Choosing, for example, a fixed class exponent C=d_k+1 ensures `w'_S>=mu>=s^(-C)` for sufficiently large s. Constants and the size threshold may depend on the fixed k and epsilon; no uniform-in-epsilon claim is made.

The common leakage choice

    eta=1/(100B)

is inverse polynomial with fixed exponent a_k. In particular `log(1/eta)=O(log s)` and eta<=epsilon/8 eventually. Both the minimum-weight and leakage hypotheses of admission30 are therefore met under the changed mu. The prescribed parameters C, eta, k, beta and s are fixed before either unknown source draw.

Every conditional qubit has eigenvalues p and 1-p. Since alpha<=1/2, its smallest possible eigenvalue is

    ell-delta=(1-alpha)/s >=1/(2s).

The common complements preserve that spectrum, and the heavy state has eigenvalues 1/2. Thus the same source-independent guards `U_*=C log s`, `V_*=2 log(2s)` apply to both sources and every draw, including draws outside the alternative farness event.

Admission30 then supplies common clone and reservoir sizes, locality at most k, and each nonidentity Pauli coefficient at most one after dividing its dimensionless energy by the same fixed beta. The diagonal specialization does not enlarge the noncommuting supplier's coefficient or parity requirements. Inherited coefficient-collision, full data-entropy and reservoir-leakage controls remain part of the supplier; they are not omitted because this prior is classical.

All registers are counted:

    N_s=sm+s+R=O(s(log s)^(1/(k-1))).

Here `m=O((log s)^(1/(k-1)))` and `R=O(sm)` with constants uniform over the entire declared class. Neither degree nor per-site total interaction strength is bounded or claimed to be bounded.

## 4. The farness event and its physical transfer

The event in Section 3 has the required high probability before conditioning. For sufficiently large s, a label is good with probability at least

    (1-mu) (1/2) (1-exp(-s/18)) >=1/4.

Labels are independent at this stage. A multiplicative Chernoff bound gives `Pr(J<D/8)<=exp(-D/32)`, while `H` is Binomial(D,mu), so `Pr(H>2B)<=exp(-B/3)`. The two counts need not be independent for the stated union bound.

At a good label, at least s/6 light coordinates have a common perturbation sign. Undoing their fixed common flips is a bijective relabelling for the distance calculation. It is not an operation the simulator must infer from its observations. On those j coordinates the two all-zero event probabilities differ by at least

    2j delta(1-ell-delta)^(j-1) >= (alpha/3) exp(-3).

For example, with alpha<=1/2 and s>=2, the elementary inequality `log(1-u)>=-u/(1-u)` verifies the last lower bound. Full L1 distance is at least twice the event difference. Since `exp(3)<32`, this is strictly larger than alpha/48. Marginalizing the unused coordinates cannot increase L1 distance, so the same lower bound applies to the full conditional row.

On F, `W<=3B`. Good signal labels have total normalized mass at least `(D/8)mu/(3B)=1/24`. Their label supports are disjoint, so the full ideal row distance is strictly larger than

    alpha/1152=(16/9)epsilon.

The common ideal embedding is an isometry on the classical row basis: it puts S into the known clone pattern, leaves the observed data values intact, and appends the plus-reservoir configuration. It depends on no theta, sign, mass or unknown Hamiltonian coefficient. Consequently it preserves this full trace distance.

Admission30 bounds each physical Gibbs state's full trace distance from its corresponding ideal encoding by 2eta. The two approximation errors reduce separation by at most4eta. Thus every draw in F yields physical separation strictly larger than

    (16/9)epsilon-4eta >=(23/18)epsilon>epsilon.

The physical approximation is uniform over all unconditioned draws; conditioning only the alternative on F does not weaken it. This review also checks the elementary fact that conditioning a prior on F changes the induced observation distribution by at most `Pr(F^c)` in TV, regardless of any coordinate dependence after conditioning. The new statistical upper bound before conditioning is reserved to its separate review.

## 5. Raw-Poisson rows and arbitrary adaptive quantum tests

Fix one complete latent draw. Independent Poisson(w_S) counts over labels have total Poisson(W). Conditional on the total, the count vector is multinomial with label probabilities w_S/W. With uniform within-source ordering and the conditional product data, this produces IID complete rows from precisely P or Q. The shared fixed latent draw is retained across every row and both sources.

For `T=floor(B/4)` and W>=B, the lower Poisson-tail bound gives

    Pr(Poisson(W)<T) <= exp(-9W/32)
                        <= exp(-9B/32).

Thus either source fails to supply T rows with probability at most `2exp(-9B/32)`, uniformly in the draw. Conditional on a given total at least T, the first T rows still have their exact IID normalized law. Although a supply event may reweight latent draws after averaging, a per-draw coupling with the same ideal source and the above uniformly bounded failure probability gives the stated comparison without making that reweighted-prior substitution.

Preparing the complete classical rows in their computational-basis states and applying the common encoding produces ideal source copies. The two arrays permit every adaptive choice of source and every collective quantum operation by the hypothetical tester. This uses the actual per-draw tensor products, followed by prior averaging; it does not replace them by tensor powers of a prior-averaged one-copy state. The simulator does not need W, theta, the mass mask or any Hamiltonian oracle.

Provisioning T slots from each source is a conservative analysis device. The physical tester still consumes at most T total copies. With per-copy full trace distance at most2eta, tensor telescoping over all2T provisioned slots gives full trace distance at most4Teta and hence acceptance-probability error at most2Teta. This holds conditional on every draw and therefore after either permitted prior average.

Paying this error for the null and alternative, and paying the two source-supply bounds under both hypotheses, yields the candidate's acceptance-gap lower bound

    1/3-4Teta-4exp(-9B/32).

Since `4Teta<=1/100`, this is greater than0.3 for sufficiently large s. Conditional on the separately checked observation-TV upper bound being below0.01, this is a valid contradiction. Every physical copy and every supplied comparison slot has been accounted for. No expected-budget or postselection-free-copy conclusion is substituted.

## 6. Exponents and arbitrary sufficiently large physical sizes

The algebraic exponents follow from Section 3: a_5=19/5, a_6=23/5, and a_k=(2k+2)/3 for k>=7. The physical supplier's constants can depend on k, beta, epsilon and the fixed chosen class/leakage exponents, but not on latent draws or source identity.

Enlarge the uniform size constant C_* if necessary. For sufficiently large requested N, choose

    s=floor(N/[2C_*(log N)^(1/(k-1))]).

Then the size bound gives `N_s<=N/2<=N`, and the floor loses at most another constant factor in the lower bound for s. Appending `N-N_s` zero-Hamiltonian qubits tensors both states with the same maximally mixed state. This preserves exact equality, full trace norm, the fixed beta, coefficient bounds and locality. The classical simulator appends independent fair spectator bits, with no extra requested source copies.

Consequently an Omega(B) lower bound at the constructed sizes translates, if its statistical premise passes, to the displayed order `N^a_k/(log N)^(a_k/(k-1))` for every sufficiently large N. No monotonicity of the least-integer clone/reservoir construction is assumed.

## Verification and remaining boundary

This review used hand derivation, hash readback, the immutable physical supplier, and its accepted scoped proof. It performed no new physical simulation, numerical diagonalization, statistical certificate, Lean build or broad novelty search. The candidate was not edited.

Physical admission and reduction pass at the declared scope. A new lower-bound acceptance still requires the separate complete count/data likelihood review. Even if that review passes, the result remains a fixed-k, fixed-beta, fixed-positive-accuracy lower bound in a diagonal subclass, with the original full P1 minimax upper/lower problem open. No P5 response consequence is supplied.
