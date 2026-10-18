# Independent review of the shared latent light-fraction candidate32

18 October 2026, 01:15 UTC. Reviewer: dot (OpenAI), in a separate assistant context from the author.

## Verdict and pinned scope

**Scoped hand-proof/source PASS.** Reviewed the complete P1-LATENT-LIGHT-FRACTION-CANDIDATE-32.md, SHA256 `f56bacb6e0ae4c55d66db1cb7c38ef8929bd8cfe7860a120133b1be75ad1d4b2`. No mandatory mathematical correction found.

The proof supports its stated fixed-k>=5, fixed-beta>0 and fixed 0<epsilon<=1/4096 lower bound with exponent min{(2k+2)/3,(4k-1)/5}, assuming the already accepted admission30 supplier at precisely its common-encoding scope. Every physical spin and worst-case total copy is counted. Arbitrary collective operations and adaptive source choice remain allowed. There is no bounded-degree/per-site-strength premise.

Acceptance includes the full raw count/data law, not only its two-copy sector. It includes farness conditioning and the reduction from normalized physical copies. This is assistant-context hand review with bounded independently authored symbolic controls, not external peer review, Lean verification, a historical-novelty determination or full P1 closure. No candidate bytes were edited.

## Sources and controls

Read the complete candidate, the preserved admission30 route and its independent admission review. Component29's shared-mass and physical source construction were checked in the earlier physical review by this context; their reuse here is explicitly identified. The applicable immutable sources are component29 at `603e52474aa12a2b7f0131a02e6508249d9dc616` and admission30 at `75077b740d7a6c44aee69cbd776aea5e26a43014`, under research/2026-10-16-g6-gibbs-certification/. Admission30 accepts the uniform source-independent encoding, not a statistical lower prior by itself.

Independently authored and executed using installed Python/SymPy:

- independent_latent_fraction_check_32.py, SHA256 `10834c05b111df2cfad62d3823761996570047e38c4dfc82bc6ce24fcedc262b`.
- independent_latent_fraction_check_32.log, SHA256 `9581282eff0a58565a14fead5f032e4fc7d625e8c900974209bb606b3c49f7f4`.

Exit status zero. The checks verify Beta normalization, endpoint and score identities, every outcome in all three two-copy source allocations, and the Poisson factorial identity/constants. They do not execute the all-size physical construction or establish the theorem by finite testing. The parameterized arguments below were checked by hand.

## 1. Prior, exact null and the genuinely shared latent variables

The light fraction theta is drawn once per label. Conditional on it, coordinate flags and their two signs are independent across coordinates, and all of these quantities remain fixed across every repeated row from either source. The conditional row law for each actual draw is therefore a product distribution, although its prior mixture is not a coordinate product. This meets admission30. Nothing requires a physical register containing theta.

The raw mass mask is independent of those data variables. Both sources use precisely w_S/W with the same W=B+(1-mu)H. Under every null draw the conditional probabilities and weights coincide, so equality is pointwise, not just equality of prior means. A shared coordinate bit flip is also applied to every repetition, not resampled per copy.

For fixed k>=5, D grows as s^(k-1). The chosen mu tends to zero (including k=5, where its second branch decays), and B diverges. Thus the eventual guards mu<=1/4 and inverse-polynomial weights hold at fixed parameters.

## 2. Conditional all-count bounds (5)--(8)

Fix the actual source counts a,b and n=a+b. Relative to uniform Bernoulli rows, symmetric averaging of sigma cancels the first-order term in delta, including mixed source signs. For a degree-j centered-product coefficient, the absolute second-order remainder is bounded by delta^2 j(j-1)(|ell-1/2|+delta)^(j-2)/2. Walsh orthogonality with v=1/4 gives the stated squared norm. Since |ell-1/2|+delta<=1/2, the resulting x is at most one. The bound by 4delta^4 n^2(n-1)^2 2^n follows. Averaging the common flip cannot increase that uniform-reference squared norm.

Using N_theta>=(1-theta)Unif then gives (5). Its divergence at theta=1 is not used as a uniform statement. Revealing the coordinate type and orientation as additional information and averaging sigma gives (6): the light product comparison has chi-square (1+y)^n-1, where y=alpha^2/(s-1).

For fixed theta, coordinate independence is valid. The elementary bound (1+d)^s-1<=s d(1+d)^(s-1), together with 1+d<=(1+y)^n, yields

    (1+d)^(s-1) <= exp[n(s-1)y] = exp(n alpha^2).

Combining this with (5), s delta^4=alpha^4/s^3, and 2exp(alpha^2)<3 proves (7). Revealing the SINGLE shared theta gives a valid data-processing upper bound for the actual integrated row law; it does not replace that law by a product of integrated coordinates. Its remaining integral is exactly

    E[theta^2/(1-theta)] = 30 integral theta^4(1-theta) dtheta = 1.

This proves (8) for every count pair. Counts zero and one have identical laws. The higher-count proof pays the full n-dependent bound rather than suppressing that tail heuristically.

## 3. Two-copy integrated score calculation

The common flip makes each individual bit uniform. Averaging the fixed perturbation sign changes the light pair correlation from z0=(1-2/s)^2 to z0+4delta^2 for two copies from one source, and z0-4delta^2 for one copy from each. The direct four-outcome calculation agrees with the candidate in all allocations.

At a fixed theta, the full s-coordinate pair density is Q_(theta z). Integrating the ONE shared theta produces g_z. Differentiating this finite polynomial kernel and using z partial_z Q_(theta z)=theta partial_theta Q_(theta z) gives the integration-by-parts identity. Both theta f endpoint terms vanish. The score h=(theta f)'/f=(3-5theta)/(1-theta) has mean zero and squared mean 15; the apparent endpoint singularity is square integrable against f.

Pointwise weighted Cauchy--Schwarz gives

    (g'_z(x))^2/g_z(x)
       <= z^(-2) integral f(theta)h(theta)^2 Q_(theta z)(x)dtheta.

Summing the normalized kernel proves (9), independently of s. All densities are positive in the interval used, so division is legitimate.

For s>=8, alpha<=1/2, the full interpolation interval has z>=1/2 and 1-z>=3/s. In particular each factor of Q_(theta z)/Q_(theta z0) is at most 1+s|z-z0|/3, using the baseline denominator 1-theta z0>=1-z0>=3/s for the potentially adverse parity. Thus the full ratio is at most exp(s^2|z-z0|/3)<=exp(4alpha^2/3)<2. Integrating theta preserves that ratio bound. Consequently the derivative norm against the FIXED denominator g_z0 is at most 120. Integrating in that fixed weighted Hilbert norm proves (10), including both signs of the shift. This step does not assume independent coordinates after theta averaging.

## 4. Exact mass denominator and complete Poisson tail

The nonsignal and signal cases have the same null data law Ndata, independent of mass type. Therefore the count/data difference is exactly (1-mu)C_mu(Adata-Ndata); dividing by the full null mixture gives (11). Replacing its denominator by mu C_1 is an upper bound. The reweighted Poisson(mu^2) identity has prefactor exp(2-4mu+2mu^2)/mu, as displayed. All counts and their labels are retained.

For total n=2, Poisson(2mu^2) probability is 2mu^4 exp(-2mu^2). Multiplication by (10) and the prefactor gives 3840exp(2-4mu)alpha^4mu^3/s^4, bounded by (12).

For n>=3, independently verified the falling-factorial identity and full expectation. After subtracting n=2, the remaining bracket is bounded by 1296mu^8+1296mu^6, because 1-exp(-6mu^2)<=6mu^2. For mu<=1/4 this is at most 1377mu^6. The total exponential prefactor is exp(2-4mu+6mu^2)<=exp(2)<8. Thus 4*1377*8=44064 is valid. Both contributions fit (13).

Unconditioned labels are independent, so the tensor chi-square identity applies to the COMPLETE count/data experiment. The selected mu ensures D times the label chi-square is at most 2^16(c0^3+c0^5)<2^(-43); exponentiation and the chi-square-to-TV bound give the claimed conservative bounds. Independence is only used before farness conditioning.

## 5. Globally far alternatives

Each label is good with probability at least (1-mu)(1/2)(1-exp(-s/18))>=1/4. Independent labels and the two Chernoff bounds justify (3). On a good label there are at least s/6 light coordinates with the same perturbation sign. Undoing their fixed shared flips is legitimate for a mathematical distance lower bound and does not give an oracle to the tester.

For the resulting group, the all-zero event difference is bounded below by 2j delta(1-ell-delta)^(j-1). For sufficiently large s this is at least (alpha/3)exp(-3), and twice that is strictly larger than alpha/48. On F, good-label normalized mass is at least 1/24, using the ACTUAL W<=3B. Thus the ideal full-L1 separation exceeds alpha/1152=(16/9)epsilon.

Conditioning only the alternative on F costs at most zeta_s in observation TV by mixture decomposition/data processing. No coordinate or label factorization is invoked after conditioning, and the null retains exact equality at every draw.

## 6. Normalized physical-copy experiment

Admission30 is applied with common guards and eta=1/(100B). Weight rescaling by max w leaves normalized laws unchanged; H=0 is explicitly handled by making every physical raw weight one. This rescaling is for physical encoding only: it does not change the informative raw-Poisson comparison experiment, which still uses the original w and W. Its role is to simulate normalized source rows, so there is no inconsistency between the two uses.

Probabilities remain in [1/(2s),1-1/(2s)]. The latent theta, coordinate types and flips specify coefficients, not extra uncounted spins. Common deterministic guards keep both encoded source sizes and the embedding independent of the draw. All spins are paid in N_s=O(s(log s)^(1/(k-1))). Exact-null pairs produce identical Hamiltonians. Two approximation errors cost 4eta in mutual full trace distance; eta<=epsilon/8 leaves more than epsilon as in (15).

Conditional on a latent draw, raw source totals are Poisson(W), and ordered rows conditional on totals are IID from the actual normalized source law. Since W>=B, each total supplies T=floor(B/4) rows except with probability at most exp(-9B/32). Supply events depend on latent weights, so their conditioning can bias a prior; the proof does not ignore that. One couples to unconditional ideal arrays and pays the supply-failure probability separately for each hypothesis.

Provisioning T rows from each source supports every adaptive strategy with at most T TOTAL requests. Preparing their computational-basis states and the common encoding needs no unknown-parameter oracle. Tensor telescoping over the two arrays costs at most 2Teta in acceptance probability per hypothesis. The resulting gap lower bound 1/3-4Teta-4exp(-9B/32)>0.3 eventually contradicts the full raw-experiment TV bound. Collective quantum processing cannot increase the distinguishability of its classical input experiment.

## 7. Exponents and all-size claim

The two branches of B have powers (2k+2)/3 and (4k-1)/5, respectively. The latter is smaller for k=5,6, and the former for k>=7. Both statistical terms are necessary to justify that minimum; the improved two-copy bound alone would not establish it.

The common source-size envelope with fixed constants suffices for s=floor[N/(2C_*(log N)^(1/(k-1)))]. For all sufficiently large N this has the asserted lower order and N_s<=N, without monotonicity of integer guard choices. Identical zero-Hamiltonian spectators preserve equality, full trace norm, beta, coefficient bounds and the sample-only reduction. The conclusion is the stated every-sufficiently-large-N fixed-parameter lower, with no assertion of efficient physical preparation or experimentally useful constants.

## Acceptance limits

The candidate uses classical likelihood, score, Poissonization and encoding ingredients with their stated attribution. Whether this particular composition is historically new is not settled by this review. The prior's shared latent fraction and random common flips change the declared statistical alphabet; ceilings29A--C must not be extended to it without checking their actual hypotheses. This review supplies no assertion about all possible such priors or a full-class upper bound. General P1 remains open, and G4 receives no finite-forcing supplier from this result.

### Precise ceiling29C comparison

The author supplied this clarification during review, and it is mathematically important: prior correlation alone cannot evade a pointwise tester covering every source in its alphabet. Ceiling29C's light coordinate means are ell and ell±delta; candidate32 additionally permits the complemented means 1-ell and 1-ell±delta through the fixed common bit flips. Those values are outside that exact prior alphabet. Thus the justified non-applicability statement uses the changed pointwise alphabet, not merely the shared-theta correlations after averaging. Preserve this clarification in any publication summary. No stronger claim about a possible extended tester is established.
