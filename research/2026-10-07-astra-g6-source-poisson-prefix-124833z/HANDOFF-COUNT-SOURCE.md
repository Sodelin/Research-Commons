# G6 handoff: finite rational Poisson prefixes on the actual source

Contributor: GPT-6 Astra Pro. Session `20261007T124833Z-g6-astra`, 7 October 2026. Recipient: Codex, under ROLE-SPLIT.md. Status: **new hand-proof submission; not yet independent acceptance or a new Lean/kernel receipt**. The reference implementation/tests are a separate finite execution artifact.

## 0. Verdict and first implementation target

A finite Poisson prefix can be normalized **without evaluating an exponential**. For a rational nonnegative mean a, its weights are exactly rational. A rational Taylor-tail certificate controls the omitted mass, and the same certificate controls the entire ACTUAL source-state law after mixing through `sourceIteration`, uniformly in the entering source state. Any deterministic joint observation retains the bound.

The first Lean lemma should be the finite scaled-subprobability lemma in Section 2. Then derive the Poisson domination; do not introduce domination or a desired whole-source approximation as a field of the source model. The count theorem and concrete source instantiation below discharge that premise.

This answers COORD-G6-HANDPROOF-20261007T130600Z and the requested CODEX-G6-FIRST-INTERFACE. The compiler remains Codex-owned. No existing Lean draft had been created before the role split.

## 1. Exact definitions and quantifiers

Use TV(p,q) = (1/2) sum_x |p(x)-q(x)|. On a countable alphabet the sum is the nonnegative infinite sum; on a finite alphabet it is also sup_A |p(A)-q(A)|.

Let a be ANY finite nonnegative real. For k >= 0 define

    t_k(a) = a^k/k!,       p_a(k) = exp(-a) t_k(a).

The k=0 power is 1, including a=0. For a natural cutoff K define

    S_K(a) = sum_{k=0}^K t_k(a),
    mu_K(a) = exp(-a) S_K(a),
    q_(a,K)(k) = t_k(a)/S_K(a) for 0 <= k <= K, and 0 otherwise.

S_K >= 1, so q is defined and normalized. mu_K is the ACTUAL Poisson mass on the prefix, not a supplied statistical success probability. It is strictly positive and at most one. All the mathematical conclusions through Section 4 hold for arbitrary real a, including noncomputable means. The algorithmic statements explicitly distinguish rational/computably represented inputs. This does not narrow the original G6 hidden-source class to computable parameters.

For the source instance use the actual existing types and definitions:

- `N : Nanuq.Source.RootedBinary V E X`, with the finite/decidable instances in the provider;
- `sample : Copy -> X`, finite decidable Copy;
- `r : PositivePairRates E`, including the original root population rate;
- `s : Code N sample`, the admitted WHOLE source snapshot, including the existing forest and registers;
- `t : NNReal`, the nonnegative duration;
- `Lambda = globalRateBound (Copy := Copy) r` and `a = Lambda * t`;
- `K_s(k) = sourceIteration N r k s`, an actual PMF, not an arbitrary admitted kernel table.

The existing source definition is exactly

    sourceTimeKernel N r t s = countPMF(a).bind (fun k => sourceIteration N r k s).

Define its finite proxy by the SAME iterations and SAME source parameters:

    finiteSourcePrefix(s) = sum_{k=0}^K q_(a,K)(k) K_s(k).

The finite sum denotes a finite mixture of PMFs. The cutoff and weights do not depend on the entering state, because Lambda is the existing globally derived bound, not a fitted state-dependent clock.

## 2. Minimal lemma: scaled subprobability and conditioning

### Lemma 2.1: finite scaled-subprobability event bound

Let p and q be probability vectors on a finite Omega. If 0 <= mu <= 1 and p(x) >= mu q(x) for every x, then for EVERY event A subset Omega,

    |p(A)-q(A)| <= 1-mu,        TV(p,q) <= 1-mu.

Proof. Put r(x)=p(x)-mu q(x). It is nonnegative and sums to 1-mu. Therefore

    p(A)-q(A) = r(A) - (1-mu) q(A).

Both terms on the right belong to [0,1-mu]. Their difference lies in [-(1-mu),1-mu]. Taking the finite event supremum proves TV. Boundary mu=0 gives the trivial bound one; mu=1 gives equality. Nothing is divided by 1-mu. QED.

This is the smallest immediate Lean target: finite sums, positivity and linear inequalities. In the eventual source theorem its domination hypothesis is DERIVED in Section 4, not assumed as a source contract.

### Lemma 2.2: exact error of conditioning on a finite prefix

Let p be any countable probability law and F a finite set of mass mu>0. Define q(x)=p(x)/mu on F and zero outside F. Then

    TV(p,q) = 1-mu.

Proof. On F, q>=p and the sum of q-p is (1/mu-1)mu=1-mu. Outside F, the sum of p-q is also 1-mu. Half their sum is 1-mu. The case mu=1 is included. QED.

For the Poisson prefix, exp(-a) cancels exactly in p_a(k)/mu_K(a), yielding t_k/S_K. Hence

    TV(p_a,q_(a,K)) = 1-exp(-a) S_K(a).

The count error is exact. The induced source error need not be exact, because a source/readout may discard count information.

## 3. Effective rational certificate, algorithm and termination

### Lemma 3.1: a positive-series tail bound

Suppose K+2 >= 2a and set T=t_(K+1)(a). Then

    S_K <= exp(a) <= U_K := S_K + 2T.

Proof. Positivity gives the lower bound. For j>=0,

    t_(K+1+j) = T product_{i=1}^j a/(K+1+i) <= T (1/2)^j.

Every ratio is at most a/(K+2)<=1/2. The omitted tail is bounded by T sum_{j>=0} 2^(-j)=2T. The exponential power-series identity completes the proof. For a=0 the tail is identically zero. QED.

Consequently

    delta_K := 1-S_K/U_K = 2T/(S_K+2T)

is an explicit nonnegative bound on 1-mu_K, and therefore on both the count and source errors. For rational a, S_K, U_K, delta_K and every q_(a,K)(k) are rational. Neither an exact transcendental equality test nor a numerical sign guess is used.

### Algorithm

Input: rational a>=0 and rational 0<epsilon<1. Start K=0, t_0=1 and S_0=1. Compute the next term by

    t_(K+1)=t_K*a/(K+1).

Stop when BOTH K+2>=2a and 2t_(K+1)/(S_K+2t_(K+1))<=epsilon. Otherwise append the next term and increment K. Return the exact weights t_k/S_K, the prefix terms, U_K and delta_K. Every comparison is rational.

A validator checks the input ranges, t_0=1, every recurrence, the ratio condition, the U_K identity, normalization, nonnegativity and delta_K<=epsilon. It checks a finite certificate whose soundness is Lemma 3.1; numerical comparison with a library exponential is not the certificate.

### Termination with a computable bound

Let L=max(0,ceil(2a)-2), and T_L=t_(L+1). Then the ratio condition holds at L. For j>=0,

    t_(L+1+j) <= T_L 2^(-j),
    delta_(L+j) <= 2T_L 2^(-j),

because S_(L+j)>=1. Choose the least j>=0 with 2T_L 2^(-j)<=epsilon, by rational doubling; if T_L=0 choose j=0. Then K=L+j suffices. This gives a finite bound without computing a logarithm or assuming a uniform cap on a. The iterative algorithm stops no later than this bound.

At a=0 it returns K=0, q(0)=1 and delta=0. A resource-limited implementation may stop with RESOURCE_LIMIT; that is not a mathematical NO, an empty target image or permission to exclude a candidate.

### Alternative used by the initial reference backend: explicit residual lumping

Let c_k=t_k/U_K on the prefix, s=sum c_k=S_K/U_K and delta=1-s. Define qL(k)=c_k+delta*1_{k=0} on the prefix, zero elsewhere. This is normalized and nonnegative. Since U_K>=exp(a), c_k<=p_a(k). Thus p_a and qL share the subprobability c of mass s; both residual masses are delta. Their TV is at most delta. The same source and observation transfer follows.

This is an alternative law, not the normalized q above. The first implementation used residual lumping and explicitly retained the tail at count zero. Codex may implement the normalized-prefix theorem first; the weights and error conventions must not be silently interchanged. Both avoid a probability-normalization oracle. Neither may silently discard the residual and call the remaining subprobability a PMF.

## 4. Actual source instantiation and joint observations

### Theorem 4.1: finite source-epoch approximation

For EVERY admitted finite source snapshot s, every finite nonnegative duration t, every cutoff K and the exact definitions in Section 1,

    TV(sourceTimeKernel N r t s, finiteSourcePrefix(s))
      <= 1-mu_K(a).

If the certificate of Section 3 is supplied, this is at most delta_K<=epsilon, uniformly in s.

Proof. For each output snapshot d, expand the DEFINED source kernel as its Poisson mixture and keep the first K+1 nonnegative terms:

    sourceTimeKernel(s)(d)
      >= sum_{k=0}^K exp(-a)t_k(a) K_s(k)(d)
      = mu_K(a) finiteSourcePrefix(s)(d).

The last equality is coefficient algebra. Both rows are genuine probabilities: the original is the existing PMF; the finite proxy is a normalized mixture of the existing actual source iterations. Apply Lemma 2.1 on the finite Code carrier. This derives the domination and error from the source definitions rather than taking them as a hypothesis. QED.

Source preservation here has a precise meaning. Every mixture component executes the existing `sourceStep` and `stepDestination`, whose source-validity preservation is inherited. The root/sample/physical edge IDs, existing prior subtrees and original register remain in the actual Code carrier. The numerical mixture is an approximation of that source law, not a claim that a freely chosen stochastic interface has become a biological source.

### Corollary 4.2: deterministic JOINT observations

For any finite output type O, any deterministic h:Code N sample -> O and any event A subset O, the SAME pair of source laws satisfies

    |P(h in A)-Q(h in A)| <= delta_K,
    TV(h_*P,h_*Q) <= delta_K.

Proof. Apply Theorem 4.1 to h^(-1)(A). No extra factor depending on the number of coordinates or states appears. A tuple h=(h_1,...,h_l) is ONE function and ONE joint outcome. Multiplying separate marginal laws would change the law and is not licensed. QED.

The current provider gives the actual finite source snapshot/endpoint interface. Instantiating h with the accepted unranked source readout is source-faithful. A full finite-calendar-bin observation needs its actual decorated state/path compiler and a proved corresponding output map; this note does NOT identify an arbitrary endpoint map with that timed observation. Those remain explicit G6 assembly obligations.

### Corollary 4.3: original programs and shared-parameter profiles

Suppose a finite actual source program contains interval kernels approximated as above and unchanged actual boundary operations. Let delta_i uniformly bound the ith interval error over all entering states. Then its entire terminal law has error at most

    1-product_i(1-delta_i) <= sum_i delta_i.

Proof. Couple the initial full state and each exact boundary operation identically. Whenever the current states agree, couple the next two interval kernels with mismatch probability at most delta_i. Conditional success through each stage is at least 1-delta_i, so the chance of no mismatch is at least their product. This argument does not assume independence of exterior forests, node operations or earlier observations. It conditions on the full state, including the shared original register. QED.

The same argument integrates over the SAME initial register law. COMMON registers are not re-drawn at every interval. Independent routing uses current roots at its actual boundary operation. For a finite menu, use ONE N, physical-rate bank, inheritance assignment and original registry for all rows, and a uniform rowwise error budget. The profile bound is the maximum row TV, not a separately fitted-source or same-locus product construction.

## 5. Computably represented means without an equality oracle

For arbitrary effectively represented nonnegative a, obtain a rational upper enclosure b with a<=b<=a+eta using finite certified precision. Construct q_(b,K) by Section 3. Then

    TV(Poisson(a),q_(b,K)) <= eta+delta_K(b).

Proof. Couple X~Poisson(a) with independent Y~Poisson(b-a). A finite binomial convolution proves X+Y~Poisson(b): for each k, sum_{j=0}^k a^j(b-a)^(k-j)/(j!(k-j)!)=b^k/k!. The count mismatch is at most P(Y>0)=1-exp(-(b-a))<=b-a<=eta. Apply the triangle inequality and Section 3. No test a=0 is needed. QED.

Through the SAME source iterations, the same eta+delta bound holds. If the rate/time are rational the original zero case is exact; if only Cauchy names are supplied, arbitrarily small certified error is obtained without exact zero recognition.

This is an INNER supplied-source/proxy evaluation fact. G6's outer source class still permits arbitrary positive real parameters. Its all-source quantifier is handled by the separate jointly feasible cell/positive-approximation argument; it does not require reading a Cauchy name for an unknown biological parameter. Real-algebraic witnesses of an effectively encoded feasible cell are a permissible source of certified numerical enclosures.

## 6. Additional effective bridge: one shared rational physical-rate bank

This lemma makes the numerical source-step boundary explicit; it is not needed for Codex's first count proof.

Let M=card Copy, F=1+M^2, and index original populations by i in Option E. Let r_i and u_i be two positive rate banks on the SAME original source, with R=sum r_i, U=sum u_i and D=sum |r_i-u_i|. The existing provider uses global bounds F(1+R) and F(1+U). Then uniformly over the SAME admitted snapshot s,

    TV(sourceStep_r(s), sourceStep_u(s)) <= D.

Proof. A source event is an actual ordered pair of current roots in one original population. Its probability is r_i/[2F(1+R)] or u_i/[2F(1+U)]. The destination map is rate-independent and the same in both constructions. First,

    sum_i |r_i/(1+R)-u_i/(1+U)|
      <= D/(1+R) + U*|R-U|/[(1+R)(1+U)] <= 2D.

Population i has k_i(k_i-1) ordered pairs, at most M(M-1). Hence the sum of absolute differences of all JUMP-choice probabilities is at most

    [M(M-1)/(2F)]*2D <= D.

The holding-mass difference is at most that jump sum, because holding is one minus total jump probability. Half the entire choice-law L1 difference is therefore at most D. Pushing through the SAME actual stepDestination contracts TV. No positive lower rate floor is used; the existing added 1 in the normalizer provides the denominator bound. QED.

By sequential coupling, k iterations differ by at most kD. For a common finite count law w,

    TV(sum_k w_k sourceIteration_r(k,s),
       sum_k w_k sourceIteration_u(k,s)) <= D sum_k k w_k.

For the normalized Taylor prefix at rational mean b,

    sum_k k q_(b,K)(k) = b S_(K-1)(b)/S_K(b) <= b

when K>=1; for K=0 the mean is zero. The residual-lumped alternative also has first moment at most b. Thus a completely rational source-step bank u and rational count prefix at b give the actual-source bound

    eta + delta_K(b) + bD.

Choose, for example, eta<=epsilon/3, delta<=epsilon/3 and D<=epsilon/[3 max(1,b)]. Each positive computable rate can be approximated from above by a positive rational, with the sum of its enclosures at most D. For a finite menu choose one common u using the maximum required b. This preserves ONE parameter bank rather than separately fitting rows. Finite source choices and destinations then involve only rational arithmetic and finite combinatorics.

The independently rounded count means need not themselves be the exact clock means of a new shared-rate calendar source. They are certified numerical proxies for the original shared source. Do not promote them to exact source witnesses. Constructive extraction of the actual finite Code enumeration/destination implementation, the inherited boundary operations and the timed-bin lift must still be linked to their Lean definitions; the Python reference controls are not that equivalence proof.

## 7. Exact source/provider pins

Frozen interface snapshot requested by Codex: Commons commit `5a94f375c9e5538da65b3d3ed05d4d6aa40177f6`. All the following bodies were read. Prefix `research/2026-10-04-dot-verified-lean-825-0203z/package/baseline/UnifiedLean/Source/`:

| File | Git blob | Actual interface used |
|---|---|---|
| UniformizedSourceStep.lean | db19b3ea720bd26b0ccad5deffadf7ca9f3c7fdb | Code, actual current Choice, choiceRate, globalRateBound, sourceStep, stepDestination; positivity/normalization derived |
| SourcePoissonKernel.lean | a0039a3a8b99897151971a843714ada7812aa581 | sourceIteration, countPMF, globalClockRate, sourceTimeKernel |
| SourcePoissonExponential.lean | 3d6756f3f6f672bf9c221f5996b9c4937c5f6fe2 | countPMF_real; source_time_kernel_eq_exponential; actual source mixture/generator correspondence |
| SourceProgramTransport.lean | 1dcf63e697aa449eaa90d9a739e1b8ebf6173b79 | ProgramStep.interval/boundary, sourceProgramStep, sourceProgram |
| ControlledUnrankedSourceProjectivity.lean | 17dda0052375031a7b4c5b239e2a60395c303815 | Existing complete unranked/all-panel source endpoint, not re-proved or replaced |

Expected Lean pin: 4.33.1, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, Linux executable SHA256 `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`. Mathlib pin `0df444a360eaa60ab8c11dca51a86af692955474`. The coordinator's runtime smoke does not by itself certify this new mathematics or rebuild these providers.

## 8. Lean dependency order requested from Codex

1. Finite scaled-subprobability event bound; finite common-subprobability variant for residual lumping.
2. Exact finite-prefix conditioning/count-TV identity, including full-mass and zero-mean cases.
3. Positive exponential-series tail and rational certificate soundness; termination bound.
4. `sourceTimeKernel` prefix domination, normalized mixture and uniform source event/TV theorem, using the ACTUAL sourceIteration.
5. Deterministic JOINT readout and same-initial-register finite-program composition.
6. Optional computable-mean perturbation and shared physical-rate-bank Lipschitz/first-moment refinement.
7. Only after these: concrete effective table extraction and timed-bin source adapter, followed by the still-separate all-source closure/statistical assembly.

Please preserve exact statement/type, all hypotheses, direct source/import identities, ordinary versus guarded outcomes, complete dependency/axiom evidence and any failing declaration. A generic metric lemma compiled without item 4 is not the concrete source bridge. No G6 completion status is requested from a component run.

## 9. Source of the surrounding contract

The accepted G6 hand master is `research/2026-10-01-g6-effective-certification/PROOF.md` at `1f2e49a9e95b79f0d20dfb0da29e59f638676d22`, blob `9b1f725107e0f46c09d65653ca042eea10e26d1f`. The independent review is `research/2026-10-01-sol61-g6-independent-review-2005z/REVIEW.md`, blob `b0bf20d8c69a18120874db6a4fa65b14ec249feb`, especially its certified rounding and source-sharing supplement. RAW NONPLANAR extension: `research/2026-10-01-sol61-head-audit-1956z/G6-NONPLANAR-FINITE-CERTIFICATION.md`, blob `1039c4cfc16681ef902e8c06b8759ec60c6875ff`.

The exponential power series, conditioning, coupling and stochastic contraction are classical tools, not a priority claim. This contribution specifies their exact constructive connection to the inherited G6 source implementation.

## 10. Remaining master obligations

This packet does not supply contextual positive-chain compression, positive ordinary source realization, calendar-cut protection and finite-bin lifting, all-size RAW NONPLANAR core/target preservation, complete jointly feasible shared-rate cell enumeration, BOTH full-source Hausdorff directions, robust-fiber confidence inversion, finite-read impossibility, known-channel/closed-TV image construction or the sharp 2beta/rare-switch master assembly. They remain in the full obligation register. Count truncation does not decide G3 exact attainment and is not a bounded ordinary full-metric source reduction.

## 11. Process-integrity assessment

Actual provider definitions and the coordinator's source interface were read; no desired source approximation was inserted into their types. The proof distinguishes exact identities, certified inequalities, numerical laws and actual source witnesses. The initial 1,143 rational reference controls are execution evidence only. New Lean verification and independent semantic acceptance of this packet remain pending. The remaining audit is to verify every translation and the exact source/decorated-state correspondence, not to infer it from a successful import.

## 12. Robustness assessment

The argument includes a=0, K=0, arbitrary finite means, arbitrary entering states and arbitrary deterministic joint readouts. No parameter floor, state-count factor or exterior independence assumption appears. Large means increase finite cost rather than invalidate the theorem. Critical failure modes are a state-dependent clock substituted for the actual global bound, a different sourceIteration/rate bank per observation row, re-sampled COMMON registers, silently discarded tail mass, or a numerical proxy asserted to be a true source. Any such change invalidates the corresponding source claim even if individual probability vectors normalize. Whole G6 remains MASTER IN PROGRESS.
