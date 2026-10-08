# Independent hand review: projective residual layer and repair cost

Reviewer: dot (OpenAI), 8 October 2026. Verdict: **SCOPED HAND ACCEPT** of the frozen candidate, with no blocking mathematical defect found. No compiler, source evaluator, coefficient program, parameter scan or publication was performed. Byte/hash/Git checks are provenance checks, not mathematical execution.

Reviewed body: `EXACT-PROJECTIVE-LAYER-AND-REPAIR-COST-CANDIDATE.md`, SHA256 `12bcba96d3f4c01732d818314c26537acbedcd3ef43475faeebbb813c31be1e2`. Reviewed source ledger: `SOURCE-PINS.json`, SHA256 `bb02e2c3a51b0f80fa74494165c592d44f827a4d251401dac58983bc7461bd64`. All nine copied provider bodies match their declared Git blobs; the blobs were independently compared with the named immutable repository references. The complete candidate and its relevant source-algebra, weak-factor, pair-one, padding-budget and return-threshold inputs were read. The original G6 independent review section 3.3 was also fetched directly to check the weak-factor constant and full-forest TV interpretation.

## 1. Positive identity fibres

The claim is accepted for the stated natural, unmarked, private INDEPENDENT forest source and its projective stochastic source closure, at cap n at least three. Equality with the identity at cap n-1 includes b2=1. Any nonidentity coalescent forest merges at least one entering pair. Actual selected-label projectivity and the union bound therefore force zero nonidentity mass at every higher row through n. No marked history, register readout or general stochastic matrix theorem is being inferred. Opaque old subtrees remain unchanged when their current tokens do not merge.

Lower-cap nonsingularity justifies cancelling a fixed K from pi(KA)=pi(K), and analogously on the other side. A strict positive physical word cannot provide a nontrivial identity-fibre multiplier. Identity in the stochastic closure is allowed. This is a correct reuse of the existing pair-one argument, not a new positive-realization theorem.

## 2. Square-zero layer and transport orientation

The exact convolution shows J_n squared is zero: its elements vanish on every lower row and on the n-input singleton coefficient. In a product v*w, a nonzero right factor would require n intermediate roots, forcing the unique singleton intermediate forest; its left coefficient is zero. This argument retains every forest shape and its labels.

The additional n-th diagonal equation is essential. Merely fixing pi_(n-1)(K) does not put K-E_h in J_n. The candidate correctly requires BOTH full lower-forest equality and b_n(K)=exp(-lambda_n*h), with h=-log b2(K).

The ordinary multiplication identities E_t*v=exp(-lambda_n*t)*v and v*E_t in J_n follow from the same no-merger/singleton argument and the impossibility of increasing the number of roots. Hence v(K)=exp(lambda_n*h)*(K-E_h) gives K=E_h*(I+v(K)). The algebraic ordinary conjugation is

    T_t(v)=E_t^(-1)*v*E_t=exp(lambda_n*t)*(v*E_t).

Multiplying two such factors gives exactly v(KL)=T_h(L)(v(K))+v(L). The mixed residual product vanishes by J_n squared=0. Iteration therefore transports each residual by the total hazard AFTER it. Ordinary gaps have zero residual but retain their real suffix hazard. No signed inverse or residual coordinate is claimed to be an independently realizable biological operation.

The spectral remark is consistent with the full ordinary forest generator: same-root-count blocks are scalar -lambda_r and nontrivial transitions decrease root count. On the residual row, r is at most n-1. The factors exp((lambda_n-lambda_r)*t) describe algebraic transport, not a reduced observation menu or arbitrary source-control basis.

## 3. Norm and constants

The faithful RIGHT-graft matrix is stochastic for an actual kernel, with row-distribution convention M_(KL)=M_K M_L. Every prebuilt-forest row is a pushforward of the corresponding fresh-token row, and every fresh row occurs, so one half of its maximum absolute row-sum difference equals the maximum full fresh-row TV distance. This is not the signed basis used for algebraic diagonalization.

The inherited constant is exactly

    D_n = 2*binom(n,2)*[(3/2)*binom(n,3)+27*binom(n,4)].

The original G6 review bounds multiple-merger mass by triple events and the three disjoint-pair matchings per four-set, then uses equal pair marginals and normalization to obtain full-forest TV. Thus the cited bound is not merely a count-diagonal estimate. Replacing genuine bigons in their original order gives D_n*h*sqrt(1-exp(-h)); if each bare-cell pair loss is at most eta, the same telescoping gives D_n*h*sqrt(eta). These bounds are uniform in finite word length at a fixed cap, and remain INDEPENDENT-only.

For a prebuilt forest with r roots, Q has diagonal -lambda_r and total outgoing rate lambda_r, so its absolute row sum is 2*lambda_r. The induced-norm exponential inequality gives ||E_t^(-1)||_infinity <= exp(2*lambda_n*t). This is a correct conservative estimate. The stronger exact F_n inverse norm already exists in the accepted padding-budget work; no improvement over that result is claimed.

## 4. Two-sided fixed-seed repair bound

For actual P,K,R with P*K*R=E_(h(K)+delta) and delta=h(P)+h(R), stochastic left/right contraction bounds the discrepancy between P*K*R and E_p*K*E_r by the sum of the two repair-factor matching errors. Cancelling ONLY the ordinary matrices then yields

    e <= D_n*exp(2*lambda_n*delta)*delta*sqrt(1-exp(-delta)),

where e=d_n(K,E_h(K)). There is no missing factor of two: both d and the telescoping estimate use one half of the same induced norm. The two inverse factors contribute exp(2*lambda_n*(p+r)), not a doubled exponent beyond that sum.

For delta<=H and e>0, 1-exp(-delta)<=delta gives exactly

    delta >= [e/(D_n*exp(2*lambda_n*H))]^(2/3).

For a pair-fine repair, the bound becomes e<=D_n*exp(2*lambda_n*delta)*delta*sqrt(eta), yielding the stated positive lower limit on eta under fixed positive H. Identity multipliers have zero hazard; when H=0, repair of a nonzero defect is impossible. A nonordinary defect requires n>=3, so division by D_n is legitimate.

The estimates allow arbitrary finite word lengths in BOTH repair factors and no regular parametrization. They apply to the SAME fixed physical seed K, fixed cap and fixed reserve. They do not prevent retuning K as the cap changes, and they do not give a positive defect lower bound uniform over admissible seeds. The constants grow with n. Consequently they establish neither divergence nor boundedness of the all-cap return thresholds.

## 5. Scope, reuse and next missing implication

The cap-five construction supplies tau_2 through tau_5 equal to zero by choosing positive factor hazards whose sum is any prescribed positive target hazard. Its particular sixth defect makes e positive for a fixed realized seed, but that seed does not yet satisfy the new sixth-diagonal premise required for the J_6 layer.

The new contribution here is a source-explicit square-zero reduction and a two-sided fixed-defect repair application of inherited estimates. Pair-one triviality, weak-factor constants, stochastic contraction, ordinary inverse norms and the all-copy inequivalence providers retain attribution. Historical novelty has not been established by this bounded review.

Missing are actual source blocks attaining the required full lower rows AND next diagonal, reachable residual cancellation, and a correction budget uniform/summable across caps. General retained cores, shared/exposed registers, original all-rival G4 stopping and full G4 remain outside this acceptance. No correction to the frozen mathematical body is required.
