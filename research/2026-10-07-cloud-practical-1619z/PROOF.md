# Joint betting on the unchanged nine literal means

Contributor: Codex / CLOUD-G6-SOL-ULTRA-20261007 practical solver lane, 7 October 2026. Evidence level: hand-derived argument plus a bounded rational research receiver; independent review pending. This is an instance of established betting/martingale confidence methods, not a novelty claim.

## Exact intended endpoint and current contribution

The master remains useful certified inference over the entire original nine-parameter fixed pulse architecture, original domain and nine shifted mean map, with all normalized physical widths at most 1/20. This contribution supplies a conditional joint confidence construction and a conservative mean-box exclusion receiver. It does not establish useful uniform widths, a sufficient practical sample count, numerical inverse completion or source existence.

The current accepted frontier rules out the old common-radius procedure and two specified simple symmetrized box substitutions through the original 100,000-locus extractor cap. Those method-specific failures are unchanged. The following uses the old literal per-locus vector itself, rather than adopting the proposed symmetrized statistic or adding AA2/BB2/CC2.

## 1. Original source and exact observable

Let D be the original parameter box: h,u,v in [1/32,1/8], g in [1/6,2/3], and rA,rB,rC,rAB,rR in [1/2,6]. One shared theta determines the original fixed ((A,B),C) pulse source, population rate ties and nine shifted means F(theta). Keep the six contemporary labelled phased copies A1,A2,B1,B2,C1,C2, homogeneous stationary normalized clock-JC, two preselected conditionally independent sites on the SAME genealogy, and independent complete loci. Root/ID/selection/calibration/source-admission obligations are inherited unchanged.

For each complete locus i, define the nine-vector X_i by the original literal extractor:

    X_{i,P k} = (1 + product_{s=1}^k chi(base_{P.left,s}) chi(base_{P.right,s}))/2,
    features = AC1,AC2,CC1,BC1,BC2,AB1,AB2,AA1,BB1.

Here chi(A)=chi(C)=1 and chi(G)=chi(T)=-1, and the fixed pairs are those in the old extractor. Every entry is in {0,1}; under the admitted original source E[X_i | earlier complete loci] = mu = F(theta). Dependencies among features, copies and sites within a locus remain unrestricted except for the original law used to justify these expectations. No coordinate or site is a separate independent observation.

`literal_rows` authenticates original integration_core.py SHA256 f409f3ae1cfeb04db61f7b3b9f0aad76e18e372c57289463ad7d5622023b131e, calls its exact byte/dataset/complete-panel/selection validation and its actual extractor, and checks that every new per-locus column sums to the old literal count. Counts alone do not retain the joint locus information; the original complete observations are required. The mathematical forward map and normalized target are unchanged, and shifted means are not transformed a second time.

## 2. Predictable joint strategies

Before observing the experiment, freeze a finite list of directions d_a in Q^9 with 0<||d_a||_1<=1 and positive rational weights w_a summing to 1. Directional comparisons may involve multiple features of the SAME locus; they do not independently fit parameter rows. Freeze the following strategy rule as well.

For a candidate mean vector mu in [0,1]^9, set p_a=d_a dot mu and Z_{a,i}=d_a dot X_i. At the first locus choose lambda_{a,1}=0. From the n=i-1 preceding loci, calculate

    A_{a,n} = (sum_{r<=n} Z_{a,r})/n,
    V_{a,n} = (sum_{r<=n} Z_{a,r}^2)/n - A_{a,n}^2,
    lambda_{a,i}(mu) = clip_{[-1/2,1/2]}((A_{a,n}-p_a)/(V_{a,n}+1/16)).

The nonnegative exact empirical variance V is used only to choose a predictable stake. It is NOT asserted to upper-bound the population variance. The 1/16 regularizer and 1/2 stake cap are fixed parts of this receiver; no performance optimality is asserted.

Candidate dependence is legal: for each fixed mu, lambda_i(mu) is a measurable function of the earlier loci. It does not inspect the current locus. Choosing directions, weights or the algorithm after inspecting the entire experiment would invalidate this claim unless separately justified; a hash by itself cannot prove predeclaration.

Since |d_a dot (X_i-mu)|<=||d_a||_1<=1, every capital factor lies in [1/2,3/2]:

    K_{a,t}(mu) = product_{i<=t} [1 + lambda_{a,i}(mu) d_a dot (X_i-mu)],
    E_t(mu) = sum_a w_a K_{a,t}(mu),  E_0(mu)=1.

At the true mu, conditional expectation of each factor given the past is exactly 1, regardless of within-locus covariance. Thus each K_a, and their fixed weighted mixture E, is a nonnegative martingale. Bounded factors make every finite-prefix capital integrable. This proof needs only the stated conditional mean law; independent complete original-model loci provide it. It does not establish that a finite RNG or empirical biological dataset has that law.

## 3. One simultaneous event, all prefixes and source boxes

For 0<delta<1, the nonnegative martingale maximal inequality gives

    P_mu(exists t>=0: E_t(mu)>=1/delta) <= delta.

Define the mean confidence sequence and the physical retained set by

    C_t = {m in [0,1]^9: E_s(m)<1/delta for all s<=t},
    R_t = {theta in D: F(theta) in C_t}.

With probability at least 1-delta, the true original source is in R_t for every prefix t. The event is pointwise at the actual unknown source; no union bound over the uncountably many candidate parameters or the nine coordinates is needed. All boxes and source points tested with this SAME predeclared process and delta inherit this one event. Running additional plans and selecting their strongest evidence after observing data needs a predeclared mixture or additional error spending. These claims do not authorize mixing a new process with old confidence events without the correct budget.

An early stop based on crossing or resource limits retains the same guarantee, because all possible processed prefixes were already covered. A resource-limited prefix is not an assertion that the full current stream was numerically processed. A nonempty R_t/outer cover does not prove an admitted witness; an empty outer cover signifies a conditional confidence/model conflict. Source existence and physical accuracy remain separate gates.

## 4. Rational interval exclusion receiver

Supply a rectangular nine shifted-mean box B. For each direction its interval P_a encloses d_a dot m for every m in B. Previous directional sums and squares are exact rationals from the retained complete locus vectors. The monotonic clip map encloses lambda_i(m); ordinary interval products enclose each factor. Intersect the factor enclosure with the proved universal [1/2,3/2] bound. All resulting lower endpoints are nonnegative, so multiplying interval endpoints encloses every candidate capital K_{a,t}(m). A positive weighted sum gives a lower bound L_t(B) for E_t(m), simultaneously for every m in B.

If L_s(B)>=1/delta at any processed prefix s, B is disjoint from C_t for every t>=s. The receiver reports CONDITIONAL_MEAN_BOX_EXCLUDED. Otherwise it reports UNKNOWN, including arithmetic stops. It does not claim that B contains a compatible source or that every nonexcluded point is in C_t. Lost dependency between candidate means in the interval operations can weaken an exclusion, never strengthen it falsely.

For an original physical parameter box Q, a separately authenticated certified enclosure F(Q) subset B would transfer a mean-box exclusion to physical-source exclusion. This is the actual source-to-answer bridge needed for contractor integration. The current receiver does NOT implement or certify that physical enclosure/journal bridge and sets `physical_source_box_excluded` false. It has not changed the original numerical backend, source pins or admission registry.

The exact products can grow costly. The implementation has a caller-declared rational bit budget, validates every supplied literal row, and stops before accepting an oversized candidate update. It preserves any earlier safe evidence. This is a bounded research receiver rather than a scalable 100,000-locus localization claim.

## 5. Governing prior and novelty boundary

- Ian Waudby-Smith and Aaditya Ramdas, *Estimating means of bounded random variables by betting*, [arXiv:2010.09686v7](https://arxiv.org/abs/2010.09686v7), §4 equation (23), Propositions 2–3 (PDF pp13–14) and Theorem 1 (p7): predictable centered capital products and test inversion into all-time confidence sets. The joint centered increment above is an elementary bounded-vector instance of this framework.
- Glenn Shafer, Alexander Shen, Nikolai Vereshchagin and Vladimir Vovk, *Test Martingales, Bayes Factors and p-Values*, Statistical Science 26(1), 84–101 (2011), [DOI 10.1214/10-STS347](https://doi.org/10.1214/10-STS347), [arXiv:0912.4269v3](https://arxiv.org/abs/0912.4269v3), PDF p4 equation (2): nonnegative supermartingale maximal inequality; p3 credits Ville's 1939 thesis.

Exact relevant passages were independently fetched/read by the internal literature/organization lane. This packet attributes the method and supplies its original-source/same-map receiver argument. It makes no claim that betting, covariance-aware inference or confidence sequences are new.

## 6. Remaining practical obligation

The receiver is a justified genuinely joint/data-adaptive alternative to the already rejected simple box substitutions, but validity is not usefulness. A source-faithful stronger direction requires: independent semantic review; actual extraction/admission binding of a frozen plan; a certified enclosure/checker integration over the unchanged physical domain; bounded arithmetic suitable for the desired observation count; useful sufficient precision across the full domain; and verified complete-union widths at the original 1/20 target. No sample, likelihood fit, full catalogue, simulator or new source experiment has run here.
