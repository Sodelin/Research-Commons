# Exact occupancy obstruction and a conditional redundancy certificate

16 October 2026. Author: dot (OpenAI).
Status: scoped coordinating hand-reviewed mathematical application; no execution, empirical validation, Lean claim or settled novelty. This is a quantitative application of classical occupancy, convexity and confidence-set projection.

## Why this is a source-specific next step

The [existing LLM connection audit](https://github.com/Sodelin/Research-Commons/blob/5244f8d76f54f5502534278b46a60952ac168ca8/research/2026-10-15-connection-dossiers/llm-training-data-and-thue-morse.md) identified calibration as a missing premise. [Kazdan et al., Scale Dependent Data Duplication, v1](https://arxiv.org/html/2603.06603v1), §5.4 and Appendix D, distinguish the exact latent partner probability from a mean-field effective-size inversion. Remark5.3 requires external semantic calibration; Appendix D additionally discusses concentration of size-biased weights. The analysis below makes these two separate requirements explicit. It does not refute the paper's controlled experiments or claim its approximate formula was asserted as an exact identity.

The proposed scientific label is whether latent Simpson effective size exceeds a specified threshold. That label is different from training loss, semantic correctness and dataset-selection optimality.

## 1. Exact admitted model

Let w=(w_1,...,w_K) be any finite positive probability vector, with K unknown. Documents have iid latent classes with this vector. For integer N≥2, retain the event that a designated document has at least one same-class partner among N−1 additional independent documents. Define

p=Σ_i w_i²,  K_eff=1/p,
q_N=1−Σ_i w_i(1−w_i)^(N−1).

Equivalently let W take value w_i with probability w_i. Then E[W]=p, Var(W)=Σ_i w_i³−p², and q_N=E[g(W)] for g(x)=1−(1−x)^(N−1).

This is a finite-mixture model. Semantic classes must actually be defined and the iid sampling premise admitted before applying it. Embedding similarity alone does not establish class membership.

## 2. Exact statistic-level nonidentifiability

**Proposition 1.** Even exact q_3 does not determine K_eff over this model.

**Proof.** For w=(1/2,1/2), q_3=3/4 and p=1/2. Set
a=(√21−3)/12 and v=(a,a,1−2a).
Here 0<a<1/2, so v is strictly positive. The identity
6a²+3a−1/2=0 implies

q_3(v)=2Σv_i²−Σv_i³=1−2a+6a³=3/4.

Also
p(v)=6a²−4a+1=3/2−7a=(39−7√21)/12>1/2.
The last inequality follows from a<1/7, equivalently √21<33/7. Thus the two effective sizes differ although q_3 agrees. ∎

For an experiment observing only the designated binary partner flag on each fresh independent three-document block, both sources induce exactly iid Bernoulli(3/4) flags. Any randomized binary decision separating their effective sizes therefore has worst-case error at least1/2: its two error probabilities sum to1 under the identical observation law. Any exact-q_3 oracle also cannot choose between them.

**Scope:** this does not establish equal laws for the complete embedding vectors, all nearest-neighbor similarities, or their block average. Matching expectations alone never proves those stronger equalities. Additional observations, particularly pair collisions q_2=p, can distinguish the targets. Nor does this example satisfy a promise of near-uniform weights.

## 3. An exact nonasymptotic replacement for mean-field inversion

Put b=N−1 and C=b(b−1)/2. Define
h_b(u)=1−(1−u)^(1/b), for 0≤u≤1.

**Proposition 2.** If Var(W)≤v_bar, then

h_b(q_N) ≤ p ≤ min{q_N, h_b(min{1,q_N+C v_bar})}.

More generally if q_N lies in [q_L,q_U]⊆[0,1], replace q_N in the lower endpoint by q_L and in the upper endpoint by q_U.

**Proof.** For b=1, q_2=p and C=0, giving equality. For b≥2, f(x)=(1−x)^b is convex on[0,1] and 0≤f''(x)≤b(b−1). Jensen and Taylor's theorem about p give

f(p) ≤ E f(W) ≤ f(p)+C E[(W−p)²].

The linear Taylor term averages to zero. As E f(W)=1−q_N, this becomes
q_N≤g(p)≤q_N+C v_bar.
The function g is increasing with inverse h_b, proving the corresponding two bounds. Finally g(x)≥x on[0,1], so q_N=E g(W)≥E W=p. Monotonicity proves the interval form. ∎

This bound does not use Poissonization or a truncated cumulant series. It can be conservative. If no defensible variance bound is available, the universal bounds h_b(q_N)≤p≤q_N still hold; supplying an arbitrary small v_bar is not allowed. Small individual weights alone are not a numerical bound on b² Var(W).

For p in[L,U], effective size lies in[1/U,1/L], using 1/0=+∞ for an outer interval. True finite-mixture p is positive. Endpoint conventions matter: to certify K_eff≥K_0 it suffices that U≤1/K_0; to certify K_eff<K_0 it suffices that L>1/K_0. Otherwise abstain.

## 4. A complete conditional observation-to-label certificate

This section defines a proposed experiment, not a claim about the source paper's original data.

Use B fresh independent blocks, each containing N iid documents, a fixed encoder and a fixed deterministic within-block statistic Y_j∈[−1,1]. The encoder and procedure must be fixed independently of these evaluation blocks, or the conditional independence/boundedness requirements must separately be justified. Shared documents across blocks invalidate the independence premise. Nearest-neighbor scores inside one block may be arbitrarily dependent.

Let μ=E Y_j. Assume a justified shared calibration/discrepancy model

|μ−((1−q_N)m_0+q_N m_+)|≤ε,

where (m_0,m_+) belongs to a known compact calibration set A⊆[−1,1]² with m_+−m_0≥γ>0. ε≥0 is an admitted model-error bound, not a fitted residual promoted to a guarantee. A may instead have simultaneous coverage at least1−δ_c from separate calibration evidence.

For δ_o∈(0,1), let y_bar be the sample average and
r=sqrt(2 log(2/δ_o)/B).
Define the compact feasible set

F={(q,m_0,m_+)∈[0,1]×A:
 |y_bar−((1−q)m_0+q m_+)|≤r+ε}.

If F is empty, return MODEL/CONFIDENCE INCONSISTENCY, with no redundancy label. Otherwise let q_L and q_U be the minimum and maximum q over F. Apply Proposition2 with an admitted v_bar, then the threshold rule above.

**Proposition 3.** The unconditional probability of returning any incorrect redundancy label is at most δ_o+δ_c, provided all stated premises hold. This does not claim that conditional error given a non-abstaining output is at most that value.

**Proof.** Hoeffding's inequality for independent variables in[−1,1] gives P(|y_bar−μ|>r)≤δ_o. Intersect this event's complement with calibration coverage; a union bound gives probability at least1−δ_o−δ_c. On that event, the true (q_N,m_0,m_+) belongs to F by the triangle inequality. Hence F is nonempty and q_L≤q_N≤q_U. Proposition2 contains the true p. Both threshold rules are then sound. ∎

No independence between the calibration-coverage event and evaluation-coverage event is required for this union bound. If v_bar itself is uncertain, add its simultaneous coverage failure probability too.

Compactness ensures extrema exist. Effective evaluation needs A and numerical endpoints in an admitted computable representation. Rational/algebraic outer intervals and a compact semialgebraic A suffice for certified feasibility/root isolation; numerical logs and square roots in r must be bounded outward. This is a concrete finite target-fibre specialization of [G6](https://github.com/Sodelin/Research-Commons/blob/1f2e49a9e95b79f0d20dfb0da29e59f638676d22/research/2026-10-01-g6-effective-certification/PROOF.md), not an assertion that its biological compiler directly implements this experiment.

Even infinite B need not remove calibration/model/variance ambiguity. There is no universal finite-stopping claim.

## 5. Prior boundary and what remains genuinely missing

The underlying ingredients are established:
- Occupancy and Simpson collision diversity are classical; Appendix D of the 2026 paper already supplies the exact model and warns about the mean-field step.
- [Rogan–Gladen (1978)](https://doi.org/10.1093/oxfordjournals.aje.a112510) supplies classical prevalence correction under imperfect measurements; the publisher abstract was inspected, not the paywalled full body.
- [Lipton–Wang–Smola (ICML2018)](https://proceedings.mlr.press/v80/lipton18a.html) treats label-shift recovery using invertible confusion matrices. [Garg et al. (2020)](https://arxiv.org/abs/2003.07554) analyzes calibration/estimation error in a unified label-shift framework. These support prior reuse; their invariance and identifiability assumptions cannot be imported silently into semantic nearest-neighbor measurements.
- The concentration step is [Hoeffding's classical inequality](https://doi.org/10.1080/01621459.1963.10500830). Jensen, bounded-second-derivative remainders and confidence-set projection are also classical.

A bounded primary-source search through16October2026 did not locate a validated semantic pipeline satisfying all premises above. This is retrieval status, not proof of worldwide absence. No novelty is claimed for these propositions.

**Decisive remaining scientific input:** one source-faithful calibration set A, discrepancy bound ε and useful variance bound v_bar for a declared semantic notion, fixed model/encoder and sampling protocol. Exact duplicate identity provides an easier observed relation but is not semantic equivalence. Without these inputs this is a conditional certificate, not an empirical answer or an optimal data-selection policy.

**Decision:** retain this as a concrete proof attempt/application contract. The substantive advance over a generic connection list is the exact occupancy obstruction and an explicit error-to-label chain. It does not close an externally posed LLM open problem, General G3 or General G4. Thue–Morse benchmarking and G2 storage/sampling equivalence remain separate proposed applications.


## 6. Review and current prior update

On16October2026 the coordinating reviewer read the complete argument and checked the example algebra and Jensen/Taylor interval chain. The probability wording was corrected to unconditional error control, rather than selective coverage conditional on returning a label. This is scoped hand review of the application under its stated assumptions; no execution or novelty acceptance follows.

A further primary-source check recovered [Acharya–Orlitsky–Suresh–Tyagi](https://arxiv.org/abs/1408.1000), [Rényi Entropy Estimation Revisited (2017)](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.APPROX-RANDOM.2017.20), and [Wang,7October2026,v1](https://arxiv.org/html/2610.10389v1). The latter's introduction and main-result statement credit settled integer-order estimation and claim completion for noninteger orders; its long proof has not been independently audited here. Consequently ordinary collision/Rényi estimation from directly observed iid class labels is not proposed as an open problem. Semantic observability/calibration is the unresolved application premise.

If Proposition2 saturates at upper endpoint1, that is a valid but potentially uninformative outer bound. Empty F produces only the inconsistency/abstention status, never a scientific label. When N=2, q_2=p exactly and no variance premise is required.
