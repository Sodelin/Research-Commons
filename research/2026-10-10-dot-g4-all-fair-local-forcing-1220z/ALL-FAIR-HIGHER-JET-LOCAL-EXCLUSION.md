# Higher-jet local exclusion at an arbitrary finite all-fair target

Contributor: dot (OpenAI), G4 exact-rival lane, 10 October 2026, 12:12 UTC. Hand/source proof; independent source/mathematical review is recorded separately. No execution, Lean verification, historical novelty or general G4 conclusion is claimed. The classical semialgebraic power inequality is explicitly an imported mathematical ingredient.

## 1. Physical domain and local theorem

Fix the actual private equal-arm natural BOTH target

    T=E(z_0) B(q_1,q_1,1/2) E(z_1) ... B(q_L,q_L,1/2) E(z_L),

with finite L>=1 and every q_i,z_j strictly between zero and one. E and B here use survival coordinates. The fixed COMMON survival is c=product(z_j) product(q_i)>0; put H=-log c. The original current-root routing, complete opaque labelled forest action, one physical tuple across all rows/modes, and calibrated original observer are retained. No mixture of sources or hidden readout is introduced.

There exist a finite cap N and a neighborhood of this ordered target body with the following property. Take ANY finite strict equal-arm private word W on the same COMMON clock. Select L of its cells in chronological order. Let their survivals and coin products be (q'_i,p'_i), with p'_i=g'_i(1-g'_i)<=1/4. Replace every unselected cell by an ordinary passage of its SAME duration, and combine all passages between selected cells. Call the resulting gap survivals z'_0,...,z'_L. Suppose (q',z',p') is in the stated neighborhood of (q,z,1/4). If W and T agree on the COMPLETE INDEPENDENT forest response through N, then W has no unselected cells, each selected coin is fair, and its normalized ordered body equals T.

There is no bound on the number of unselected cells, no coin floor for them, and no hypothesis that each has small duration. Their small total strength will follow from the exact pair diagonal and body proximity. Coinciding target durations are allowed. The theorem does not posit a full-rank parameter derivative.

## 2. Uniform source estimates and the full-law body map

For an unselected cell put t=-log q, p=g(1-g), and

    w=p(exp(t)-1)>0;  S=sum_unselected w.

For the selected cells put epsilon_i=1/4-p'_i>=0 and B=sum_i epsilon_i. These are actual one-sided physical deviations from fairness. Let theta=(q',z') and theta_0=(q,z), with delta=||theta-theta_0||_infinity.

At every fixed complete cap m, the actual equal-arm forest kernel B(t,p) is analytic on 0<=t<=H, 0<=p<=1/4. Symmetric polynomial dependence on g makes it analytic in p, including p=1/4. The difference B(t,p)-E_t vanishes at p=0 and at t=0; hence it is p t times a bounded analytic matrix function on this compact rectangle. Consequently

    ||B(t,p)-E_t|| <= C_(m,H) p t <= C_(m,H) w.       (1)

This is only a norm comparison: the replacement does not assert INDEPENDENT equality. Its COMMON law and actual duration do agree. Stochastic row-norm telescoping through the original chronological word bounds the total replacement error by C_(m,H) S, regardless of cell count. Setting the L selected coins to fair contributes at most C_m B, uniformly in a fixed strict body neighborhood.

Let F_m(theta) be the complete response difference between the all-fair L-cell body at theta and T. Exact response agreement of W through m therefore gives

    ||F_m(theta)|| <= C_m(S+B).                      (2)

All gap/location parameters remain in theta and in F_m. No diagonal response is substituted for this full-law estimate.

The accepted supplied finite ordered normal form says that, in the strict L-cell all-fair parameter domain, F_m(theta)=0 for EVERY m implies theta=theta_0. Repeated cells do not introduce a permutation freedom. Every finite forest probability is a polynomial with rational coefficients in the survivals: ordinary rates are the integer binomial rates, and the finite compiler uses their finite exponential sums and the fixed fair routing weights.

Hilbert finite generation in this ONE fixed finite parameter ring supplies a finite m_0 whose response equations have exactly that same zero locus. Restrict to a small closed parameter box wholly inside the strict domain. The common zero set there is the single point theta_0. The standard semialgebraic Łojasiewicz inequality gives constants C_0>0 and an integer K>=1 such that

    delta^K <= C_0 ||F_(m_0)(theta)|| <= C_1(S+B).    (3)

This is an isolated-fibre power estimate, not a nonsingular-Jacobian assertion. It handles coincident durations and every higher-order null retuning. No unknown-size polynomial ring is used: the map in (3) belongs only to the selected fixed L-cell body after norm-controlled removal of the extras.

## 3. Every required fair-duration jet lacks a linear n term

Write

    phi_n(q,p)=log R_n(q,p),
    R_n(q,g)=sum_(k=0)^n binom(n,k)g^k(1-g)^(n-k)q^(-k(n-k)).

At fairness and t=-log q, with X_n=Bin(n,1/2)-n/2,

    phi_n(t,1/4)=t n^2/4+log E exp(-t X_n^2).

For t in any compact subinterval of (0,infinity), ALL fixed-order moments of X_n under the tilted weights proportional to Pr(X_n=x)exp(-t x^2) are bounded uniformly in n. To see this, divide the binomial weights by their central maximum. Every resulting weight is at most one, and the normalizing denominator contains a central term at x=0 or x=1/2. Thus each moment is bounded by a constant times the convergent Gaussian lattice sum sum_(x in (1/2)Z) |x|^r exp(-t_min x^2). This covers both parities and all n.

Derivatives of the logarithm in t are cumulants of X_n^2. Therefore the first duration derivative is n^2/4+O(1), and every fixed derivative of order >=2 is O(1), uniformly in n. Conversion to survival derivatives by d/dq=-(1/q)d/dt shows that every fixed q derivative has the form A n^2+O(1).

Let V_K be the finite-dimensional sequence space spanned by

    (partial_q^j phi_n(q_i,1/4))_(n>=2),
        i=1,...,L; j=1,...,K.

Every member of V_K is A n^2+O(1). In particular

    u_n=n(n-1)=n^2-n is NOT in V_K.                 (4)

No linear independence of the displayed jets is required.

## 4. Uniform separation of the full weak-cell cone

Choose Q>1/c, so every actual cell has y=1/q in [1,Q]. Define

    D_n(y)=n(1+y+...+y^(n-2)),  D_n(1)=u_n.

The inherited exact equal-arm polynomial division yields, uniformly on 0<=p<=1/4 and 1<=y<=Q, for every fixed finite coordinate set,

    phi_n(p,y)=w D_n(y)+O_n(w^2),  w=p(y-1).        (5)

This includes rare-coin, finite-duration cells. It is not just the short-duration tangent.

No probability mixture of the sequences D(y), y in [1,Q], belongs to V_K. Indeed, if a probability measure mu has positive mass on (1,Q], then it has some positive mass on [a,Q] for a>1, and its D_n mixture grows at least exponentially in n. Every V_K sequence has quadratic growth. The only remaining measure is the point mass at 1, giving u, excluded by (4).

The set of probability measures on [1,Q] is weakly compact. Choose finitely many coordinates detecting a basis of V_K; their fixed left inverse determines continuously the only possible V_K coefficient vector of any proposed mixture. If every finite coordinate projection allowed equality to V_K, the resulting nested closed sets of probability measures would have a common element, contradicting the preceding paragraph. Hence some finite projection separates the compact convex mixture set from V_K. Finite-dimensional strict separation gives coefficients a_2,...,a_N1 and d>0 with

    a.v=0 for all v in V_K,
    a.D(y)>=d for EVERY y in [1,Q].                 (6)

In particular a.u>=d. This reuses the full compact-positive-mixture argument from the accepted biased local separator; the only change is the enlarged finite jet space V_K. It provides a uniform floor across all allowed rare-coin directions.

## 5. One-sided fairness, arbitrary retuning, and the uniform remainder

The exact fair boundary derivative identity is

    partial_p phi_n(q,1/4)=8 partial_t phi_n(q,1/4)-2u_n,
    partial_t=-q partial_q.                         (7)

It follows directly by differentiating the symmetric binomial weights at fairness. It is also recorded in the accepted biased local proof. Since a kills each target first q derivative, Taylor expansion at the target survivals gives

    a.[phi(q'_i,1/4-epsilon_i)-phi(q'_i,1/4)]
       =2 epsilon_i (a.u)
          +O(epsilon_i delta+epsilon_i^2).          (8)

The sign is POSITIVE because physical epsilon_i>=0. Replacing this cone by a signed p tangent would destroy the argument.

For the all-fair part, a annihilates all q jets through degree K at every target cell. Thus, even when durations coincide,

    a.sum_i [phi(q'_i,1/4)-phi(q_i,1/4)]
       =O(delta^(K+1)).                             (9)

By (3), the right side is O(delta(S+B)). By (5)–(6), the unselected cells satisfy

    a.sum_extra phi >= d S-C sum_extra w_i^2
                     >= d S-C S^2.                 (10)

All constants concern finitely many fixed response coordinates and fixed compact parameter boxes. They are independent of the number and positions of extras.

Because COMMON clocks agree, exact diagonal agreement reads sum_selected phi +sum_extra phi =sum_target phi. Apply a and combine (8)–(10):

    0 >= d S+2d B
             -C[delta(S+B)+B^2+S^2]
      >= d(S+B)-C[delta+(S+B)](S+B).                (11)

The local neighborhood makes delta and B small. Exact pair-diagonal agreement makes S uniformly small too: phi_2(cell)=log(1+2w), and w<=W_H=(exp(H)-1)/4 gives

    sum_extra phi_2 >= 2S/(1+2W_H).

Its left side equals the target pair log diagonal minus the selected sum and tends to zero as the selected parameters tend to their fair targets. Thus shrinking the selected-body neighborhood controls S regardless of extra-cell count, individual duration or bias.

Choose this neighborhood so C[delta+(S+B)]<d/2. Equation (11) is impossible unless S+B=0. Strict extra cells all have w>0, so none exist; B=0 makes every selected coin fair. Exact full response through m_0 and the isolated fibre then give theta=theta_0. Take N=max(m_0,N1,2). This proves the local theorem.

## 6. Composition with the all-fair skeleton: existential finite forcing

Assume the reviewed arbitrary-L all-fair skeleton corollary. If no finite complete cap determined this fixed T among same-clock strict equal-arm private words, choose for each increasing cap a later-inequivalent exact rival. The source compactification and zero bias budget give a subsequence with exactly L fair retained cells, ordered parameters/gaps converging to T, and total extra strength tending to zero. The local theorem uses SAME-COMMON-duration collapsed gaps. In each gap their duration is the effective weak INDEPENDENT duration plus 2 sum_extra p_i t_i. The skeleton theorem gives convergence of the effective gaps and sum_extra w_i ->0; since p_i t_i<=w_i, this difference tends to zero. Thus the actual same-duration collapsed gap parameters used in theta converge to the target gaps as required. For all sufficiently late members, the selected body lies in the local neighborhood above and the matched cap includes N. The local theorem gives equality to T, contradicting later inequivalence.

Consequently EVERY fixed strict finite all-fair private target has SOME finite determining complete cap against arbitrary finite strict equal-arm private rivals on the same COMMON clock. The original-observation transfer uses specifically CALIBRATED-ORIGINAL-TAXON-FOREST-DECODER: ALL ordered-pair COMMON J calibration identities, natural same-bank BOTH, and the actual exclusive private words K_(i|j), K_(j|i) with the derived fixed meeting vertex and positive upper completion law. In that domain the finite complete rows are reconstructed from finite original-taxon topology laws. A generic admitted-context quotient alone does not grant hidden-row access; no broader all-core reduction is asserted here. This is a proposed positive branch for arbitrary serial fair-cell counts, not general G4: biased targets, uncalibrated COMMON laws and other source/menu classes are not covered.

For L=0, no compactness argument is needed: a nonempty strict equal-arm word on COMMON duration H has INDEPENDENT pair survival exp(-H) times product_i[1+2p_i(exp(t_i)-1)], strictly greater than exp(-H). Thus the pair row determines the ordinary target within this same-clock class.

This compactness contradiction is an EXISTENTIAL finite-cap result. It does not by itself provide a target-effective global cap, a recognizable stopping certificate, or a solver that halts on the full unknown-size problem. The fixed finite-body map and local separator may be searched effectively for algebraic target parameters, but detecting that all possible unknown-size rivals have entered this local neighborhood requires its own argument. No numerical cap has been computed here.

## 7. Source and attribution boundary

The source compiler, supplied ordered normal form, same-clock weak-cell bounds, exact fair derivative identity, compact weak-cone separator and countable compactification are inherited. The proposed addition is the use of a finite-body isolated-fibre power bound followed by annihilation of sufficiently many fair jets, retaining the one-sided bias sign. No historical novelty claim is made.

- Supplied finite normal form and its fixed-ring finite-prefix principle: https://github.com/Sodelin/Research-Commons/blob/b005368d41c258e7ea05e3bdfa36631c7ee2c544/research/2026-10-01-sol61-g4-allcopy-2237z/PASSIVE-CHAIN-NORMAL-FORM.md ; Git blob 5d48d299ec72d3a297fe85e33e2686d106769977. Accepted review blob 8e1ae00cbbf7afef74cf67485f9fef5d9d5f6242.
- Reviewed local separator and fair derivative identity: https://github.com/Sodelin/Research-Commons/blob/a3453370e8e2f79dfee488d75ee90066c6285591/research/2026-10-09-dot-local-forcing-and-coverage-review-1627z/g4-local/LOCAL-WEAK-INSERTION-EXCLUSION.md ; proof SHA256 4b8e43ecb28f15e7c6267811405d8d4041022068b8c354e99067ac364677f9a0.
- Same packet's FINITE-PERSISTENT-ARRAY-CLASSIFICATION.md supplies the actual full-forest weak-cell analytic and stochastic-telescoping interface; its same-duration variant (1) is derived explicitly above.
- Countable compactification: https://github.com/Sodelin/Research-Commons/blob/4b57fe0b35d1ee98163785eef8120adf015369ad/research/2026-10-10-dot-g4-countable-clock-compactification-1105z/README.md .
- Reviewed all-fair skeleton: https://github.com/Sodelin/Research-Commons/blob/42d22198094c98154ece7a3ac038462b3b4a21f5/research/2026-10-10-dot-g4-all-fair-finite-skeleton-1216z/ALL-FAIR-FINITE-SKELETON-COROLLARY.md ; proof SHA256 8fa46511333eb1b5a258d8b6cab2b35ecdcf28d4e6489f23e59ab77b8f9f2b09; independent review SHA256 08f8138db108a745a2aa6a811601f70329833648e0d317a4ec145de71811c4b3.
- Original observer adapter: https://github.com/Sodelin/Research-Commons/blob/4e9f1ef2fcef4d1215025086f86f3df9c021d392/research/2026-10-09-dot-calibrated-tree-edge-reduction-1531z/CALIBRATED-ORIGINAL-TAXON-FOREST-DECODER.md ; Git blob 40cc961e52cf6a670c02e7b94224a60df0aa3d57, SHA256 06c5b954d6976456db7ae3502cacd791957a4bcc04f27833a5dfa8e847124447. Its all-J and natural same-bank BOTH conditions are mandatory.
- Actual original source compiler: https://github.com/Sodelin/Research-Commons/blob/5e01a8e727478a2f22686d31f71304126e345116/research/2026-10-01-g4-admitted-testers-0819z/PROOF.md ; Git blob b41fdf706e4dfcb5d14ffdbc88631012674ef1f4, SHA256 661696b322c1ee2f57ffeb45ada556808f945d698ef0187c1a32ec0d881e40a1.
- Classical mathematical ingredient: the compact semialgebraic Łojasiewicz inequality, applied only to the finite polynomial map F_(m_0) and distance to its isolated zero. A primary-source formulation is Basu and Mohammad-Nezhad, Improved effective Łojasiewicz inequality and applications, Forum of Mathematics, Sigma 12 (2024), e115, Theorem 1.1: https://www.cambridge.org/core/journals/forum-of-mathematics-sigma/article/improved-effective-lojasiewicz-inequality-and-applications/022BF859F5714FDA8050F6DC1992E48B . No new effective bound from that paper is claimed.

Independent review is requested particularly for the polynomial finite-body isolation, same-clock full-kernel estimate, all-order fair-jet growth, compact mixture separation, and the use of one power exponent to make every nonlinear remainder o(S+B).
